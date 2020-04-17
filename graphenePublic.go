package eth

import (
	"encoding/binary"
	"errors"
	"math"
	"math/big"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/bissias/go-IBLT-sz"
	"github.com/willf/bloom"
)

var (
	grapheneDefaultOverhead = 1.35
	grapheneBeta            = 0.9998
	grapheneC               = 8 * grapheneDefaultOverhead * math.Pow(math.Log(2), 2)
	grapheneTau             = 37.5
	IBLT_CELL_MINIMUM			  = 2
	APPROX_ITEMS_THRESH 	  = 600
	APPROX_EXCESS_RATE      = 4
	IBLT_DEFAULT_OVERHEAD   = 1.5
	FILTER_CELL_SIZE        = 1
	IBLT_FIXED_CELL_SIZE    = 13.0
	APPROX_ITEMS_THRESH_REDUCE_CHECK = 500
	FILTER_FPR_MAX          = 0.999
	LARGE_MEM_POOL_SIZE     = 10000000
	MAX_CHECKSUM_BITS       = 32;
	MaxFloat64              = 1.797693134862315708145274237317043567981e+308
	LN2SQUARED              = 0.4804530139182014246671025263266649717305529515945455
	version                 = 4
)

/*
GrapheneManager single manager for all our block conversations
*/
type GrapheneManager struct {
	BlockManager map[string]*GrapheneBlockManager
}

type GrapheneBlockManager struct {
	Z       map[string]*types.Transaction
	TxIds   []string
	Indices []byte
	Hash    common.Hash
	Number  *big.Int
	Header  *types.Header
	Uncles  []*types.Header
	Txs     []*types.Transaction
}

func RequestUnknownBlocksGraphene(p *peer, pm *ProtocolManager, block struct {
	Hash   common.Hash
	Number uint64
}) {

	//Retrieve the pending transactions
	pending, _ := pm.txpool.Pending()


	//gather the list of the number of transactions that are in pending
	nTxs := 0
	for _, txs := range pending {
		nTxs += len(txs)

	}

	//Send the the block.hash and number of transactions over for step 1 of protocol 1
	blockManager := new(GrapheneBlockManager)
	blockManager.Hash = block.Hash
	blockManager.Z = make(map[string]*types.Transaction)
	hashString := getTxID(block.Hash)
	if pm.gm.BlockManager == nil {
		pm.gm.BlockManager = make(map[string]*GrapheneBlockManager)
	}
	pm.gm.BlockManager[hashString] = blockManager

	p.RequestGraphene(block.Hash, nTxs)
}

func GetGrapheneMsgCall(p *peer, pm *ProtocolManager, msg p2p.Msg) {

	// pulls needed information from query and from the local environment
	var query getGrapheneData
	msg.Decode(&query)
	block := pm.blockchain.GetBlockByHash(query.Hash)
	nPendingAtRecv := query.NTxs
	txs := block.Transactions()
	nTxsInBlock := uint(len(txs))
	pending, _ := pm.txpool.Pending()
	nPendingAtSend := len(pending)
	if nTxsInBlock == 0 {
		log.Info("GRAPHENE DEBUG GetGraphene for empty block Protocol 1", "hash", query.Hash)
		return
	}

	nReceiverUniverseItems := nPendingAtRecv;
	nSenderUniverseItems := nPendingAtSend;
	nItems := nTxsInBlock;
	nReceiverExcessItems := math.Max(float64(nReceiverUniverseItems - nItems), float64(uint(nSenderUniverseItems) - nItems));
	nReceiverExcessItems = math.Max(0.0, float64(nReceiverExcessItems)); // must be non-negative
	nReceiverExcessItems = math.Min(float64(nReceiverUniverseItems), float64(nReceiverExcessItems)); // must not exceed total mempool size
	nReceiverMissingItems := math.Max(1.0, float64(float64(nItems) - (float64(nReceiverUniverseItems) - nReceiverExcessItems)));

	// Optimal symmetric differences between receiver and sender IBLTs
	// This is the parameter "a" from the graphene paper
	optSymDiff := float64(nReceiverMissingItems);
	ibltExtraPadding := uint64(0)
		log.Info("GRAPHENE DEBUG GetGraphene OptimalSymDiff before 1a Protocol 1", "hash", query.Hash)
		optSymDiff = OptimalSymDiff(uint64(nItems), uint64(nReceiverUniverseItems), uint64(nReceiverExcessItems), uint64(nReceiverMissingItems));
		ibltExtraPadding = uint64(nReceiverMissingItems)
	}

	// Set false positive rate for Bloom filter based on optSymDiff
	bloomFPR := float64(BloomFalsePositiveRate(optSymDiff, uint64(nReceiverExcessItems)));


	// Account for variance in bloom filter (a* in the paper)
	gr_s := - math.Log(1 - grapheneBeta) / float64(optSymDiff)
	dlta := 0.5 * (gr_s + math.Sqrt(math.Pow(gr_s, 2) + 8 * gr_s))
	optSymDiff = float64((1.0 + dlta) * float64(optSymDiff))


	// So far we have only made room for false positives in the IBLT
	// Make more room for missing items
	optSymDiff += float64(ibltExtraPadding);

	bloomFilter := bloom.NewWithEstimates(nTxsInBlock, bloomFPR)
	optSymDiffInt := int(optSymDiff)


	senderIBLT := iblt.New(uint(optSymDiffInt))
	txIds := []string{}
	txHashes := [][]byte{}

	txPositions := make(map[string]uint32)
	blk_size := block.Size()
	blk_sizeS, err := ToBytes(blk_size.String())

	m_number_of_Bits, k_hashing_numbers := bloom.EstimateParameters(nTxsInBlock, bloomFPR)
	float_k := float64(k_hashing_numbers)
	float_txs := float64(len(txs))
	float_m := float64(m_number_of_Bits)
	probability := math.Pow(1-math.Exp(-(float_k*float_txs)/float_m), float_k)

	//generate bloom filter S and iblt I from the transaction ids of the block
	for i, tx := range txs {
		txHash := tx.Hash().Bytes()[:6]
		txHashString := string(txHash[:])

		bloomFilter.Add(txHash)
		senderIBLT.Insert(txHash)
		txIds = append(txIds, txHashString)
		txHashes = append(txHashes, txHash)
		txPositions[txHashString] = uint32(i)
	}

	indexArray := []byte{}

	sort.Strings(txIds)

	//gets a lits of the indexs to send
	for _, txId := range txIds {
		bs := make([]byte, 4)
		binary.LittleEndian.PutUint32(bs, txPositions[txId])
		indexArray = append(indexArray, bs...)
	}

	//generaates binaries
	ibltBinary, _ := senderIBLT.Serialize()
	bloomFilterBinary, _ := bloomFilter.GobEncode()

	p.SendGraphene(query.Hash, ibltBinary, bloomFilterBinary, uint(nPendingAtRecv), uint(nTxsInBlock), indexArray, block.Header().Number, block.Header(), block.Uncles(), uint(nPendingAtSend))
}

type writeCounter common.StorageSize

func (c *writeCounter) Write(b []byte) (int, error) {
	*c += writeCounter(len(b))
	return len(b), nil
}

func RecieveGraphene(p *peer, pm *ProtocolManager, msg p2p.Msg) {
	//gathers needed data from mesage and generates iblt and bloom filter
	var body grapheneData
	msg.Decode(&body)
	hashString := getTxID(body.Hash)
	bm, ok := pm.gm.BlockManager[hashString]
	if ok {
		bm.Number = body.Number
		bm.Header = body.Header
		bm.Uncles = body.Uncles
	} else {
		return //no futher action needed for removed/handled block
	}

	nPendingAtRecv := body.NTxs


	c := writeCounter(0)
	rlp.Encode(&c, &body)
	graphene_blk_sizeToBytes := common.StorageSize(c)
	graphene_blk_size, err := ToBytes(graphene_blk_sizeToBytes.String()) // "1K"

	nReceiverUniverseItems := nPendingAtRecv;
	nSenderUniverseItems := body.NPendingAtSend;
	nItems := body.NTxs;
	nReceiverExcessItems := math.Max(float64(nReceiverUniverseItems - nItems), float64(uint(nSenderUniverseItems) - nItems));
	nReceiverExcessItems = math.Max(0.0, float64(nReceiverExcessItems)); // must be non-negative
	nReceiverExcessItems = math.Min(float64(nReceiverUniverseItems), float64(nReceiverExcessItems)); // must not exceed total mempool size
	nReceiverMissingItems := math.Max(1.0, float64(float64(nItems) - (float64(nReceiverUniverseItems) - nReceiverExcessItems)));

	// Optimal symmetric differences between receiver and sender IBLTs
	// This is the parameter "a" from the graphene paper
	optSymDiff := float64(nReceiverMissingItems);
	ibltExtraPadding := uint64(0)
	if nItems <= uint(math.Ceil(float64(nReceiverUniverseItems) + nReceiverMissingItems)) {
		optSymDiff = OptimalSymDiff(uint64(nItems), uint64(nReceiverUniverseItems), uint64(nReceiverExcessItems), uint64(nReceiverMissingItems));
		ibltExtraPadding = uint64(nReceiverMissingItems)
	}
	bloomFPR := float64(BloomFalsePositiveRate(optSymDiff, uint64(nReceiverExcessItems)));

	// Account for variance in bloom filter (a* in the paper)
	gr_s := - math.Log(1 - grapheneBeta) / float64(optSymDiff)
	dlta := 0.5 * (gr_s + math.Sqrt(math.Pow(gr_s, 2) + 8 * gr_s))
	optSymDiff = float64((1.0 + dlta) * float64(optSymDiff))

	// So far we have only made room for false positives in the IBLT
	// Make more room for missing items
	optSymDiff += float64(ibltExtraPadding);

	bloomFilter := bloom.NewWithEstimates(body.NTxs, bloomFPR)
	bloomFilter.GobDecode(body.BloomFilter)
	m_number_of_Bits, k_hashing_numbers := bloom.EstimateParameters(body.NTxs, bloomFPR)



	receivedIBLT, _ := iblt.Deserialize(body.IBLT)
	localIBLT := iblt.NewTable(receivedIBLT.BktNum, receivedIBLT.DataLen, receivedIBLT.HashLen, receivedIBLT.HashNum)

	nTested := 0
	pending, _ := pm.txpool.Pending()
	shortTxHashMap := make(map[string]*types.Transaction)

	m := len(pending)
	num_inserted := 0
	num_inserted2 := 0
	txIds := []string{}
	txHashes := [][]byte{}


	for _, txs := range pending {
		for _, tx := range txs {
			nTested += 1
			txHash := tx.Hash().Bytes()[:6]
			txHashString := string(txHash[:])
			num_inserted += 1
			if bloomFilter.Test(txHash) {
				num_inserted2 += 1
				localIBLT.Insert(txHash)
				shortTxHashMap[txHashString] = tx
				txIds = append(txIds, txHashString)
				txHashes = append(txHashes, txHash)
			}
		}
	}

	float_k := float64(k_hashing_numbers)
	float_m := float64(m_number_of_Bits)

	float_num_inserted := float64(num_inserted)
	float_num_inserted2 := float64(num_inserted2)

	probability1 := math.Pow(1-math.Exp(-(float_k*(float_num_inserted))/float_m), float_k)
	probability2 := math.Pow(1-math.Exp(-(float_k*(float_num_inserted2))/float_m), float_k)

	sort.Strings(txIds)
	z := len(shortTxHashMap)



	receivedIBLT.Subtract(localIBLT)
	decodedIBLT, err := receivedIBLT.Decode()

	//metrix gathering
	graphene_bloom_size_c := writeCounter(0)
	rlp.Encode(&graphene_bloom_size_c, *&body.BloomFilter)
	graphene_bloom_sizeToByte := common.StorageSize(graphene_bloom_size_c)
	graphene_bloom_size, _ := ToBytes(graphene_bloom_sizeToByte.String()) // "1K"

	graphene_iblt_size_c := writeCounter(0)
	rlp.Encode(&graphene_iblt_size_c, *&body.IBLT)
	graphene_iblt_sizeToByte := common.StorageSize(graphene_iblt_size_c)
	graphene_iblt_size, _ := ToBytes(graphene_iblt_sizeToByte.String()) // "1K"


		graphene_localiblt_size_c := writeCounter(0)
		rlp.Encode(&graphene_localiblt_size_c, *&localIBLT)
		graphene_localiblt_sizeToByte := common.StorageSize(graphene_localiblt_size_c)
		graphene_localiblt_size, _ := ToBytes(graphene_localiblt_sizeToByte.String()) // "1K"

	graphene_rank_size_c := writeCounter(0)
	rlp.Encode(&graphene_rank_size_c, *&body.Indices)
	graphene_rank_sizeToByte := common.StorageSize(graphene_rank_size_c)
	graphene_rank_size, _ := ToBytes(graphene_rank_sizeToByte.String()) // "1K"

	//protocol 2
	if err != nil {
		//FIXME confirm diff and bloom setup along with x*
		//gather values for altx and y, and create bloom filter
		alternateX := CreateX(z, m, int(nItems), bloomFPR, grapheneBeta)
		alternateY := CreateY(alternateX, z, m, bloomFPR, grapheneBeta)

		b := ApproxOptimalSymDiff(uint64(z))

		if float64(body.NTxs) == alternateX {
			bloomFPR = 0.999
		} else {
			bloomFPR = b / float64(float64(body.NTxs)-alternateX)
		}
		bloomFilter := bloom.NewWithEstimates(uint(len(shortTxHashMap)), bloomFPR)

		txIds := []string{}
		//get id list and sort
		for k := range shortTxHashMap {

			txIds = append(txIds, k)
		}
		sort.Strings(txIds)

		//add to filter


		for _, txId := range txIds {
			txHash := shortTxHashMap[txId].Hash().Bytes()[:6]
			bloomFilter.Add(txHash)
		}

		//send filter and idff
		bloomFilterBinary, _ := bloomFilter.GobEncode()
		bm.Indices = body.Indices
		bm.Z = shortTxHashMap


		p.RequestGrapheneExtension(body.Hash, bloomFilterBinary, Float64Bytes(b), Float64Bytes(alternateY), Float64Bytes(bloomFPR)) //CHECK This was changed
	} else {
		//remove ones with neg counts and add positive, but shouldnt this be Removed or do we need to edit the library? This was based on sunny

		for _, txHash := range decodedIBLT.Beta.Set {
			txHashString := string(txHash[:])

			delete(shortTxHashMap, txHashString)
		}

		bm.Z = shortTxHashMap
		bm.Indices = body.Indices


		p.RequestGrapheneTransactionsProtocol1Peer(body.Hash, decodedIBLT.Alpha.Set)

	}

}

func RequestGrapheneTransactionsProtocol1Function(p *peer, pm *ProtocolManager, msg p2p.Msg) {

	var query requestGrapheneTransactionsProtocol1
	msg.Decode(&query)
	block := pm.blockchain.GetBlockByHash(query.Hash)
	txIdsRecieved := query.Added
	txs := block.Transactions()

	txsReturn := []*types.Transaction{}
	//gathers and sends transactions

	for _, txId := range txIdsRecieved {
		for _, tx := range txs {
			txHash := tx.Hash().Bytes()[:6]
			txHashString := string(txHash[:])
			txIdString := string(txId)
			if txHashString == txIdString {
				txsReturn = append(txsReturn, tx)
			}
		}
	}


	p.RecieveGrapheneTransactionsProtocol1Peer(query.Hash, txsReturn, block.Number())

}

func RecieveGrapheneTransactionsProtocol1Function(p *peer, pm *ProtocolManager, msg p2p.Msg) {

	var body recieveGrapheneTransactionsProtocol1
	msg.Decode(&body)

	hashString := getTxID(body.Hash)
	bm, ok := pm.gm.BlockManager[hashString]
	if !ok {
		return //no futher action needed for removed/handled block
	}

	txsAdded := body.Transactions
	shortTxHashMap := bm.Z


	for _, tx := range txsAdded {
		txHash := tx.Hash().Bytes()[:6]
		txHashString := string(txHash[:])
		shortTxHashMap[txHashString] = tx
	}

	//pull out ids and sort
	txIds := []string{}
	for k := range shortTxHashMap {
		txIds = append(txIds, k)
	}
	sort.Strings(txIds)


	txs := make([]*types.Transaction, len(txIds))
	//arrange by index
	for i, txId := range txIds {
		index := binary.LittleEndian.Uint32(bm.Indices[4*i : 4*i+4])
		txs[index] = shortTxHashMap[txId]
	}
	// TXS should be all transactions in block
	//need to create block and add to reciever blockchain


	graphene_rereqtx_size_c := writeCounter(0)
	rlp.Encode(&graphene_rereqtx_size_c, *&body)
	unconverted_graphene_rereqtx_size := common.StorageSize(graphene_rereqtx_size_c)
	graphene_rereqtx_sizeToBytes := common.StorageSize(graphene_rereqtx_size_c)
	graphene_rereqtx_size, _ := ToBytes(graphene_rereqtx_sizeToBytes.String()) // "1K"



	block := types.NewBlockWithHeader(bm.Header).WithBody(txs, bm.Uncles)
	delete(pm.gm.BlockManager, hashString) //prevent futher responses unless block requested again

	if _, err := pm.blockchain.InsertChain(types.Blocks{block}); err != nil {
		log.Info("GRAPHENE METRIC Propagated Graphene Protocol 1 block import failed Protocol 1", "number", block.Number(), "hash", body.Hash, "err", err)
		return
	}



	//successfully inserted block
	log.Info("GRAPHENE METRIC Propagated Graphene Protocol 1 block import suceeded Protocol 1", "number", block.Number(), "hash", body.Hash)

}

func GetGrapheneMsgExtended(p *peer, pm *ProtocolManager, msg p2p.Msg) {
	//decode and get inno
	var query getGrapheneDataExtendedRequest

	msg.Decode(&query)
	bloomFPR := Float64FromBytes(query.BloomFPR)
	alternateY := Float64FromBytes(query.AlternateY)
	b := Float64FromBytes(query.Beta)  // beta is actually b from the graphene paper


	block := pm.blockchain.GetBlockByHash(query.Hash)

	txs := block.Transactions()

	bloomFilter := bloom.NewWithEstimates(uint(len(txs)), bloomFPR)
	bloomFilter.GobDecode(query.BloomFilter)
	txsToReturn := []*types.Transaction{}

	//test transactions from block against bloom filter to get transactions to return
	for _, tx := range txs {
		txHash := tx.Hash().Bytes()[:6]
		if !bloomFilter.Test(txHash) {
			txsToReturn = append(txsToReturn, tx)
		}
	}

	//create iblt
	expectedDiff := b + alternateY
	if expectedDiff < 2 {
		expectedDiff = 2
	}

	JIBLT := iblt.New(uint(expectedDiff))


	//add to iblt
	for _, tx := range txs {
		txHash := tx.Hash().Bytes()[:6]
		JIBLT.Insert(txHash)
	}
	ibltBinary, err := JIBLT.Serialize()
	//send info

	if (err != nil) {
		log.Info("GRAPHENE METRIC", "blk_hash", query.Hash, "iblt2_ser_error", err)
	}

	graphene_bloom2_size_c := writeCounter(0)
	rlp.Encode(&graphene_bloom2_size_c, *&query.BloomFilter)
	graphene_bloom2_sizeToByte := common.StorageSize(graphene_bloom2_size_c)
	graphene_bloom2_size, _ := ToBytes(graphene_bloom2_sizeToByte.String()) // "1K"


	graphene_iblt_size2_c := writeCounter(0)
	rlp.Encode(&graphene_iblt_size2_c, *&JIBLT)
	graphene_iblt_size2ToByte := common.StorageSize(graphene_iblt_size2_c)
	graphene_iblt_size2, _ := ToBytes(graphene_iblt_size2ToByte.String()) // "1K"


	p.SendGrapheneExtension(query.Hash, ibltBinary, txsToReturn, Float64Bytes(b), query.AlternateY)
}

func RecieveGrapheneExtended(p *peer, pm *ProtocolManager, msg p2p.Msg) {

	//get information
	var body getGrapheneDataExtended
	msg.Decode(&body)

	hashString := getTxID(body.Hash)
	bm, ok := pm.gm.BlockManager[hashString]
	if !ok {
		return //no futher action needed for removed/handled block
	}

	//create iblt
	receivedJIBLT, _ := iblt.Deserialize(body.IBLT)
	localIBLT := iblt.NewTable(receivedJIBLT.BktNum, receivedJIBLT.DataLen, receivedJIBLT.HashLen, receivedJIBLT.HashNum)



	shortTxHashMap := make(map[string]*types.Transaction)
	if len(bm.Z) > 0 {
		shortTxHashMap = bm.Z
	}

	// Augment Z with missing transactions
	for _, tx := range body.Transactions {
		txHash := tx.Hash().Bytes()[:6]
		txHashString := string(txHash[:])
  		shortTxHashMap[txHashString] = tx
	}

	// Add transactions from Z to localIBLT
	for _, tx := range shortTxHashMap {
		txHash := tx.Hash().Bytes()[:6]
		localIBLT.Insert(txHash)
	}

	//subtract the iblt

	receivedJIBLT.Subtract(localIBLT)
	decodedIBLT, err := receivedJIBLT.Decode()
	if err != nil {
		delete(pm.gm.BlockManager, hashString) //prevent futher responses unless block requested again
		pm.fetcher.Notify(p.id, bm.Hash, bm.Number.Uint64(), time.Now(), p.RequestOneHeader, p.RequestBodies)
		return
	}


	for _, txHash := range decodedIBLT.Beta.Set {
		txHashString := string(txHash[:])
		delete(shortTxHashMap, txHashString)
	}
	bm.Txs = body.Transactions
	if len(decodedIBLT.Alpha.Set) >= 0 {
		p.RequestGrapheneTransactionsProtocol2Peer(body.Hash, decodedIBLT.Alpha.Set)
	} else {

		for _, tx := range bm.Txs {
			txHash := tx.Hash().Bytes()[:6]
			txHashString := string(txHash[:])
			shortTxHashMap[txHashString] = tx
		}
		txIds := []string{}
		for k, _ := range shortTxHashMap {
			txIds = append(txIds, k)
		}
		sort.Strings(txIds)

		txs := make([]*types.Transaction, len(txIds))

		for i, txId := range txIds {
			index := binary.LittleEndian.Uint32(bm.Indices[4*i : 4*i+4])
			txs[index] = shortTxHashMap[txId]
		}

		graphene_iblt2_size_c := writeCounter(0)
		rlp.Encode(&graphene_iblt2_size_c, *&body.IBLT)
		graphene_iblt2_sizeToBytes := common.StorageSize(graphene_iblt2_size_c)
		graphene_iblt2_size, _ := ToBytes(graphene_iblt2_sizeToBytes.String()) // "1K"

		graphene_localiblt2_size_c := writeCounter(0)
		rlp.Encode(&graphene_localiblt2_size_c, *&localIBLT)
		graphene_localiblt2_sizeToBytes := common.StorageSize(graphene_localiblt2_size_c)
		graphene_localiblt2_size, _ := ToBytes(graphene_localiblt2_sizeToBytes.String()) // "1K

		graphene_addtx2_size_c := writeCounter(0)
		rlp.Encode(&graphene_addtx2_size_c, *&body.Transactions)
		graphene_addtx2_sizeToBytes := common.StorageSize(graphene_addtx2_size_c)
		graphene_addtx2_size, _ := ToBytes(graphene_addtx2_sizeToBytes.String()) // "1K"


		block := types.NewBlockWithHeader(bm.Header).WithBody(txs, bm.Uncles)
		delete(pm.gm.BlockManager, hashString) //prevent futher responses unless block requested again

		if _, err := pm.blockchain.InsertChain(types.Blocks{block}); err != nil {
			log.Info("GRAPHENE METRIC Propagated Graphene RecieveGrapheneExtended block import failed", "number", block.Number(), "hash", body.Hash, "err", err)
			return
		}

		log.Info("GRAPHENE METRIC Propagated Graphene Protocol 1 block import suceeded Protocol 2", "number", block.Number(), "hash", body.Hash, "err", err)

	}
}

func RequestGrapheneTransactionsProtocol2Function(p *peer, pm *ProtocolManager, msg p2p.Msg) {

	//gathers needed data from mesage and generates iblt and bloom filter
	var query requestGrapheneTransactionsProtocol2
	msg.Decode(&query)
	block := pm.blockchain.GetBlockByHash(query.Hash)
	txIdsRecieved := query.Added
	txs := block.Transactions()
	txsReturn := []*types.Transaction{}
	//gathers and sends transactions

	for _, txId := range txIdsRecieved {
		for _, tx := range txs {
			txHash := tx.Hash().Bytes()[:6]
			txHashString := string(txHash[:])
			txIdString := string(txId)
			if txHashString == txIdString {
				txsReturn = append(txsReturn, tx)
			}
		}
	}

	graphene_rereqtx2_size_c := writeCounter(0)
	rlp.Encode(&graphene_rereqtx2_size_c, *&txsReturn)
	graphene_rereqtx2_sizeToBytes := common.StorageSize(graphene_rereqtx2_size_c)
	graphene_rereqtx2_size, _ := ToBytes(graphene_rereqtx2_sizeToBytes.String()) // "1K"

	// graphene_rereqtx2_size := unsafe.Sizeof(txsReturn)


	errorSend := p.RecieveGrapheneTransactionsProtocol2Peer(query.Hash, txsReturn)
	log.Info("GRAPHENE METRIC RequestGrapheneTransactionsProtocol2Function", "sent", query.Hash, "errorSend", errorSend)

}

func RecieveGrapheneTransactionsProtocol2Function(p *peer, pm *ProtocolManager, msg p2p.Msg) {
	//gathers needed data from mesage and generates iblt and bloom filter
	var body recieveGrapheneTransactionsProtocol2
	msg.Decode(&body)
	txsAdded := body.Transactions

	hashString := getTxID(body.Hash)
	bm, ok := pm.gm.BlockManager[hashString]
	if !ok {
		return //no futher action needed for removed/handled block
	}
	shortTxHashMap := bm.Z

	for _, tx := range txsAdded {
		txHash := tx.Hash().Bytes()[:6]
		txHashString := string(txHash[:])
		shortTxHashMap[txHashString] = tx
	}
	for _, tx := range bm.Txs {
		txHash := tx.Hash().Bytes()[:6]
		txHashString := string(txHash[:])
		shortTxHashMap[txHashString] = tx
	}

	txIds := []string{}
	//pull out ids and sort
	for k := range shortTxHashMap {
		txIds = append(txIds, k)
	}
	sort.Strings(txIds)

	//TODO Bitarray
	txs := make([]*types.Transaction, len(txIds))
	//arrange by index
	for i, txId := range txIds {
		index := binary.LittleEndian.Uint32(bm.Indices[4*i : 4*i+4])
		txs[index] = shortTxHashMap[txId]
	}
	nSizeGrapheneBlockTx2_c := writeCounter(0)
	rlp.Encode(&nSizeGrapheneBlockTx2_c, *&txsAdded)
	nSizeGrapheneBlockTx2ToBytes := common.StorageSize(nSizeGrapheneBlockTx2_c)
	nSizeGrapheneBlockTx2, _ := ToBytes(nSizeGrapheneBlockTx2ToBytes.String()) // "1K"

	graphene_rereqtx2_size_c := writeCounter(0)
	rlp.Encode(&graphene_rereqtx2_size_c, *&body)
	graphene_rereqtx2_sizeToBytes := common.StorageSize(graphene_rereqtx2_size_c)
	graphene_rereqtx2_size, _ := ToBytes(graphene_rereqtx2_sizeToBytes.String()) // "1K"

	block := types.NewBlockWithHeader(bm.Header).WithBody(txs, bm.Uncles)
	delete(pm.gm.BlockManager, hashString) //prevent futher responses unless block requested again

	if _, err := pm.blockchain.InsertChain(types.Blocks{block}); err != nil {
		log.Info("GRAPHENE METRIC Propagated Graphene RecieveGrapheneTransactionsProtocol2Function block import failed", "number", block.Number(), "hash", body.Hash, "err", err)
		return
	}

	log.Info("GRAPHENE METRIC Propagated Graphene Protocol 1 block import suceeded", "number", block.Number(), "hash", body.Hash)

}


func CreateX(z int, m int, n int, f_S float64, beta float64) float64 {
	if z == 0 {
		return 0.0
	}

	xStar := 0
	p := probXEqK(z, xStar, m, f_S)
	for p <= 1-beta && xStar <= int(math.Min(float64(z), float64(n))) {
		xStar += 1
		p += probXEqK(z, xStar, m, f_S)
	}

	return float64(math.Max(0.0, float64(xStar-1)))
}

func CreateY(x_star float64, z int, m int, f_S float64, beta float64) float64 {
	if z == 0 {
		return 0.0
	}

	return float64(math.Min(float64(z), (1.0+delta(x_star, m, f_S, beta))*float64(float64(m)-x_star)*f_S))
}

func CreateDeltaI(z int, i int, m int, f_S float64) float64 {
	return float64(z-i)/(float64(m-i)*f_S) - 1
}

func probXEqK(z int, i int, m int, f_S float64) float64 {
	di := CreateDeltaI(z, i, m, f_S)
	di_plus_1 := di + 1

	return math.Pow(math.Exp(di) / math.Pow(di_plus_1, di_plus_1), float64(m-i) * f_S)
}

func delta(x_star float64, m int, f_S float64, beta float64) float64 {
	log_b := math.Log(1 - beta) // natural log
	s := -log_b / (float64(float64(m)-x_star) * f_S)

	return 0.5 * (s + math.Sqrt(math.Pow(s, 2) + 8*s))
}

func Float64FromBytes(bytes []byte) float64 {
	bits := binary.LittleEndian.Uint64(bytes)
	float := math.Float64frombits(bits)

	return float
}

func Float64Bytes(float float64) []byte {
	bits := math.Float64bits(float)
	bytes := make([]byte, 8)

	binary.LittleEndian.PutUint64(bytes, bits)

	return bytes
}


func OptimalSymDiff(nBlockTxs uint64,
    nReceiverPoolTx uint64,
    nReceiverExcessTxs uint64,
    nReceiverMissingTxs uint64) float64 {

    approx_items_thresh := APPROX_ITEMS_THRESH;

		if version >= 4 {
			approx_items_thresh= APPROX_ITEMS_THRESH_REDUCE_CHECK
		}

    optSymDiff := 0.0;
    if nBlockTxs >= uint64(approx_items_thresh) && nReceiverExcessTxs >= nBlockTxs / uint64(APPROX_EXCESS_RATE) {

       optSymDiff = ApproxOptimalSymDiff(nBlockTxs);
		 } else {
			optSymDiff = BruteForceSymDiff(nBlockTxs, nReceiverPoolTx, nReceiverExcessTxs, nReceiverMissingTxs, uint64(MAX_CHECKSUM_BITS));

		}

    return optSymDiff
}


func ApproxOptimalSymDiff(nBlockTxs uint64) float64 {
    nChecksumBits := uint32(32);
    return math.Max(1.0, math.Round(float64(FILTER_CELL_SIZE) * float64(nBlockTxs) /
                                    (float64(nChecksumBits + 8 * uint32(IBLT_FIXED_CELL_SIZE)) * IBLT_DEFAULT_OVERHEAD * LN2SQUARED)));
}

/* Brute force search for optimal symmetric difference between block txs and receiver
 * mempool txs passing though filter to use for IBLT.
 *
 * Let a be defined as the size of the symmetric difference between items in the
 * sender and receiver IBLTs.
 *
 * The total size in bytes of a graphene block is given by T(a) = F(a) + L(a) as defined
 * in the code below. (Note that meta parameters for the Bloom Filter and IBLT are ignored).
 */

func BruteForceSymDiff(nBlockTxs uint64,
    nReceiverPoolTx uint64,
    nReceiverExcessTxs uint64,
    nReceiverMissingTxs uint64,
    nChecksumBits uint64) float64 {
    //assert(nReceiverExcessTxs <= nReceiverPoolTx); // Excess contained in mempool
    //assert(nReceiverMissingTxs <= nBlockTxs); // Can't be missing more txs than are in block
		if nReceiverExcessTxs > nReceiverPoolTx || nReceiverMissingTxs > nBlockTxs {
			return .999;
		}
  	if int(nReceiverPoolTx) > LARGE_MEM_POOL_SIZE {
			return .999; 	//runtime_error("Receiver mempool is too large for optimization");
		}


    optSymDiff := 1;
    optT := MaxFloat64;

    for a := 1; a < int(nReceiverPoolTx) ; a++ {
				F :=  math.Floor(float64(FILTER_CELL_SIZE) * (-1.0 / LN2SQUARED * float64(nBlockTxs) * math.Log(float64(fpr(nReceiverExcessTxs, uint64(a)))) / 8.0));
        T := F + L(a);

        if T < optT {
            optSymDiff = a;
            optT = T;
        }
    }

    return float64(optSymDiff);
}


func fpr(nReceiverExcessTxs uint64, a uint64) uint64 {

	if nReceiverExcessTxs == 0 {
		return uint64(FILTER_FPR_MAX);
	}

	_fpr := float64(a) / float64(nReceiverExcessTxs);
	if _fpr < FILTER_FPR_MAX {
		return uint64(_fpr)
	} else {
		return uint64(FILTER_FPR_MAX)
	}
}


func L(a int) float64 {
			nChecksumBits := 32.0;

			ibltParam := iblt.GetIbltParams(uint(a))
			padded_cells := int(ibltParam.ItemOverhead * float64(a));
			cells := ibltParam.NumHashFuncs * int(math.Ceil(float64(padded_cells) / float64(ibltParam.NumHashFuncs)));
			return (nChecksumBits / 8.0 + IBLT_FIXED_CELL_SIZE) * float64(cells);
	};


func BloomFalsePositiveRate(optSymDiff float64, nReceiverExcessItems uint64) float64 {

	    fpr := 0.0;
	    if optSymDiff >= float64(nReceiverExcessItems) {
				fpr = FILTER_FPR_MAX;

			} else {
				fpr = optSymDiff / float64(nReceiverExcessItems);

			}
	    return fpr;
	}


func OptimalOverhead(numItems int) int {
    ibltParam := iblt.GetIbltParams(uint(numItems))

    return int(ibltParam.ItemOverhead)
}


// Package bytefmt contains helper methods and constants for converting to and from a human-readable byte format.
//
//	bytefmt.ByteSize(100.5*bytefmt.MEGABYTE) // "100.5M"
//	bytefmt.ByteSize(uint64(1024)) // "1K"
//

const (
	BYTE = 1 << (10 * iota)
	KILOBYTE
	MEGABYTE
	GIGABYTE
	TERABYTE
	PETABYTE
	EXABYTE
)

var invalidByteQuantityError = errors.New("byte quantity must be a positive integer with a unit of measurement like M, MB, MiB, G, GiB, or GB")

// ByteSize returns a human-readable byte string of the form 10M, 12.5K, and so forth.  The following units are available:
//	E: Exabyte
//	P: Petabyte
//	T: Terabyte
//	G: Gigabyte
//	M: Megabyte
//	K: Kilobyte
//	B: Byte
// The unit that results in the smallest number greater than or equal to 1 is always chosen.
func ByteSize(bytes uint64) string {
	unit := ""
	value := float64(bytes)

	switch {
	case bytes >= EXABYTE:
		unit = "E"
		value = value / EXABYTE
	case bytes >= PETABYTE:
		unit = "P"
		value = value / PETABYTE
	case bytes >= TERABYTE:
		unit = "T"
		value = value / TERABYTE
	case bytes >= GIGABYTE:
		unit = "G"
		value = value / GIGABYTE
	case bytes >= MEGABYTE:
		unit = "M"
		value = value / MEGABYTE
	case bytes >= KILOBYTE:
		unit = "K"
		value = value / KILOBYTE
	case bytes >= BYTE:
		unit = "B"
	case bytes == 0:
		return "0B"
	}

	result := strconv.FormatFloat(value, 'f', 1, 64)
	result = strings.TrimSuffix(result, ".0")
	return result + unit
}

// ToMegabytes parses a string formatted by ByteSize as megabytes.
func ToMegabytes(s string) (uint64, error) {
	bytes, err := ToBytes(s)
	if err != nil {
		return 0, err
	}

	return bytes / MEGABYTE, nil
}

// ToBytes parses a string formatted by ByteSize as bytes. Note binary-prefixed and SI prefixed units both mean a base-2 units
// KB = K = KiB	= 1024
// MB = M = MiB = 1024 * K
// GB = G = GiB = 1024 * M
// TB = T = TiB = 1024 * G
// PB = P = PiB = 1024 * T
// EB = E = EiB = 1024 * P
func ToBytes(s string) (uint64, error) {
	s = strings.TrimSpace(s)
	s = strings.ToUpper(s)

	i := strings.IndexFunc(s, unicode.IsLetter)

	if i == -1 {
		return 0, invalidByteQuantityError
	}

	bytesString, multiple := s[:i], s[i:]
	bytesString = strings.TrimSpace(bytesString)
	bytes, err := strconv.ParseFloat(bytesString, 64)

	if err != nil || bytes < 0 {
		return 0, invalidByteQuantityError
	}

	switch multiple {
	case "E", "EB", "EIB":
		return uint64(bytes * EXABYTE), nil
	case "P", "PB", "PIB":
		return uint64(bytes * PETABYTE), nil
	case "T", "TB", "TIB":
		return uint64(bytes * TERABYTE), nil
	case "G", "GB", "GIB":
		return uint64(bytes * GIGABYTE), nil
	case "M", "MB", "MIB":
		return uint64(bytes * MEGABYTE), nil
	case "K", "KB", "KIB":
		return uint64(bytes * KILOBYTE), nil
	case "B":
		return uint64(bytes), nil
	default:
		return 0, invalidByteQuantityError
	}
}

func getTxID(blockHash common.Hash) string {
	txHash := blockHash.Bytes()[:6]
	return string(txHash[:])
}
