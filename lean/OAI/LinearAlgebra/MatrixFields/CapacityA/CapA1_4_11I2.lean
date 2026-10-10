import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SupportedContraction

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_4_11I2PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 4 11)) (shape 1 4 11) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) a
def CA1_4_11I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 4 11) A1_4_11Law 2 a
lemma CA1_4_11I2PairRaw_sound (a : PairSlot × PairSlot) :
    (CA1_4_11I2PairRaw a).Encloses (CA1_4_11I2PairValue a) := by
  exact stageAPairBall_sound (shape 1 4 11) (by decide +kernel) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (fun u _ => A1_4_11Law_sound u) 2 a
def CA1_4_11I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(61436712352474830488612391 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7372459591722180802103669681 / 100000000000000000000000000000000), (1235931 / 50000000000000000000000000000000)⟩ ⟨(-1200008807343871317001204918543989 / 100000000000000000000000000000000), (201170406373 / 50000000000000000000000000000000)⟩ ⟨-18, 61436712352474830488612391, 38146972656250000000000000⟩,
   .log ⟨(20890993075933606986049075471 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(44255518130701293310819022579 / 25000000000000000000000000000000), (7741721 / 12500000000000000000000000000000)⟩ ⟨(-847360735219113820046267163931973 / 100000000000000000000000000000000), (74115384087 / 25000000000000000000000000000000)⟩ ⟨-13, 20890993075933606986049075471, 12207031250000000000000000000⟩,
   .log ⟨(12647475172166827455070439 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2187112567878730349464064949 / 10000000000000000000000000000000), (3557 / 48828125000000000000000000000)⟩ ⟨(-1080804932459902736691495491288357 / 100000000000000000000000000000000), (359989052027 / 100000000000000000000000000000000)⟩ ⟨-16, 12647475172166827455070439, 9536743164062500000000000⟩,
   .log ⟨(247638212185665772009484323 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(26264822769214557249286875369 / 100000000000000000000000000000000), (2228679 / 25000000000000000000000000000000)⟩ ⟨(-530306339587095105926029728199953 / 50000000000000000000000000000000), (22499315187 / 6250000000000000000000000000000)⟩ ⟨-16, 247638212185665772009484323, 152587890625000000000000000⟩,
   .log ⟨(69447984709920411412613034571 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(51096815302679477193995154419 / 3125000000000000000000000000000), (294123663 / 50000000000000000000000000000000)⟩ ⟨(-588605305292672876755862321341519 / 100000000000000000000000000000000), (211758237549 / 100000000000000000000000000000000)⟩ ⟨-9, 69447984709920411412613034571, 48828125000000000000000000000⟩,
   .log ⟨(530086454874906741118217258983 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(163418910837898166576723149541 / 2000000000000000000000000000000), (628600979 / 20000000000000000000000000000000)⟩ ⟨(-38535909882016987914182026336639 / 10000000000000000000000000000000), (37057691563 / 25000000000000000000000000000000)⟩ ⟨-6, 530086454874906741118217258983, 390625000000000000000000000000⟩,
   .log ⟨(36353911613803057996403498157 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(475024151536006995650968084953 / 50000000000000000000000000000000), (169361289 / 50000000000000000000000000000000)⟩ ⟨(-653332929592708737962053091580513 / 100000000000000000000000000000000), (582335153 / 250000000000000000000000000000)⟩ ⟨-10, 36353911613803057996403498157, 24414062500000000000000000000⟩,
   .log ⟨(246603819537866388940074677 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(74550597575614554248039379723 / 100000000000000000000000000000000), (12532899 / 50000000000000000000000000000000)⟩ ⟨(-472358088087160571858308357214297 / 50000000000000000000000000000000), (79409341979 / 25000000000000000000000000000000)⟩ ⟨-14, 246603819537866388940074677, 190734863281250000000000000⟩,
   .log ⟨(4104145260099889041045443621 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(19305449453087283873116811937 / 25000000000000000000000000000000), (814769 / 3125000000000000000000000000000)⟩ ⟨(-470389039120350646964104214669537 / 50000000000000000000000000000000), (317637367427 / 100000000000000000000000000000000)⟩ ⟨-14, 4104145260099889041045443621, 3051757812500000000000000000⟩,
   .log ⟨(600828099618234061392902613529 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(8960323050853044634501556597273 / 100000000000000000000000000000000), (178122421 / 5000000000000000000000000000000)⟩ ⟨(-372832223415750294598111936759829 / 100000000000000000000000000000000), (148230766197 / 100000000000000000000000000000000)⟩ ⟨-6, 600828099618234061392902613529, 390625000000000000000000000000⟩,
   .log ⟨(93456021197746811342512607853 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(26075854183003606395757775073 / 4000000000000000000000000000000), (59370249 / 25000000000000000000000000000000)⟩ ⟨(-348771725042584591538500912392203 / 50000000000000000000000000000000), (127054942633 / 50000000000000000000000000000000)⟩ ⟨-11, 93456021197746811342512607853, 48828125000000000000000000000⟩,
   .log ⟨(284072886806370408119373327 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(3628022640385256911008687731 / 100000000000000000000000000000000), (120311 / 10000000000000000000000000000000)⟩ ⟨(-63857249475170566733952604570697 / 5000000000000000000000000000000), (211758412841 / 50000000000000000000000000000000)⟩ ⟨-19, 284072886806370408119373327, 190734863281250000000000000⟩,
   .log ⟨(94239156817735785123068899863 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(591251052228123992924326317639 / 50000000000000000000000000000000), (87806041 / 20000000000000000000000000000000)⟩ ⟨(-313697125586362789199873511438207 / 50000000000000000000000000000000), (116467030787 / 50000000000000000000000000000000)⟩ ⟨-10, 94239156817735785123068899863, 48828125000000000000000000000⟩,
   .log ⟨(3477934774897537944856216767 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(8323862696055864315472366073 / 12500000000000000000000000000000), (5523613 / 25000000000000000000000000000000)⟩ ⟨(-239333490556938070483060085432873 / 25000000000000000000000000000000), (15881868481 / 5000000000000000000000000000000)⟩ ⟨-14, 3477934774897537944856216767, 3051757812500000000000000000⟩,
   .log ⟨(503911615790262895556819127379 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2665956788363537793012590795623 / 100000000000000000000000000000000), (960366937 / 100000000000000000000000000000000)⟩ ⟨(-132263114444317408776508448138551 / 25000000000000000000000000000000), (95291206871 / 50000000000000000000000000000000)⟩ ⟨-8, 503911615790262895556819127379, 390625000000000000000000000000⟩,
   .log ⟨(15037030684492895073999860934781 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩ ⟨(28489975068915472258197911036001 / 100000000000000000000000000000000), (12736860571 / 100000000000000000000000000000000)⟩ ⟨(-23683178935632614221075250605851 / 12500000000000000000000000000000), (84703295077 / 100000000000000000000000000000000)⟩ ⟨-3, 15037030684492895073999860934781, 12500000000000000000000000000000⟩,
   .log ⟨(527266867202792760023966491371 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(960062586291216178629491724419 / 20000000000000000000000000000000), (1786449657 / 100000000000000000000000000000000)⟩ ⟨(-227603573733082047463521721259441 / 50000000000000000000000000000000), (169406589843 / 100000000000000000000000000000000)⟩ ⟨-7, 527266867202792760023966491371, 390625000000000000000000000000⟩]
lemma CA1_4_11I2PairCertificates_valid :
    CA1_4_11I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 5, 5, 4, 0 => 1
  | 5, 5, 2, 1 => 2
  | 5, 5, 3, 1 => 3
  | 5, 5, 1, 2 => 2
  | 5, 5, 1, 3 => 3
  | 5, 5, 0, 4 => 1
  | 4, 5, 5, 0 => 4
  | 4, 5, 4, 1 => 5
  | 4, 5, 2, 2 => 6
  | 4, 5, 2, 3 => 7
  | 4, 5, 3, 2 => 7
  | 4, 5, 3, 3 => 8
  | 4, 5, 1, 4 => 5
  | 4, 5, 0, 5 => 4
  | 5, 4, 5, 0 => 4
  | 5, 4, 4, 1 => 5
  | 5, 4, 2, 2 => 6
  | 5, 4, 2, 3 => 7
  | 5, 4, 3, 2 => 7
  | 5, 4, 3, 3 => 8
  | 5, 4, 1, 4 => 5
  | 5, 4, 0, 5 => 4
  | 2, 5, 5, 1 => 9
  | 2, 5, 4, 2 => 10
  | 2, 5, 4, 3 => 11
  | 2, 5, 2, 4 => 10
  | 2, 5, 3, 4 => 11
  | 2, 5, 1, 5 => 9
  | 3, 5, 5, 1 => 12
  | 3, 5, 4, 2 => 13
  | 3, 5, 4, 3 => 14
  | 3, 5, 2, 4 => 13
  | 3, 5, 3, 4 => 14
  | 3, 5, 1, 5 => 12
  | 4, 4, 5, 1 => 15
  | 4, 4, 4, 2 => 16
  | 4, 4, 4, 3 => 17
  | 4, 4, 2, 4 => 16
  | 4, 4, 3, 4 => 17
  | 4, 4, 1, 5 => 15
  | 5, 2, 5, 1 => 9
  | 5, 2, 4, 2 => 10
  | 5, 2, 4, 3 => 11
  | 5, 2, 2, 4 => 10
  | 5, 2, 3, 4 => 11
  | 5, 2, 1, 5 => 9
  | 5, 3, 5, 1 => 12
  | 5, 3, 4, 2 => 13
  | 5, 3, 4, 3 => 14
  | 5, 3, 2, 4 => 13
  | 5, 3, 3, 4 => 14
  | 5, 3, 1, 5 => 12
  | 1, 5, 5, 2 => 9
  | 1, 5, 5, 3 => 12
  | 1, 5, 4, 4 => 15
  | 1, 5, 2, 5 => 9
  | 1, 5, 3, 5 => 12
  | 2, 4, 5, 2 => 10
  | 2, 4, 5, 3 => 13
  | 2, 4, 4, 4 => 16
  | 2, 4, 2, 5 => 10
  | 2, 4, 3, 5 => 13
  | 3, 4, 5, 2 => 11
  | 3, 4, 5, 3 => 14
  | 3, 4, 4, 4 => 17
  | 3, 4, 2, 5 => 11
  | 3, 4, 3, 5 => 14
  | 4, 2, 5, 2 => 10
  | 4, 2, 5, 3 => 13
  | 4, 2, 4, 4 => 16
  | 4, 2, 2, 5 => 10
  | 4, 2, 3, 5 => 13
  | 4, 3, 5, 2 => 11
  | 4, 3, 5, 3 => 14
  | 4, 3, 4, 4 => 17
  | 4, 3, 2, 5 => 11
  | 4, 3, 3, 5 => 14
  | 5, 1, 5, 2 => 9
  | 5, 1, 5, 3 => 12
  | 5, 1, 4, 4 => 15
  | 5, 1, 2, 5 => 9
  | 5, 1, 3, 5 => 12
  | 5, 0, 4, 5 => 4
  | 5, 0, 5, 4 => 4
  | 4, 1, 4, 5 => 5
  | 4, 1, 5, 4 => 5
  | 2, 2, 4, 5 => 6
  | 2, 2, 5, 4 => 6
  | 2, 3, 4, 5 => 7
  | 2, 3, 5, 4 => 7
  | 3, 2, 4, 5 => 7
  | 3, 2, 5, 4 => 7
  | 3, 3, 4, 5 => 8
  | 3, 3, 5, 4 => 8
  | 1, 4, 4, 5 => 5
  | 1, 4, 5, 4 => 5
  | 0, 5, 4, 5 => 4
  | 0, 5, 5, 4 => 4
  | 4, 0, 5, 5 => 1
  | 2, 1, 5, 5 => 2
  | 3, 1, 5, 5 => 3
  | 1, 2, 5, 5 => 2
  | 1, 3, 5, 5 => 3
  | 0, 4, 5, 5 => 1
  | _, _, _, _ => 0
def CA1_4_11I2PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2PairCertificates (CA1_4_11I2PairCertificateIndex a)).input
lemma CA1_4_11I2PairP_check_0_0 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((0,0),(k,l))) (CA1_4_11I2PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_0_1 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((0,1),(k,l))) (CA1_4_11I2PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_0_2 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((0,2),(k,l))) (CA1_4_11I2PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_0_3 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((0,3),(k,l))) (CA1_4_11I2PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_0_4 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((0,4),(k,l))) (CA1_4_11I2PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_0_5 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((0,5),(k,l))) (CA1_4_11I2PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_1_0 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((1,0),(k,l))) (CA1_4_11I2PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_1_1 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((1,1),(k,l))) (CA1_4_11I2PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_1_2 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((1,2),(k,l))) (CA1_4_11I2PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_1_3 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((1,3),(k,l))) (CA1_4_11I2PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_1_4 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((1,4),(k,l))) (CA1_4_11I2PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_1_5 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((1,5),(k,l))) (CA1_4_11I2PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_2_0 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((2,0),(k,l))) (CA1_4_11I2PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_2_1 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((2,1),(k,l))) (CA1_4_11I2PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_2_2 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((2,2),(k,l))) (CA1_4_11I2PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_2_3 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((2,3),(k,l))) (CA1_4_11I2PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_2_4 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((2,4),(k,l))) (CA1_4_11I2PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_2_5 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((2,5),(k,l))) (CA1_4_11I2PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_3_0 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((3,0),(k,l))) (CA1_4_11I2PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_3_1 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((3,1),(k,l))) (CA1_4_11I2PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_3_2 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((3,2),(k,l))) (CA1_4_11I2PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_3_3 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((3,3),(k,l))) (CA1_4_11I2PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_3_4 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((3,4),(k,l))) (CA1_4_11I2PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_3_5 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((3,5),(k,l))) (CA1_4_11I2PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_4_0 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((4,0),(k,l))) (CA1_4_11I2PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_4_1 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((4,1),(k,l))) (CA1_4_11I2PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_4_2 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((4,2),(k,l))) (CA1_4_11I2PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_4_3 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((4,3),(k,l))) (CA1_4_11I2PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_4_4 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((4,4),(k,l))) (CA1_4_11I2PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_4_5 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((4,5),(k,l))) (CA1_4_11I2PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_5_0 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((5,0),(k,l))) (CA1_4_11I2PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_5_1 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((5,1),(k,l))) (CA1_4_11I2PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_5_2 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((5,2),(k,l))) (CA1_4_11I2PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_5_3 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((5,3),(k,l))) (CA1_4_11I2PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_5_4 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((5,4),(k,l))) (CA1_4_11I2PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check_5_5 : ∀ k l : Fin 6, contains (CA1_4_11I2PairRaw ((5,5),(k,l))) (CA1_4_11I2PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I2PairP_check (a : PairSlot × PairSlot) : contains (CA1_4_11I2PairRaw a) (CA1_4_11I2PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA1_4_11I2PairP_check_0_0 k l) (CA1_4_11I2PairP_check_0_1 k l) (CA1_4_11I2PairP_check_0_2 k l) (CA1_4_11I2PairP_check_0_3 k l) (CA1_4_11I2PairP_check_0_4 k l) (CA1_4_11I2PairP_check_0_5 k l)
  · exact forall_fin6 (CA1_4_11I2PairP_check_1_0 k l) (CA1_4_11I2PairP_check_1_1 k l) (CA1_4_11I2PairP_check_1_2 k l) (CA1_4_11I2PairP_check_1_3 k l) (CA1_4_11I2PairP_check_1_4 k l) (CA1_4_11I2PairP_check_1_5 k l)
  · exact forall_fin6 (CA1_4_11I2PairP_check_2_0 k l) (CA1_4_11I2PairP_check_2_1 k l) (CA1_4_11I2PairP_check_2_2 k l) (CA1_4_11I2PairP_check_2_3 k l) (CA1_4_11I2PairP_check_2_4 k l) (CA1_4_11I2PairP_check_2_5 k l)
  · exact forall_fin6 (CA1_4_11I2PairP_check_3_0 k l) (CA1_4_11I2PairP_check_3_1 k l) (CA1_4_11I2PairP_check_3_2 k l) (CA1_4_11I2PairP_check_3_3 k l) (CA1_4_11I2PairP_check_3_4 k l) (CA1_4_11I2PairP_check_3_5 k l)
  · exact forall_fin6 (CA1_4_11I2PairP_check_4_0 k l) (CA1_4_11I2PairP_check_4_1 k l) (CA1_4_11I2PairP_check_4_2 k l) (CA1_4_11I2PairP_check_4_3 k l) (CA1_4_11I2PairP_check_4_4 k l) (CA1_4_11I2PairP_check_4_5 k l)
  · exact forall_fin6 (CA1_4_11I2PairP_check_5_0 k l) (CA1_4_11I2PairP_check_5_1 k l) (CA1_4_11I2PairP_check_5_2 k l) (CA1_4_11I2PairP_check_5_3 k l) (CA1_4_11I2PairP_check_5_4 k l) (CA1_4_11I2PairP_check_5_5 k l)
lemma CA1_4_11I2PairP_sound (a : PairSlot × PairSlot) :
    (CA1_4_11I2PairP a).Encloses (CA1_4_11I2PairValue a) :=
  contains_sound (CA1_4_11I2PairRaw_sound a) (CA1_4_11I2PairP_check a)
def CA1_4_11I2PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2PairCertificates (CA1_4_11I2PairCertificateIndex a)).output
lemma CA1_4_11I2PairTerms_sound (a : PairSlot × PairSlot) :
    (CA1_4_11I2PairTerms a).Encloses (Foundation.entropyTerm (CA1_4_11I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2PairCertificates_valid
    (CA1_4_11I2PairCertificateIndex a) (CA1_4_11I2PairP_sound a)
def CA1_4_11I2PairEntropy : Ball := ⟨(71515153480864000296843130640223 / 25000000000000000000000000000000), (14585933523 / 12500000000000000000000000000000)⟩
lemma CA1_4_11I2PairEntropy_sound : CA1_4_11I2PairEntropy.Encloses (Foundation.finiteEntropy CA1_4_11I2PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA1_4_11I2PairValue CA1_4_11I2PairTerms CA1_4_11I2PairTerms_sound) (by decide +kernel)
def CA1_4_11I2PairMass : Ball := ⟨(24999999999999999999999999999999 / 25000000000000000000000000000000), (113 / 25000000000000000000000000000000)⟩
lemma CA1_4_11I2PairMass_sound : CA1_4_11I2PairMass.Encloses (∑ a, CA1_4_11I2PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA1_4_11I2PairP CA1_4_11I2PairValue CA1_4_11I2PairP_sound) (by decide +kernel)
def CA1_4_11I2PairMassTermLogWitness : LogWitness := ⟨-1, 24999999999999999999999999999999, 12500000000000000000000000000000⟩
def CA1_4_11I2PairMassTermLog : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175823909 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I2PairMassTermLog_sound : CA1_4_11I2PairMassTermLog.Encloses (Real.log ((∑ a, CA1_4_11I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_4_11I2PairMass_sound) (w := CA1_4_11I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_4_11I2PairMassTerm : Ball := ⟨(1 / 25000000000000000000000000000000), (42351647819 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I2PairMassTerm_sound : CA1_4_11I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA1_4_11I2PairMass_sound) CA1_4_11I2PairMassTermLog_sound) (by decide +kernel)
def CA1_4_11I2PairH : Ball := ⟨(35757576740432000148421565320111 / 12500000000000000000000000000000), (159039116003 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I2PairH_sound : CA1_4_11I2PairH.Encloses (homogeneousEntropy CA1_4_11I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2PairValue CA1_4_11I2PairMassTerm_sound CA1_4_11I2PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_4_11I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA1_4_11I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA1_4_11I2R0Raw_sound (a : PairSlot) :
    (CA1_4_11I2R0Raw a).Encloses (CA1_4_11I2R0Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA1_4_11I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R0Certificates_valid :
    CA1_4_11I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R0Certificates (CA1_4_11I2R0CertificateIndex a)).input
lemma CA1_4_11I2R0P_check : ∀ a : PairSlot, contains (CA1_4_11I2R0Raw a) (CA1_4_11I2R0P a) = true := by
  decide +kernel
lemma CA1_4_11I2R0P_sound (a : PairSlot) :
    (CA1_4_11I2R0P a).Encloses (CA1_4_11I2R0Value a) :=
  contains_sound (CA1_4_11I2R0Raw_sound a) (CA1_4_11I2R0P_check a)
def CA1_4_11I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R0Certificates (CA1_4_11I2R0CertificateIndex a)).output
lemma CA1_4_11I2R0Terms_sound (a : PairSlot) :
    (CA1_4_11I2R0Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R0Certificates_valid
    (CA1_4_11I2R0CertificateIndex a) (CA1_4_11I2R0P_sound a)
def CA1_4_11I2R0Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R0Entropy_sound : CA1_4_11I2R0Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R0Value CA1_4_11I2R0Terms CA1_4_11I2R0Terms_sound) (by decide +kernel)
def CA1_4_11I2R0Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R0Mass_sound : CA1_4_11I2R0Mass.Encloses (∑ a, CA1_4_11I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R0P CA1_4_11I2R0Value CA1_4_11I2R0P_sound) (by decide +kernel)
def CA1_4_11I2R0MassTerm : Ball := .exact 0
lemma CA1_4_11I2R0MassTerm_sound : CA1_4_11I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R0Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R0Mass_sound)
def CA1_4_11I2R0H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R0H_sound : CA1_4_11I2R0H.Encloses (homogeneousEntropy CA1_4_11I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R0Value CA1_4_11I2R0MassTerm_sound CA1_4_11I2R0Entropy_sound) (by decide +kernel)
def CA1_4_11I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA1_4_11I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA1_4_11I2R1Raw_sound (a : PairSlot) :
    (CA1_4_11I2R1Raw a).Encloses (CA1_4_11I2R1Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA1_4_11I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R1Certificates_valid :
    CA1_4_11I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R1Certificates (CA1_4_11I2R1CertificateIndex a)).input
lemma CA1_4_11I2R1P_check : ∀ a : PairSlot, contains (CA1_4_11I2R1Raw a) (CA1_4_11I2R1P a) = true := by
  decide +kernel
lemma CA1_4_11I2R1P_sound (a : PairSlot) :
    (CA1_4_11I2R1P a).Encloses (CA1_4_11I2R1Value a) :=
  contains_sound (CA1_4_11I2R1Raw_sound a) (CA1_4_11I2R1P_check a)
def CA1_4_11I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R1Certificates (CA1_4_11I2R1CertificateIndex a)).output
lemma CA1_4_11I2R1Terms_sound (a : PairSlot) :
    (CA1_4_11I2R1Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R1Certificates_valid
    (CA1_4_11I2R1CertificateIndex a) (CA1_4_11I2R1P_sound a)
def CA1_4_11I2R1Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R1Entropy_sound : CA1_4_11I2R1Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R1Value CA1_4_11I2R1Terms CA1_4_11I2R1Terms_sound) (by decide +kernel)
def CA1_4_11I2R1Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R1Mass_sound : CA1_4_11I2R1Mass.Encloses (∑ a, CA1_4_11I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R1P CA1_4_11I2R1Value CA1_4_11I2R1P_sound) (by decide +kernel)
def CA1_4_11I2R1MassTerm : Ball := .exact 0
lemma CA1_4_11I2R1MassTerm_sound : CA1_4_11I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R1Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R1Mass_sound)
def CA1_4_11I2R1H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R1H_sound : CA1_4_11I2R1H.Encloses (homogeneousEntropy CA1_4_11I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R1Value CA1_4_11I2R1MassTerm_sound CA1_4_11I2R1Entropy_sound) (by decide +kernel)
def CA1_4_11I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA1_4_11I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA1_4_11I2R2Raw_sound (a : PairSlot) :
    (CA1_4_11I2R2Raw a).Encloses (CA1_4_11I2R2Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA1_4_11I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R2Certificates_valid :
    CA1_4_11I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R2Certificates (CA1_4_11I2R2CertificateIndex a)).input
lemma CA1_4_11I2R2P_check : ∀ a : PairSlot, contains (CA1_4_11I2R2Raw a) (CA1_4_11I2R2P a) = true := by
  decide +kernel
lemma CA1_4_11I2R2P_sound (a : PairSlot) :
    (CA1_4_11I2R2P a).Encloses (CA1_4_11I2R2Value a) :=
  contains_sound (CA1_4_11I2R2Raw_sound a) (CA1_4_11I2R2P_check a)
def CA1_4_11I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R2Certificates (CA1_4_11I2R2CertificateIndex a)).output
lemma CA1_4_11I2R2Terms_sound (a : PairSlot) :
    (CA1_4_11I2R2Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R2Certificates_valid
    (CA1_4_11I2R2CertificateIndex a) (CA1_4_11I2R2P_sound a)
def CA1_4_11I2R2Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R2Entropy_sound : CA1_4_11I2R2Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R2Value CA1_4_11I2R2Terms CA1_4_11I2R2Terms_sound) (by decide +kernel)
def CA1_4_11I2R2Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R2Mass_sound : CA1_4_11I2R2Mass.Encloses (∑ a, CA1_4_11I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R2P CA1_4_11I2R2Value CA1_4_11I2R2P_sound) (by decide +kernel)
def CA1_4_11I2R2MassTerm : Ball := .exact 0
lemma CA1_4_11I2R2MassTerm_sound : CA1_4_11I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R2Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R2Mass_sound)
def CA1_4_11I2R2H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R2H_sound : CA1_4_11I2R2H.Encloses (homogeneousEntropy CA1_4_11I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R2Value CA1_4_11I2R2MassTerm_sound CA1_4_11I2R2Entropy_sound) (by decide +kernel)
def CA1_4_11I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA1_4_11I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA1_4_11I2R3Raw_sound (a : PairSlot) :
    (CA1_4_11I2R3Raw a).Encloses (CA1_4_11I2R3Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA1_4_11I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(61436712352474830488612391 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7372459591722180802103669681 / 100000000000000000000000000000000), (1235931 / 50000000000000000000000000000000)⟩ ⟨(-1200008807343871317001204918543989 / 100000000000000000000000000000000), (201170406373 / 50000000000000000000000000000000)⟩ ⟨-18, 61436712352474830488612391, 38146972656250000000000000⟩,
   .log ⟨(20890993075933606986049075471 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(44255518130701293310819022579 / 25000000000000000000000000000000), (7741721 / 12500000000000000000000000000000)⟩ ⟨(-847360735219113820046267163931973 / 100000000000000000000000000000000), (74115384087 / 25000000000000000000000000000000)⟩ ⟨-13, 20890993075933606986049075471, 12207031250000000000000000000⟩,
   .log ⟨(12647475172166827455070439 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2187112567878730349464064949 / 10000000000000000000000000000000), (3557 / 48828125000000000000000000000)⟩ ⟨(-1080804932459902736691495491288357 / 100000000000000000000000000000000), (359989052027 / 100000000000000000000000000000000)⟩ ⟨-16, 12647475172166827455070439, 9536743164062500000000000⟩]
lemma CA1_4_11I2R3Certificates_valid :
    CA1_4_11I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_4_11I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R3Certificates (CA1_4_11I2R3CertificateIndex a)).input
lemma CA1_4_11I2R3P_check : ∀ a : PairSlot, contains (CA1_4_11I2R3Raw a) (CA1_4_11I2R3P a) = true := by
  decide +kernel
lemma CA1_4_11I2R3P_sound (a : PairSlot) :
    (CA1_4_11I2R3P a).Encloses (CA1_4_11I2R3Value a) :=
  contains_sound (CA1_4_11I2R3Raw_sound a) (CA1_4_11I2R3P_check a)
def CA1_4_11I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R3Certificates (CA1_4_11I2R3CertificateIndex a)).output
lemma CA1_4_11I2R3Terms_sound (a : PairSlot) :
    (CA1_4_11I2R3Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R3Certificates_valid
    (CA1_4_11I2R3CertificateIndex a) (CA1_4_11I2R3P_sound a)
def CA1_4_11I2R3Entropy : Ball := ⟨(206265657793314657540020409487 / 50000000000000000000000000000000), (35845183 / 25000000000000000000000000000000)⟩
lemma CA1_4_11I2R3Entropy_sound : CA1_4_11I2R3Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R3Value CA1_4_11I2R3Terms CA1_4_11I2R3Terms_sound) (by decide +kernel)
def CA1_4_11I2R3Mass : Ball := ⟨(23528956227005047683746469621 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I2R3Mass_sound : CA1_4_11I2R3Mass.Encloses (∑ a, CA1_4_11I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R3P CA1_4_11I2R3Value CA1_4_11I2R3P_sound) (by decide +kernel)
def CA1_4_11I2R3MassTermLogWitness : LogWitness := ⟨-12, 23528956227005047683746469621, 12207031250000000000000000000⟩
def CA1_4_11I2R3MassTermLog : Ball := ⟨(-383077322094910835836992754825221 / 50000000000000000000000000000000), (275285720629 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I2R3MassTermLog_sound : CA1_4_11I2R3MassTermLog.Encloses (Real.log ((∑ a, CA1_4_11I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_4_11I2R3Mass_sound) (w := CA1_4_11I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_4_11I2R3MassTerm : Ball := ⟨(180268190862589412980979300497 / 50000000000000000000000000000000), (1619297 / 1250000000000000000000000000000)⟩
lemma CA1_4_11I2R3MassTerm_sound : CA1_4_11I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_4_11I2R3Mass_sound) CA1_4_11I2R3MassTermLog_sound) (by decide +kernel)
def CA1_4_11I2R3H : Ball := ⟨(2599746693072524455904110899 / 5000000000000000000000000000000), (68231123 / 25000000000000000000000000000000)⟩
lemma CA1_4_11I2R3H_sound : CA1_4_11I2R3H.Encloses (homogeneousEntropy CA1_4_11I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R3Value CA1_4_11I2R3MassTerm_sound CA1_4_11I2R3Entropy_sound) (by decide +kernel)
def CA1_4_11I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA1_4_11I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA1_4_11I2R4Raw_sound (a : PairSlot) :
    (CA1_4_11I2R4Raw a).Encloses (CA1_4_11I2R4Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA1_4_11I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(675590492357013698713995109 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(502685504275185179583228751 / 6250000000000000000000000000000), (2718189 / 100000000000000000000000000000000)⟩ ⟨(-595254681600276381793198535164501 / 50000000000000000000000000000000), (80468159599 / 20000000000000000000000000000000)⟩ ⟨-18, 675590492357013698713995109, 381469726562500000000000000⟩,
   .log ⟨(133830529574469617999668594627 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1585411053395870048139682753047 / 100000000000000000000000000000000), (283397177 / 50000000000000000000000000000000)⟩ ⟨(-296160199477069350470806166977669 / 50000000000000000000000000000000), (211758237577 / 100000000000000000000000000000000)⟩ ⟨-9, 133830529574469617999668594627, 97656250000000000000000000000⟩,
   .log ⟨(284437587041342969390806612487 / 10000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(405019386275128425873996955433 / 4000000000000000000000000000000), (421624019 / 10000000000000000000000000000000)⟩ ⟨(-355982652018717647827715657652457 / 100000000000000000000000000000000), (148230766203 / 100000000000000000000000000000000)⟩ ⟨-6, 284437587041342969390806612487, 156250000000000000000000000000⟩,
   .log ⟨(147480825491657547530678195629 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(480730511466098859677777116159 / 50000000000000000000000000000000), (343533083 / 100000000000000000000000000000000)⟩ ⟨(-26076909177229525697088505975703 / 4000000000000000000000000000000), (232934061191 / 100000000000000000000000000000000)⟩ ⟨-10, 147480825491657547530678195629, 97656250000000000000000000000⟩,
   .log ⟨(43928590602018655644399493 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(4413478728619861079566301109 / 100000000000000000000000000000000), (1488373 / 100000000000000000000000000000000)⟩ ⟨(-251173476552252963534643964200933 / 20000000000000000000000000000000), (105879189553 / 25000000000000000000000000000000)⟩ ⟨-19, 43928590602018655644399493, 23841857910156250000000000⟩]
lemma CA1_4_11I2R4Certificates_valid :
    CA1_4_11I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 0 => 1
  | 4, 1 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 1, 4 => 2
  | 0, 5 => 1
  | _, _ => 0
def CA1_4_11I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R4Certificates (CA1_4_11I2R4CertificateIndex a)).input
lemma CA1_4_11I2R4P_check : ∀ a : PairSlot, contains (CA1_4_11I2R4Raw a) (CA1_4_11I2R4P a) = true := by
  decide +kernel
lemma CA1_4_11I2R4P_sound (a : PairSlot) :
    (CA1_4_11I2R4P a).Encloses (CA1_4_11I2R4Value a) :=
  contains_sound (CA1_4_11I2R4Raw_sound a) (CA1_4_11I2R4P_check a)
def CA1_4_11I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R4Certificates (CA1_4_11I2R4CertificateIndex a)).output
lemma CA1_4_11I2R4Terms_sound (a : PairSlot) :
    (CA1_4_11I2R4Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R4Certificates_valid
    (CA1_4_11I2R4CertificateIndex a) (CA1_4_11I2R4P_sound a)
def CA1_4_11I2R4Entropy : Ball := ⟨(238120753506246437010416054339 / 1562500000000000000000000000000), (1208763963 / 20000000000000000000000000000000)⟩
lemma CA1_4_11I2R4Entropy_sound : CA1_4_11I2R4Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R4Value CA1_4_11I2R4Terms CA1_4_11I2R4Terms_sound) (by decide +kernel)
def CA1_4_11I2R4Mass : Ball := ⟨(1838181124702076718805340040399 / 50000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I2R4Mass_sound : CA1_4_11I2R4Mass.Encloses (∑ a, CA1_4_11I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R4P CA1_4_11I2R4Value CA1_4_11I2R4P_sound) (by decide +kernel)
def CA1_4_11I2R4MassTermLogWitness : LogWitness := ⟨-5, 1838181124702076718805340040399, 1562500000000000000000000000000⟩
def CA1_4_11I2R4MassTermLog : Ball := ⟨(-330324644189821671673985641754329 / 100000000000000000000000000000000), (31763735667 / 25000000000000000000000000000000)⟩
lemma CA1_4_11I2R4MassTermLog_sound : CA1_4_11I2R4MassTermLog.Encloses (Real.log ((∑ a, CA1_4_11I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_4_11I2R4Mass_sound) (w := CA1_4_11I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_4_11I2R4MassTerm : Ball := ⟨(3035982629868298560652886595353 / 25000000000000000000000000000000), (2335500009 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I2R4MassTerm_sound : CA1_4_11I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_4_11I2R4Mass_sound) CA1_4_11I2R4MassTermLog_sound) (by decide +kernel)
def CA1_4_11I2R4H : Ball := ⟨(773949426231644431513770274071 / 25000000000000000000000000000000), (10714819833 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I2R4H_sound : CA1_4_11I2R4H.Encloses (homogeneousEntropy CA1_4_11I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R4Value CA1_4_11I2R4MassTerm_sound CA1_4_11I2R4Entropy_sound) (by decide +kernel)
def CA1_4_11I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA1_4_11I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA1_4_11I2R5Raw_sound (a : PairSlot) :
    (CA1_4_11I2R5Raw a).Encloses (CA1_4_11I2R5Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA1_4_11I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18138120034399794853090260729 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(156258265537147701001751566529 / 100000000000000000000000000000000), (53772559 / 100000000000000000000000000000000)⟩ ⟨(-430745483106288237002291658559271 / 50000000000000000000000000000000), (11858461483 / 4000000000000000000000000000000)⟩ ⟨-13, 18138120034399794853090260729, 12207031250000000000000000000⟩,
   .log ⟨(752915443548722822830379625787 / 6250000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩ ⟨(25495328928592416167136082228937 / 100000000000000000000000000000000), (12754883817 / 100000000000000000000000000000000)⟩ ⟨(-211638381399983837207000776148451 / 100000000000000000000000000000000), (52939559303 / 50000000000000000000000000000000)⟩ ⟨-4, 752915443548722822830379625787, 390625000000000000000000000000⟩,
   .log ⟨(111141817618374134334930680753 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(481539625883784876366837532177 / 20000000000000000000000000000000), (423633523 / 50000000000000000000000000000000)⟩ ⟨(-27079120409095235826197750264821 / 5000000000000000000000000000000), (47645603399 / 25000000000000000000000000000000)⟩ ⟨-8, 111141817618374134334930680753, 97656250000000000000000000000⟩]
lemma CA1_4_11I2R5Certificates_valid :
    CA1_4_11I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA1_4_11I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R5Certificates (CA1_4_11I2R5CertificateIndex a)).input
lemma CA1_4_11I2R5P_check : ∀ a : PairSlot, contains (CA1_4_11I2R5Raw a) (CA1_4_11I2R5P a) = true := by
  decide +kernel
lemma CA1_4_11I2R5P_sound (a : PairSlot) :
    (CA1_4_11I2R5P a).Encloses (CA1_4_11I2R5Value a) :=
  contains_sound (CA1_4_11I2R5Raw_sound a) (CA1_4_11I2R5P_check a)
def CA1_4_11I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R5Certificates (CA1_4_11I2R5CertificateIndex a)).output
lemma CA1_4_11I2R5Terms_sound (a : PairSlot) :
    (CA1_4_11I2R5Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R5Certificates_valid
    (CA1_4_11I2R5CertificateIndex a) (CA1_4_11I2R5P_sound a)
def CA1_4_11I2R5Entropy : Ball := ⟨(28059285323548488249972021456351 / 50000000000000000000000000000000), (6827961711 / 25000000000000000000000000000000)⟩
lemma CA1_4_11I2R5Entropy_sound : CA1_4_11I2R5Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R5Value CA1_4_11I2R5Terms CA1_4_11I2R5Terms_sound) (by decide +kernel)
def CA1_4_11I2R5Mass : Ball := ⟨(12509352487287461497478886996333 / 50000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
lemma CA1_4_11I2R5Mass_sound : CA1_4_11I2R5Mass.Encloses (∑ a, CA1_4_11I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R5P CA1_4_11I2R5Value CA1_4_11I2R5P_sound) (by decide +kernel)
def CA1_4_11I2R5MassTermLogWitness : LogWitness := ⟨-2, 12509352487287461497478886996333, 12500000000000000000000000000000⟩
def CA1_4_11I2R5MassTermLog : Ball := ⟨(-17319330523727708959248212380091 / 12500000000000000000000000000000), (7940933907 / 12500000000000000000000000000000)⟩
lemma CA1_4_11I2R5MassTermLog_sound : CA1_4_11I2R5MassTermLog.Encloses (Real.log ((∑ a, CA1_4_11I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_4_11I2R5Mass_sound) (w := CA1_4_11I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_4_11I2R5MassTerm : Ball := ⟨(34664577658423499082858619295681 / 100000000000000000000000000000000), (3973437671 / 25000000000000000000000000000000)⟩
lemma CA1_4_11I2R5MassTerm_sound : CA1_4_11I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_4_11I2R5Mass_sound) CA1_4_11I2R5MassTermLog_sound) (by decide +kernel)
def CA1_4_11I2R5H : Ball := ⟨(21453992988673477417085423617021 / 100000000000000000000000000000000), (5400699691 / 12500000000000000000000000000000)⟩
lemma CA1_4_11I2R5H_sound : CA1_4_11I2R5H.Encloses (homogeneousEntropy CA1_4_11I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R5Value CA1_4_11I2R5MassTerm_sound CA1_4_11I2R5Entropy_sound) (by decide +kernel)
def CA1_4_11I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA1_4_11I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA1_4_11I2R6Raw_sound (a : PairSlot) :
    (CA1_4_11I2R6Raw a).Encloses (CA1_4_11I2R6Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA1_4_11I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(177571602779606609244244421869 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1124658898503515455075567975467 / 100000000000000000000000000000000), (10340619 / 2500000000000000000000000000000)⟩ ⟨(-158338788536389508578027784169353 / 25000000000000000000000000000000), (232934061639 / 100000000000000000000000000000000)⟩ ⟨-10, 177571602779606609244244421869, 97656250000000000000000000000⟩,
   .log ⟨(1398464475151336582003091 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(179069061735961277107640157 / 100000000000000000000000000000000), (11849 / 20000000000000000000000000000000)⟩ ⟨(-400146609276093460159869386768671 / 25000000000000000000000000000000), (10588090609 / 2000000000000000000000000000000)⟩ ⟨-24, 1398464475151336582003091, 745058059692382812500000⟩,
   .log ⟨(930993068943178587526919271357 / 5000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩ ⟨(31298895088922340799913625208817 / 100000000000000000000000000000000), (985727261 / 6250000000000000000000000000000)⟩ ⟨(-168094135891105168076544183405379 / 100000000000000000000000000000000), (84703294957 / 100000000000000000000000000000000)⟩ ⟨-3, 930993068943178587526919271357, 625000000000000000000000000000⟩]
lemma CA1_4_11I2R6Certificates_valid :
    CA1_4_11I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA1_4_11I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R6Certificates (CA1_4_11I2R6CertificateIndex a)).input
lemma CA1_4_11I2R6P_check : ∀ a : PairSlot, contains (CA1_4_11I2R6Raw a) (CA1_4_11I2R6P a) = true := by
  decide +kernel
lemma CA1_4_11I2R6P_sound (a : PairSlot) :
    (CA1_4_11I2R6P a).Encloses (CA1_4_11I2R6Value a) :=
  contains_sound (CA1_4_11I2R6Raw_sound a) (CA1_4_11I2R6P_check a)
def CA1_4_11I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R6Certificates (CA1_4_11I2R6CertificateIndex a)).output
lemma CA1_4_11I2R6Terms_sound (a : PairSlot) :
    (CA1_4_11I2R6Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R6Certificates_valid
    (CA1_4_11I2R6CertificateIndex a) (CA1_4_11I2R6P_sound a)
def CA1_4_11I2R6Entropy : Ball := ⟨(6709714204810568726523795288013 / 20000000000000000000000000000000), (8299502093 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I2R6Entropy_sound : CA1_4_11I2R6Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R6Value CA1_4_11I2R6Terms CA1_4_11I2R6Terms_sound) (by decide +kernel)
def CA1_4_11I2R6Mass : Ball := ⟨(9487513479927193695206093160167 / 50000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
lemma CA1_4_11I2R6Mass_sound : CA1_4_11I2R6Mass.Encloses (∑ a, CA1_4_11I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R6P CA1_4_11I2R6Value CA1_4_11I2R6P_sound) (by decide +kernel)
def CA1_4_11I2R6MassTermLogWitness : LogWitness := ⟨-3, 9487513479927193695206093160167, 6250000000000000000000000000000⟩
def CA1_4_11I2R6MassTermLog : Ball := ⟨(-83102322094910835836992839972633 / 50000000000000000000000000000000), (10587911873 / 12500000000000000000000000000000)⟩
lemma CA1_4_11I2R6MassTermLog_sound : CA1_4_11I2R6MassTermLog.Encloses (Real.log ((∑ a, CA1_4_11I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_4_11I2R6Mass_sound) (w := CA1_4_11I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_4_11I2R6MassTerm : Ball := ⟨(15768688021774360428200263096397 / 50000000000000000000000000000000), (803623657 / 5000000000000000000000000000000)⟩
lemma CA1_4_11I2R6MassTerm_sound : CA1_4_11I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_4_11I2R6Mass_sound) CA1_4_11I2R6MassTermLog_sound) (by decide +kernel)
def CA1_4_11I2R6H : Ball := ⟨(2011194980504122776218450247271 / 100000000000000000000000000000000), (16335738663 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I2R6H_sound : CA1_4_11I2R6H.Encloses (homogeneousEntropy CA1_4_11I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R6Value CA1_4_11I2R6MassTerm_sound CA1_4_11I2R6Entropy_sound) (by decide +kernel)
def CA1_4_11I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA1_4_11I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA1_4_11I2R7Raw_sound (a : PairSlot) :
    (CA1_4_11I2R7Raw a).Encloses (CA1_4_11I2R7Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA1_4_11I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R7Certificates_valid :
    CA1_4_11I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R7Certificates (CA1_4_11I2R7CertificateIndex a)).input
lemma CA1_4_11I2R7P_check : ∀ a : PairSlot, contains (CA1_4_11I2R7Raw a) (CA1_4_11I2R7P a) = true := by
  decide +kernel
lemma CA1_4_11I2R7P_sound (a : PairSlot) :
    (CA1_4_11I2R7P a).Encloses (CA1_4_11I2R7Value a) :=
  contains_sound (CA1_4_11I2R7Raw_sound a) (CA1_4_11I2R7P_check a)
def CA1_4_11I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R7Certificates (CA1_4_11I2R7CertificateIndex a)).output
lemma CA1_4_11I2R7Terms_sound (a : PairSlot) :
    (CA1_4_11I2R7Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R7Certificates_valid
    (CA1_4_11I2R7CertificateIndex a) (CA1_4_11I2R7P_sound a)
def CA1_4_11I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R7Entropy_sound : CA1_4_11I2R7Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R7Value CA1_4_11I2R7Terms CA1_4_11I2R7Terms_sound) (by decide +kernel)
def CA1_4_11I2R7Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R7Mass_sound : CA1_4_11I2R7Mass.Encloses (∑ a, CA1_4_11I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R7P CA1_4_11I2R7Value CA1_4_11I2R7P_sound) (by decide +kernel)
def CA1_4_11I2R7MassTerm : Ball := .exact 0
lemma CA1_4_11I2R7MassTerm_sound : CA1_4_11I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R7Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R7Mass_sound)
def CA1_4_11I2R7H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R7H_sound : CA1_4_11I2R7H.Encloses (homogeneousEntropy CA1_4_11I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R7Value CA1_4_11I2R7MassTerm_sound CA1_4_11I2R7Entropy_sound) (by decide +kernel)
def CA1_4_11I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA1_4_11I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA1_4_11I2R8Raw_sound (a : PairSlot) :
    (CA1_4_11I2R8Raw a).Encloses (CA1_4_11I2R8Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA1_4_11I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R8Certificates_valid :
    CA1_4_11I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R8Certificates (CA1_4_11I2R8CertificateIndex a)).input
lemma CA1_4_11I2R8P_check : ∀ a : PairSlot, contains (CA1_4_11I2R8Raw a) (CA1_4_11I2R8P a) = true := by
  decide +kernel
lemma CA1_4_11I2R8P_sound (a : PairSlot) :
    (CA1_4_11I2R8P a).Encloses (CA1_4_11I2R8Value a) :=
  contains_sound (CA1_4_11I2R8Raw_sound a) (CA1_4_11I2R8P_check a)
def CA1_4_11I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R8Certificates (CA1_4_11I2R8CertificateIndex a)).output
lemma CA1_4_11I2R8Terms_sound (a : PairSlot) :
    (CA1_4_11I2R8Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R8Certificates_valid
    (CA1_4_11I2R8CertificateIndex a) (CA1_4_11I2R8P_sound a)
def CA1_4_11I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R8Entropy_sound : CA1_4_11I2R8Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R8Value CA1_4_11I2R8Terms CA1_4_11I2R8Terms_sound) (by decide +kernel)
def CA1_4_11I2R8Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R8Mass_sound : CA1_4_11I2R8Mass.Encloses (∑ a, CA1_4_11I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R8P CA1_4_11I2R8Value CA1_4_11I2R8P_sound) (by decide +kernel)
def CA1_4_11I2R8MassTerm : Ball := .exact 0
lemma CA1_4_11I2R8MassTerm_sound : CA1_4_11I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R8Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R8Mass_sound)
def CA1_4_11I2R8H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R8H_sound : CA1_4_11I2R8H.Encloses (homogeneousEntropy CA1_4_11I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R8Value CA1_4_11I2R8MassTerm_sound CA1_4_11I2R8Entropy_sound) (by decide +kernel)
def CA1_4_11I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA1_4_11I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA1_4_11I2R9Raw_sound (a : PairSlot) :
    (CA1_4_11I2R9Raw a).Encloses (CA1_4_11I2R9Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA1_4_11I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R9Certificates_valid :
    CA1_4_11I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R9Certificates (CA1_4_11I2R9CertificateIndex a)).input
lemma CA1_4_11I2R9P_check : ∀ a : PairSlot, contains (CA1_4_11I2R9Raw a) (CA1_4_11I2R9P a) = true := by
  decide +kernel
lemma CA1_4_11I2R9P_sound (a : PairSlot) :
    (CA1_4_11I2R9P a).Encloses (CA1_4_11I2R9Value a) :=
  contains_sound (CA1_4_11I2R9Raw_sound a) (CA1_4_11I2R9P_check a)
def CA1_4_11I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R9Certificates (CA1_4_11I2R9CertificateIndex a)).output
lemma CA1_4_11I2R9Terms_sound (a : PairSlot) :
    (CA1_4_11I2R9Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R9Certificates_valid
    (CA1_4_11I2R9CertificateIndex a) (CA1_4_11I2R9P_sound a)
def CA1_4_11I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R9Entropy_sound : CA1_4_11I2R9Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R9Value CA1_4_11I2R9Terms CA1_4_11I2R9Terms_sound) (by decide +kernel)
def CA1_4_11I2R9Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R9Mass_sound : CA1_4_11I2R9Mass.Encloses (∑ a, CA1_4_11I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R9P CA1_4_11I2R9Value CA1_4_11I2R9P_sound) (by decide +kernel)
def CA1_4_11I2R9MassTerm : Ball := .exact 0
lemma CA1_4_11I2R9MassTerm_sound : CA1_4_11I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R9Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R9Mass_sound)
def CA1_4_11I2R9H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R9H_sound : CA1_4_11I2R9H.Encloses (homogeneousEntropy CA1_4_11I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R9Value CA1_4_11I2R9MassTerm_sound CA1_4_11I2R9Entropy_sound) (by decide +kernel)
def CA1_4_11I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA1_4_11I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA1_4_11I2R10Raw_sound (a : PairSlot) :
    (CA1_4_11I2R10Raw a).Encloses (CA1_4_11I2R10Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA1_4_11I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R10Certificates_valid :
    CA1_4_11I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R10Certificates (CA1_4_11I2R10CertificateIndex a)).input
lemma CA1_4_11I2R10P_check : ∀ a : PairSlot, contains (CA1_4_11I2R10Raw a) (CA1_4_11I2R10P a) = true := by
  decide +kernel
lemma CA1_4_11I2R10P_sound (a : PairSlot) :
    (CA1_4_11I2R10P a).Encloses (CA1_4_11I2R10Value a) :=
  contains_sound (CA1_4_11I2R10Raw_sound a) (CA1_4_11I2R10P_check a)
def CA1_4_11I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R10Certificates (CA1_4_11I2R10CertificateIndex a)).output
lemma CA1_4_11I2R10Terms_sound (a : PairSlot) :
    (CA1_4_11I2R10Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R10Certificates_valid
    (CA1_4_11I2R10CertificateIndex a) (CA1_4_11I2R10P_sound a)
def CA1_4_11I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R10Entropy_sound : CA1_4_11I2R10Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R10Value CA1_4_11I2R10Terms CA1_4_11I2R10Terms_sound) (by decide +kernel)
def CA1_4_11I2R10Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R10Mass_sound : CA1_4_11I2R10Mass.Encloses (∑ a, CA1_4_11I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R10P CA1_4_11I2R10Value CA1_4_11I2R10P_sound) (by decide +kernel)
def CA1_4_11I2R10MassTerm : Ball := .exact 0
lemma CA1_4_11I2R10MassTerm_sound : CA1_4_11I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R10Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R10Mass_sound)
def CA1_4_11I2R10H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R10H_sound : CA1_4_11I2R10H.Encloses (homogeneousEntropy CA1_4_11I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R10Value CA1_4_11I2R10MassTerm_sound CA1_4_11I2R10Entropy_sound) (by decide +kernel)
def CA1_4_11I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA1_4_11I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA1_4_11I2R11Raw_sound (a : PairSlot) :
    (CA1_4_11I2R11Raw a).Encloses (CA1_4_11I2R11Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA1_4_11I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R11Certificates_valid :
    CA1_4_11I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R11Certificates (CA1_4_11I2R11CertificateIndex a)).input
lemma CA1_4_11I2R11P_check : ∀ a : PairSlot, contains (CA1_4_11I2R11Raw a) (CA1_4_11I2R11P a) = true := by
  decide +kernel
lemma CA1_4_11I2R11P_sound (a : PairSlot) :
    (CA1_4_11I2R11P a).Encloses (CA1_4_11I2R11Value a) :=
  contains_sound (CA1_4_11I2R11Raw_sound a) (CA1_4_11I2R11P_check a)
def CA1_4_11I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R11Certificates (CA1_4_11I2R11CertificateIndex a)).output
lemma CA1_4_11I2R11Terms_sound (a : PairSlot) :
    (CA1_4_11I2R11Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R11Certificates_valid
    (CA1_4_11I2R11CertificateIndex a) (CA1_4_11I2R11P_sound a)
def CA1_4_11I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R11Entropy_sound : CA1_4_11I2R11Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R11Value CA1_4_11I2R11Terms CA1_4_11I2R11Terms_sound) (by decide +kernel)
def CA1_4_11I2R11Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R11Mass_sound : CA1_4_11I2R11Mass.Encloses (∑ a, CA1_4_11I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R11P CA1_4_11I2R11Value CA1_4_11I2R11P_sound) (by decide +kernel)
def CA1_4_11I2R11MassTerm : Ball := .exact 0
lemma CA1_4_11I2R11MassTerm_sound : CA1_4_11I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R11Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R11Mass_sound)
def CA1_4_11I2R11H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R11H_sound : CA1_4_11I2R11H.Encloses (homogeneousEntropy CA1_4_11I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R11Value CA1_4_11I2R11MassTerm_sound CA1_4_11I2R11Entropy_sound) (by decide +kernel)
def CA1_4_11I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA1_4_11I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA1_4_11I2R12Raw_sound (a : PairSlot) :
    (CA1_4_11I2R12Raw a).Encloses (CA1_4_11I2R12Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA1_4_11I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R12Certificates_valid :
    CA1_4_11I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R12Certificates (CA1_4_11I2R12CertificateIndex a)).input
lemma CA1_4_11I2R12P_check : ∀ a : PairSlot, contains (CA1_4_11I2R12Raw a) (CA1_4_11I2R12P a) = true := by
  decide +kernel
lemma CA1_4_11I2R12P_sound (a : PairSlot) :
    (CA1_4_11I2R12P a).Encloses (CA1_4_11I2R12Value a) :=
  contains_sound (CA1_4_11I2R12Raw_sound a) (CA1_4_11I2R12P_check a)
def CA1_4_11I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R12Certificates (CA1_4_11I2R12CertificateIndex a)).output
lemma CA1_4_11I2R12Terms_sound (a : PairSlot) :
    (CA1_4_11I2R12Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R12Certificates_valid
    (CA1_4_11I2R12CertificateIndex a) (CA1_4_11I2R12P_sound a)
def CA1_4_11I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R12Entropy_sound : CA1_4_11I2R12Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R12Value CA1_4_11I2R12Terms CA1_4_11I2R12Terms_sound) (by decide +kernel)
def CA1_4_11I2R12Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R12Mass_sound : CA1_4_11I2R12Mass.Encloses (∑ a, CA1_4_11I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R12P CA1_4_11I2R12Value CA1_4_11I2R12P_sound) (by decide +kernel)
def CA1_4_11I2R12MassTerm : Ball := .exact 0
lemma CA1_4_11I2R12MassTerm_sound : CA1_4_11I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R12Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R12Mass_sound)
def CA1_4_11I2R12H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R12H_sound : CA1_4_11I2R12H.Encloses (homogeneousEntropy CA1_4_11I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R12Value CA1_4_11I2R12MassTerm_sound CA1_4_11I2R12Entropy_sound) (by decide +kernel)
def CA1_4_11I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA1_4_11I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA1_4_11I2R13Raw_sound (a : PairSlot) :
    (CA1_4_11I2R13Raw a).Encloses (CA1_4_11I2R13Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA1_4_11I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R13Certificates_valid :
    CA1_4_11I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R13Certificates (CA1_4_11I2R13CertificateIndex a)).input
lemma CA1_4_11I2R13P_check : ∀ a : PairSlot, contains (CA1_4_11I2R13Raw a) (CA1_4_11I2R13P a) = true := by
  decide +kernel
lemma CA1_4_11I2R13P_sound (a : PairSlot) :
    (CA1_4_11I2R13P a).Encloses (CA1_4_11I2R13Value a) :=
  contains_sound (CA1_4_11I2R13Raw_sound a) (CA1_4_11I2R13P_check a)
def CA1_4_11I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R13Certificates (CA1_4_11I2R13CertificateIndex a)).output
lemma CA1_4_11I2R13Terms_sound (a : PairSlot) :
    (CA1_4_11I2R13Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R13Certificates_valid
    (CA1_4_11I2R13CertificateIndex a) (CA1_4_11I2R13P_sound a)
def CA1_4_11I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R13Entropy_sound : CA1_4_11I2R13Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R13Value CA1_4_11I2R13Terms CA1_4_11I2R13Terms_sound) (by decide +kernel)
def CA1_4_11I2R13Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R13Mass_sound : CA1_4_11I2R13Mass.Encloses (∑ a, CA1_4_11I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R13P CA1_4_11I2R13Value CA1_4_11I2R13P_sound) (by decide +kernel)
def CA1_4_11I2R13MassTerm : Ball := .exact 0
lemma CA1_4_11I2R13MassTerm_sound : CA1_4_11I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R13Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R13Mass_sound)
def CA1_4_11I2R13H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R13H_sound : CA1_4_11I2R13H.Encloses (homogeneousEntropy CA1_4_11I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R13Value CA1_4_11I2R13MassTerm_sound CA1_4_11I2R13Entropy_sound) (by decide +kernel)
def CA1_4_11I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA1_4_11I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA1_4_11I2R14Raw_sound (a : PairSlot) :
    (CA1_4_11I2R14Raw a).Encloses (CA1_4_11I2R14Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA1_4_11I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R14Certificates_valid :
    CA1_4_11I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R14Certificates (CA1_4_11I2R14CertificateIndex a)).input
lemma CA1_4_11I2R14P_check : ∀ a : PairSlot, contains (CA1_4_11I2R14Raw a) (CA1_4_11I2R14P a) = true := by
  decide +kernel
lemma CA1_4_11I2R14P_sound (a : PairSlot) :
    (CA1_4_11I2R14P a).Encloses (CA1_4_11I2R14Value a) :=
  contains_sound (CA1_4_11I2R14Raw_sound a) (CA1_4_11I2R14P_check a)
def CA1_4_11I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R14Certificates (CA1_4_11I2R14CertificateIndex a)).output
lemma CA1_4_11I2R14Terms_sound (a : PairSlot) :
    (CA1_4_11I2R14Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R14Certificates_valid
    (CA1_4_11I2R14CertificateIndex a) (CA1_4_11I2R14P_sound a)
def CA1_4_11I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R14Entropy_sound : CA1_4_11I2R14Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R14Value CA1_4_11I2R14Terms CA1_4_11I2R14Terms_sound) (by decide +kernel)
def CA1_4_11I2R14Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R14Mass_sound : CA1_4_11I2R14Mass.Encloses (∑ a, CA1_4_11I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R14P CA1_4_11I2R14Value CA1_4_11I2R14P_sound) (by decide +kernel)
def CA1_4_11I2R14MassTerm : Ball := .exact 0
lemma CA1_4_11I2R14MassTerm_sound : CA1_4_11I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R14Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R14Mass_sound)
def CA1_4_11I2R14H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R14H_sound : CA1_4_11I2R14H.Encloses (homogeneousEntropy CA1_4_11I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R14Value CA1_4_11I2R14MassTerm_sound CA1_4_11I2R14Entropy_sound) (by decide +kernel)
def CA1_4_11I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA1_4_11I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA1_4_11I2R15Raw_sound (a : PairSlot) :
    (CA1_4_11I2R15Raw a).Encloses (CA1_4_11I2R15Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA1_4_11I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R15Certificates_valid :
    CA1_4_11I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R15Certificates (CA1_4_11I2R15CertificateIndex a)).input
lemma CA1_4_11I2R15P_check : ∀ a : PairSlot, contains (CA1_4_11I2R15Raw a) (CA1_4_11I2R15P a) = true := by
  decide +kernel
lemma CA1_4_11I2R15P_sound (a : PairSlot) :
    (CA1_4_11I2R15P a).Encloses (CA1_4_11I2R15Value a) :=
  contains_sound (CA1_4_11I2R15Raw_sound a) (CA1_4_11I2R15P_check a)
def CA1_4_11I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R15Certificates (CA1_4_11I2R15CertificateIndex a)).output
lemma CA1_4_11I2R15Terms_sound (a : PairSlot) :
    (CA1_4_11I2R15Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R15Certificates_valid
    (CA1_4_11I2R15CertificateIndex a) (CA1_4_11I2R15P_sound a)
def CA1_4_11I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R15Entropy_sound : CA1_4_11I2R15Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R15Value CA1_4_11I2R15Terms CA1_4_11I2R15Terms_sound) (by decide +kernel)
def CA1_4_11I2R15Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R15Mass_sound : CA1_4_11I2R15Mass.Encloses (∑ a, CA1_4_11I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R15P CA1_4_11I2R15Value CA1_4_11I2R15P_sound) (by decide +kernel)
def CA1_4_11I2R15MassTerm : Ball := .exact 0
lemma CA1_4_11I2R15MassTerm_sound : CA1_4_11I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R15Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R15Mass_sound)
def CA1_4_11I2R15H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R15H_sound : CA1_4_11I2R15H.Encloses (homogeneousEntropy CA1_4_11I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R15Value CA1_4_11I2R15MassTerm_sound CA1_4_11I2R15Entropy_sound) (by decide +kernel)
def CA1_4_11I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA1_4_11I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA1_4_11I2R16Raw_sound (a : PairSlot) :
    (CA1_4_11I2R16Raw a).Encloses (CA1_4_11I2R16Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA1_4_11I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I2R16Certificates_valid :
    CA1_4_11I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R16Certificates (CA1_4_11I2R16CertificateIndex a)).input
lemma CA1_4_11I2R16P_check : ∀ a : PairSlot, contains (CA1_4_11I2R16Raw a) (CA1_4_11I2R16P a) = true := by
  decide +kernel
lemma CA1_4_11I2R16P_sound (a : PairSlot) :
    (CA1_4_11I2R16P a).Encloses (CA1_4_11I2R16Value a) :=
  contains_sound (CA1_4_11I2R16Raw_sound a) (CA1_4_11I2R16P_check a)
def CA1_4_11I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R16Certificates (CA1_4_11I2R16CertificateIndex a)).output
lemma CA1_4_11I2R16Terms_sound (a : PairSlot) :
    (CA1_4_11I2R16Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I2R16Certificates_valid
    (CA1_4_11I2R16CertificateIndex a) (CA1_4_11I2R16P_sound a)
def CA1_4_11I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R16Entropy_sound : CA1_4_11I2R16Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I2R16Value CA1_4_11I2R16Terms CA1_4_11I2R16Terms_sound) (by decide +kernel)
def CA1_4_11I2R16Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R16Mass_sound : CA1_4_11I2R16Mass.Encloses (∑ a, CA1_4_11I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I2R16P CA1_4_11I2R16Value CA1_4_11I2R16P_sound) (by decide +kernel)
def CA1_4_11I2R16MassTerm : Ball := .exact 0
lemma CA1_4_11I2R16MassTerm_sound : CA1_4_11I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I2R16Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I2R16Mass_sound)
def CA1_4_11I2R16H : Ball := ⟨0, 0⟩
lemma CA1_4_11I2R16H_sound : CA1_4_11I2R16H.Encloses (homogeneousEntropy CA1_4_11I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I2R16Value CA1_4_11I2R16MassTerm_sound CA1_4_11I2R16Entropy_sound) (by decide +kernel)
def CA1_4_11I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_4_11I2R0H
  | 1 => CA1_4_11I2R1H
  | 2 => CA1_4_11I2R2H
  | 3 => CA1_4_11I2R3H
  | 4 => CA1_4_11I2R4H
  | 5 => CA1_4_11I2R5H
  | 6 => CA1_4_11I2R6H
  | 7 => CA1_4_11I2R7H
  | 8 => CA1_4_11I2R8H
  | 9 => CA1_4_11I2R9H
  | 10 => CA1_4_11I2R10H
  | 11 => CA1_4_11I2R11H
  | 12 => CA1_4_11I2R12H
  | 13 => CA1_4_11I2R13H
  | 14 => CA1_4_11I2R14H
  | 15 => CA1_4_11I2R15H
  | 16 => CA1_4_11I2R16H
  | _ => (.exact 0)
lemma CA1_4_11I2ResidualEntropies_sound (k : Fin 17) :
    (CA1_4_11I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_4_11I2R0H_sound
  · exact CA1_4_11I2R1H_sound
  · exact CA1_4_11I2R2H_sound
  · exact CA1_4_11I2R3H_sound
  · exact CA1_4_11I2R4H_sound
  · exact CA1_4_11I2R5H_sound
  · exact CA1_4_11I2R6H_sound
  · exact CA1_4_11I2R7H_sound
  · exact CA1_4_11I2R8H_sound
  · exact CA1_4_11I2R9H_sound
  · exact CA1_4_11I2R10H_sound
  · exact CA1_4_11I2R11H_sound
  · exact CA1_4_11I2R12H_sound
  · exact CA1_4_11I2R13H_sound
  · exact CA1_4_11I2R14H_sound
  · exact CA1_4_11I2R15H_sound
  · exact CA1_4_11I2R16H_sound
def CA1_4_11I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 1, 0, 7 => Z1_0_7H2H
  | _, _, _ => (.exact 0)
lemma CA1_4_11I2Singles_sound (u : Shape) (hu : u ∈ below (shape 1 4 11))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA1_4_11I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A1_4_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 4 3) by decide +kernel) hd |>.elim
def CA1_4_11I2Singleton : Ball := ⟨(56488132491887973451105759346661 / 100000000000000000000000000000000), (24495359647 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I2Singleton_sound : CA1_4_11I2Singleton.Encloses
    (singletonEntropy (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA1_4_11I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_4_11Law_sound u) CA1_4_11I2Singles_sound) (by decide +kernel)
def CA1_4_11I2Group : Ball := ⟨(83101113099853601859582796525217 / 100000000000000000000000000000000), (135855538473 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I2Group_sound : CA1_4_11I2Group.Encloses
    (groupedEntropy (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_4_11I2Singleton_sound
    (finSumBall_sound 17 CA1_4_11I2ResidualEntropies _ CA1_4_11I2ResidualEntropies_sound)) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_4_11I2H : Ball := ⟨(59929193861874398734103464755227 / 50000000000000000000000000000000), (430750192949 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I2_sound : CA1_4_11I2H.Encloses (stageACapacity (shape 1 4 11) 2) := by
  have hb := contains_sound (Ball.add_sound CA1_4_11I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_4_11I2Group_sound)))
    (show contains (.add CA1_4_11I2PairH (.neg (.mul (.exact 2) CA1_4_11I2Group))) CA1_4_11I2H = true by decide +kernel)
  unfold CA1_4_11I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
