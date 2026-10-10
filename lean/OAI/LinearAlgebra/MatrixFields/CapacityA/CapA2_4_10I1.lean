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
def CA2_4_10I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 2 4 10)) (shape 2 4 10) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA2_4_10I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 4 10) A2_4_10Law 1 a
lemma CA2_4_10I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA2_4_10I1PairRaw a).Encloses (CA2_4_10I1PairValue a) := by
  exact stageAPairBall_sound (shape 2 4 10) (by decide +kernel) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (fun u _ => A2_4_10Law_sound u) 1 a
def CA2_4_10I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1570267050551735974943873725333 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(1304554149917839056437223571411 / 20000000000000000000000000000000), (2327618947 / 100000000000000000000000000000000)⟩ ⟨(-415392448519971536465802051772989 / 100000000000000000000000000000000), (9264422917 / 6250000000000000000000000000000)⟩ ⟨-6, 1570267050551735974943873725333, 1562500000000000000000000000000⟩,
   .log ⟨(3034387089383124528122128843 / 2000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(984794096329826778408729518697 / 100000000000000000000000000000000), (353406069 / 100000000000000000000000000000000)⟩ ⟨(-81136162536371588356964125744811 / 12500000000000000000000000000000), (232934061831 / 100000000000000000000000000000000)⟩ ⟨-10, 3034387089383124528122128843, 1953125000000000000000000000⟩,
   .log ⟨(953593008292007130199388873 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(134080594248960785344959468161 / 100000000000000000000000000000000), (45232593 / 100000000000000000000000000000000)⟩ ⟨(-878785505733692706370894943601029 / 100000000000000000000000000000000), (59292307623 / 20000000000000000000000000000000)⟩ ⟨-13, 953593008292007130199388873, 762939453125000000000000000⟩,
   .log ⟨(303667440279865518063022157441 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1760357815737784962170102391733 / 100000000000000000000000000000000), (643040839 / 100000000000000000000000000000000)⟩ ⟨(-144924807720199332735360433851017 / 25000000000000000000000000000000), (105879118909 / 50000000000000000000000000000000)⟩ ⟨-9, 303667440279865518063022157441, 195312500000000000000000000000⟩,
   .log ⟨(4295678730458672526115271023 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(43194406613782287477000663553 / 100000000000000000000000000000000), (7277169 / 50000000000000000000000000000000)⟩ ⟨(-502765794698643470656208650110853 / 50000000000000000000000000000000), (338813202207 / 100000000000000000000000000000000)⟩ ⟨-15, 4295678730458672526115271023, 3051757812500000000000000000⟩,
   .log ⟨(2528984564228431434820444687137 / 50000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩ ⟨(15094017477510129457010294452863 / 100000000000000000000000000000000), (1606599971 / 25000000000000000000000000000000)⟩ ⟨(-14921025706334399094195115931971 / 5000000000000000000000000000000), (12705494277 / 10000000000000000000000000000000)⟩ ⟨-5, 2528984564228431434820444687137, 1562500000000000000000000000000⟩,
   .log ⟨(122420790923018468574288295871 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(260470646978220434206094808563 / 10000000000000000000000000000000), (29164063 / 3125000000000000000000000000000)⟩ ⟨(-531916688771459333603262788731019 / 100000000000000000000000000000000), (190582413963 / 100000000000000000000000000000000)⟩ ⟨-8, 122420790923018468574288295871, 97656250000000000000000000000⟩,
   .log ⟨(60600842512749909065437114167 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(364957805749404454085143082913 / 25000000000000000000000000000000), (128327281 / 25000000000000000000000000000000)⟩ ⟨(-301116115401052710030492793355751 / 50000000000000000000000000000000), (211758238067 / 100000000000000000000000000000000)⟩ ⟨-9, 60600842512749909065437114167, 48828125000000000000000000000⟩,
   .log ⟨(1425649691580132680461890821801 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(6059784678668181098739670143709 / 100000000000000000000000000000000), (301893073 / 12500000000000000000000000000000)⟩ ⟨(-26565890951583273860873471957703 / 6250000000000000000000000000000), (84703295153 / 50000000000000000000000000000000)⟩ ⟨-7, 1425649691580132680461890821801, 781250000000000000000000000000⟩,
   .log ⟨(71380118090287457174125633539 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(187066129933937167370719339141 / 20000000000000000000000000000000), (332537231 / 100000000000000000000000000000000)⟩ ⟨(-3275879455980314197911224765219 / 500000000000000000000000000000), (232934061913 / 100000000000000000000000000000000)⟩ ⟨-10, 71380118090287457174125633539, 48828125000000000000000000000⟩,
   .log ⟨(5194274658497938993575257267147 / 100000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩ ⟨(240041488503310393902760243513 / 1562500000000000000000000000000), (6599582787 / 100000000000000000000000000000000)⟩ ⟨(-295761319418838368875440969706011 / 100000000000000000000000000000000), (63527471357 / 50000000000000000000000000000000)⟩ ⟨-5, 5194274658497938993575257267147, 3125000000000000000000000000000⟩,
   .log ⟨(224121877578321584972333781 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(126937003819149110868295781031 / 100000000000000000000000000000000), (42523861 / 100000000000000000000000000000000)⟩ ⟨(-884960766037260043466052530094137 / 100000000000000000000000000000000), (296461538533 / 100000000000000000000000000000000)⟩ ⟨-13, 224121877578321584972333781, 190734863281250000000000000⟩,
   .log ⟨(104128067974015647083683350937 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(136872856753006379266553856473 / 5000000000000000000000000000000), (992248949 / 100000000000000000000000000000000)⟩ ⟨(-525786598814690158746556680501431 / 100000000000000000000000000000000), (95291206957 / 50000000000000000000000000000000)⟩ ⟨-8, 104128067974015647083683350937, 78125000000000000000000000000⟩,
   .log ⟨(18908059881216521834005381548437 / 100000000000000000000000000000000), (83 / 100000000000000000000000000000000)⟩ ⟨(3936615302164090789828690581369 / 12500000000000000000000000000000), (16015749911 / 100000000000000000000000000000000)⟩ ⟨(-1040988691302688453154033716209 / 625000000000000000000000000000), (84703295171 / 100000000000000000000000000000000)⟩ ⟨-3, 18908059881216521834005381548437, 12500000000000000000000000000000⟩]
lemma CA2_4_10I1PairCertificates_valid :
    CA2_4_10I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 2, 2 => 1
  | 0, 0, 2, 3 => 2
  | 0, 0, 3, 2 => 2
  | 0, 0, 3, 3 => 3
  | 0, 0, 4, 1 => 4
  | 0, 0, 5, 0 => 5
  | 0, 0, 1, 4 => 4
  | 0, 0, 0, 5 => 5
  | 1, 0, 1, 2 => 6
  | 1, 0, 1, 3 => 7
  | 1, 0, 2, 1 => 6
  | 1, 0, 3, 1 => 7
  | 1, 0, 4, 0 => 8
  | 1, 0, 0, 4 => 8
  | 0, 1, 1, 2 => 6
  | 0, 1, 1, 3 => 7
  | 0, 1, 2, 1 => 6
  | 0, 1, 3, 1 => 7
  | 0, 1, 4, 0 => 8
  | 0, 1, 0, 4 => 8
  | 2, 0, 0, 2 => 9
  | 2, 0, 0, 3 => 10
  | 2, 0, 1, 1 => 11
  | 2, 0, 2, 0 => 9
  | 2, 0, 3, 0 => 10
  | 3, 0, 0, 2 => 10
  | 3, 0, 0, 3 => 12
  | 3, 0, 1, 1 => 13
  | 3, 0, 2, 0 => 10
  | 3, 0, 3, 0 => 12
  | 1, 1, 0, 2 => 11
  | 1, 1, 0, 3 => 13
  | 1, 1, 1, 1 => 14
  | 1, 1, 2, 0 => 11
  | 1, 1, 3, 0 => 13
  | 0, 2, 0, 2 => 9
  | 0, 2, 0, 3 => 10
  | 0, 2, 1, 1 => 11
  | 0, 2, 2, 0 => 9
  | 0, 2, 3, 0 => 10
  | 0, 3, 0, 2 => 10
  | 0, 3, 0, 3 => 12
  | 0, 3, 1, 1 => 13
  | 0, 3, 2, 0 => 10
  | 0, 3, 3, 0 => 12
  | 4, 0, 0, 1 => 8
  | 4, 0, 1, 0 => 8
  | 2, 1, 0, 1 => 6
  | 2, 1, 1, 0 => 6
  | 3, 1, 0, 1 => 7
  | 3, 1, 1, 0 => 7
  | 1, 2, 0, 1 => 6
  | 1, 2, 1, 0 => 6
  | 1, 3, 0, 1 => 7
  | 1, 3, 1, 0 => 7
  | 0, 4, 0, 1 => 8
  | 0, 4, 1, 0 => 8
  | 0, 5, 0, 0 => 5
  | 1, 4, 0, 0 => 4
  | 2, 2, 0, 0 => 1
  | 2, 3, 0, 0 => 2
  | 3, 2, 0, 0 => 2
  | 3, 3, 0, 0 => 3
  | 4, 1, 0, 0 => 4
  | 5, 0, 0, 0 => 5
  | _, _, _, _ => 0
def CA2_4_10I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1PairCertificates (CA2_4_10I1PairCertificateIndex a)).input
lemma CA2_4_10I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((0,0),(k,l))) (CA2_4_10I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((0,1),(k,l))) (CA2_4_10I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((0,2),(k,l))) (CA2_4_10I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((0,3),(k,l))) (CA2_4_10I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((0,4),(k,l))) (CA2_4_10I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((0,5),(k,l))) (CA2_4_10I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((1,0),(k,l))) (CA2_4_10I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((1,1),(k,l))) (CA2_4_10I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((1,2),(k,l))) (CA2_4_10I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((1,3),(k,l))) (CA2_4_10I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((1,4),(k,l))) (CA2_4_10I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((1,5),(k,l))) (CA2_4_10I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((2,0),(k,l))) (CA2_4_10I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((2,1),(k,l))) (CA2_4_10I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((2,2),(k,l))) (CA2_4_10I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((2,3),(k,l))) (CA2_4_10I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((2,4),(k,l))) (CA2_4_10I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((2,5),(k,l))) (CA2_4_10I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((3,0),(k,l))) (CA2_4_10I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((3,1),(k,l))) (CA2_4_10I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((3,2),(k,l))) (CA2_4_10I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((3,3),(k,l))) (CA2_4_10I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((3,4),(k,l))) (CA2_4_10I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((3,5),(k,l))) (CA2_4_10I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((4,0),(k,l))) (CA2_4_10I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((4,1),(k,l))) (CA2_4_10I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((4,2),(k,l))) (CA2_4_10I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((4,3),(k,l))) (CA2_4_10I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((4,4),(k,l))) (CA2_4_10I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((4,5),(k,l))) (CA2_4_10I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((5,0),(k,l))) (CA2_4_10I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((5,1),(k,l))) (CA2_4_10I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((5,2),(k,l))) (CA2_4_10I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((5,3),(k,l))) (CA2_4_10I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((5,4),(k,l))) (CA2_4_10I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA2_4_10I1PairRaw ((5,5),(k,l))) (CA2_4_10I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA2_4_10I1PairP_check (a : PairSlot × PairSlot) : contains (CA2_4_10I1PairRaw a) (CA2_4_10I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA2_4_10I1PairP_check_0_0 k l) (CA2_4_10I1PairP_check_0_1 k l) (CA2_4_10I1PairP_check_0_2 k l) (CA2_4_10I1PairP_check_0_3 k l) (CA2_4_10I1PairP_check_0_4 k l) (CA2_4_10I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA2_4_10I1PairP_check_1_0 k l) (CA2_4_10I1PairP_check_1_1 k l) (CA2_4_10I1PairP_check_1_2 k l) (CA2_4_10I1PairP_check_1_3 k l) (CA2_4_10I1PairP_check_1_4 k l) (CA2_4_10I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA2_4_10I1PairP_check_2_0 k l) (CA2_4_10I1PairP_check_2_1 k l) (CA2_4_10I1PairP_check_2_2 k l) (CA2_4_10I1PairP_check_2_3 k l) (CA2_4_10I1PairP_check_2_4 k l) (CA2_4_10I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA2_4_10I1PairP_check_3_0 k l) (CA2_4_10I1PairP_check_3_1 k l) (CA2_4_10I1PairP_check_3_2 k l) (CA2_4_10I1PairP_check_3_3 k l) (CA2_4_10I1PairP_check_3_4 k l) (CA2_4_10I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA2_4_10I1PairP_check_4_0 k l) (CA2_4_10I1PairP_check_4_1 k l) (CA2_4_10I1PairP_check_4_2 k l) (CA2_4_10I1PairP_check_4_3 k l) (CA2_4_10I1PairP_check_4_4 k l) (CA2_4_10I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA2_4_10I1PairP_check_5_0 k l) (CA2_4_10I1PairP_check_5_1 k l) (CA2_4_10I1PairP_check_5_2 k l) (CA2_4_10I1PairP_check_5_3 k l) (CA2_4_10I1PairP_check_5_4 k l) (CA2_4_10I1PairP_check_5_5 k l)
lemma CA2_4_10I1PairP_sound (a : PairSlot × PairSlot) :
    (CA2_4_10I1PairP a).Encloses (CA2_4_10I1PairValue a) :=
  contains_sound (CA2_4_10I1PairRaw_sound a) (CA2_4_10I1PairP_check a)
def CA2_4_10I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1PairCertificates (CA2_4_10I1PairCertificateIndex a)).output
lemma CA2_4_10I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA2_4_10I1PairTerms a).Encloses (Foundation.entropyTerm (CA2_4_10I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1PairCertificates_valid
    (CA2_4_10I1PairCertificateIndex a) (CA2_4_10I1PairP_sound a)
def CA2_4_10I1PairEntropy : Ball := ⟨(78464608316607251550725274170061 / 25000000000000000000000000000000), (130647428739 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1PairEntropy_sound : CA2_4_10I1PairEntropy.Encloses (Foundation.finiteEntropy CA2_4_10I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA2_4_10I1PairValue CA2_4_10I1PairTerms CA2_4_10I1PairTerms_sound) (by decide +kernel)
def CA2_4_10I1PairMass : Ball := ⟨(19999999999999999999999999999999 / 20000000000000000000000000000000), (677 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1PairMass_sound : CA2_4_10I1PairMass.Encloses (∑ a, CA2_4_10I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA2_4_10I1PairP CA2_4_10I1PairValue CA2_4_10I1PairP_sound) (by decide +kernel)
def CA2_4_10I1PairMassTermLogWitness : LogWitness := ⟨-1, 19999999999999999999999999999999, 10000000000000000000000000000000⟩
def CA2_4_10I1PairMassTermLog : Ball := ⟨(-1 / 20000000000000000000000000000000), (42351648043 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1PairMassTermLog_sound : CA2_4_10I1PairMassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I1PairMass_sound) (w := CA2_4_10I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I1PairMassTerm : Ball := ⟨(1 / 20000000000000000000000000000000), (10587912011 / 25000000000000000000000000000000)⟩
lemma CA2_4_10I1PairMassTerm_sound : CA2_4_10I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I1PairMass_sound) CA2_4_10I1PairMassTermLog_sound) (by decide +kernel)
def CA2_4_10I1PairH : Ball := ⟨(313858433266429006202901096680239 / 100000000000000000000000000000000), (172999076783 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1PairH_sound : CA2_4_10I1PairH.Encloses (homogeneousEntropy CA2_4_10I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1PairValue CA2_4_10I1PairMassTerm_sound CA2_4_10I1PairEntropy_sound) (by decide +kernel)

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
def CA2_4_10I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA2_4_10I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA2_4_10I1R0Raw_sound (a : PairSlot) :
    (CA2_4_10I1R0Raw a).Encloses (CA2_4_10I1R0Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA2_4_10I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2504889485643368923017551688527 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩ ⟨(2308835273618154621376203064027 / 25000000000000000000000000000000), (3713016947 / 100000000000000000000000000000000)⟩ ⟨(-92173139248302656677203865689747 / 25000000000000000000000000000000), (148230766459 / 100000000000000000000000000000000)⟩ ⟨-6, 2504889485643368923017551688527, 1562500000000000000000000000000⟩]
lemma CA2_4_10I1R0Certificates_valid :
    CA2_4_10I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA2_4_10I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R0Certificates (CA2_4_10I1R0CertificateIndex a)).input
lemma CA2_4_10I1R0P_check : ∀ a : PairSlot, contains (CA2_4_10I1R0Raw a) (CA2_4_10I1R0P a) = true := by
  decide +kernel
lemma CA2_4_10I1R0P_sound (a : PairSlot) :
    (CA2_4_10I1R0P a).Encloses (CA2_4_10I1R0Value a) :=
  contains_sound (CA2_4_10I1R0Raw_sound a) (CA2_4_10I1R0P_check a)
def CA2_4_10I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R0Certificates (CA2_4_10I1R0CertificateIndex a)).output
lemma CA2_4_10I1R0Terms_sound (a : PairSlot) :
    (CA2_4_10I1R0Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R0Certificates_valid
    (CA2_4_10I1R0CertificateIndex a) (CA2_4_10I1R0P_sound a)
def CA2_4_10I1R0Entropy : Ball := ⟨(2308835273618154621376203064027 / 25000000000000000000000000000000), (3713016947 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1R0Entropy_sound : CA2_4_10I1R0Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R0Value CA2_4_10I1R0Terms CA2_4_10I1R0Terms_sound) (by decide +kernel)
def CA2_4_10I1R0Mass : Ball := ⟨(2504889485643368923017551688527 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1R0Mass_sound : CA2_4_10I1R0Mass.Encloses (∑ a, CA2_4_10I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R0P CA2_4_10I1R0Value CA2_4_10I1R0P_sound) (by decide +kernel)
def CA2_4_10I1R0MassTermLogWitness : LogWitness := ⟨-6, 2504889485643368923017551688527, 1562500000000000000000000000000⟩
def CA2_4_10I1R0MassTermLog : Ball := ⟨(-92173139248302656677203865689747 / 25000000000000000000000000000000), (148230766459 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1R0MassTermLog_sound : CA2_4_10I1R0MassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I1R0Mass_sound) (w := CA2_4_10I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I1R0MassTerm : Ball := ⟨(2308835273618154621376203064027 / 25000000000000000000000000000000), (3713016947 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1R0MassTerm_sound : CA2_4_10I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I1R0Mass_sound) CA2_4_10I1R0MassTermLog_sound) (by decide +kernel)
def CA2_4_10I1R0H : Ball := ⟨0, (3713016947 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I1R0H_sound : CA2_4_10I1R0H.Encloses (homogeneousEntropy CA2_4_10I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R0Value CA2_4_10I1R0MassTerm_sound CA2_4_10I1R0Entropy_sound) (by decide +kernel)
def CA2_4_10I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA2_4_10I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA2_4_10I1R1Raw_sound (a : PairSlot) :
    (CA2_4_10I1R1Raw a).Encloses (CA2_4_10I1R1Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA2_4_10I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(11580111324399872760399582028853 / 100000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩ ⟨(24965343144609674399182126743019 / 100000000000000000000000000000000), (490436799 / 4000000000000000000000000000000)⟩ ⟨(-2155881100383417719247352642923 / 1000000000000000000000000000000), (105879118941 / 100000000000000000000000000000000)⟩ ⟨-4, 11580111324399872760399582028853, 6250000000000000000000000000000⟩]
lemma CA2_4_10I1R1Certificates_valid :
    CA2_4_10I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA2_4_10I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R1Certificates (CA2_4_10I1R1CertificateIndex a)).input
lemma CA2_4_10I1R1P_check : ∀ a : PairSlot, contains (CA2_4_10I1R1Raw a) (CA2_4_10I1R1P a) = true := by
  decide +kernel
lemma CA2_4_10I1R1P_sound (a : PairSlot) :
    (CA2_4_10I1R1P a).Encloses (CA2_4_10I1R1Value a) :=
  contains_sound (CA2_4_10I1R1Raw_sound a) (CA2_4_10I1R1P_check a)
def CA2_4_10I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R1Certificates (CA2_4_10I1R1CertificateIndex a)).output
lemma CA2_4_10I1R1Terms_sound (a : PairSlot) :
    (CA2_4_10I1R1Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R1Certificates_valid
    (CA2_4_10I1R1CertificateIndex a) (CA2_4_10I1R1P_sound a)
def CA2_4_10I1R1Entropy : Ball := ⟨(24965343144609674399182126743019 / 50000000000000000000000000000000), (490436799 / 2000000000000000000000000000000)⟩
lemma CA2_4_10I1R1Entropy_sound : CA2_4_10I1R1Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R1Value CA2_4_10I1R1Terms CA2_4_10I1R1Terms_sound) (by decide +kernel)
def CA2_4_10I1R1Mass : Ball := ⟨(11580111324399872760399582028853 / 50000000000000000000000000000000), (61 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I1R1Mass_sound : CA2_4_10I1R1Mass.Encloses (∑ a, CA2_4_10I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R1P CA2_4_10I1R1Value CA2_4_10I1R1P_sound) (by decide +kernel)
def CA2_4_10I1R1MassTermLogWitness : LogWitness := ⟨-3, 11580111324399872760399582028853, 6250000000000000000000000000000⟩
def CA2_4_10I1R1MassTermLog : Ball := ⟨(-14627339198234724098301207124197 / 10000000000000000000000000000000), (42351647629 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I1R1MassTermLog_sound : CA2_4_10I1R1MassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I1R1Mass_sound) (w := CA2_4_10I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I1R1MassTerm : Ball := ⟨(4234655407382902096081315647709 / 12500000000000000000000000000000), (1226091997 / 6250000000000000000000000000000)⟩
lemma CA2_4_10I1R1MassTerm_sound : CA2_4_10I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I1R1Mass_sound) CA2_4_10I1R1MassTermLog_sound) (by decide +kernel)
def CA2_4_10I1R1H : Ball := ⟨(8026721515078066014856864152183 / 50000000000000000000000000000000), (22069655951 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I1R1H_sound : CA2_4_10I1R1H.Encloses (homogeneousEntropy CA2_4_10I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R1Value CA2_4_10I1R1MassTerm_sound CA2_4_10I1R1Entropy_sound) (by decide +kernel)
def CA2_4_10I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA2_4_10I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA2_4_10I1R2Raw_sound (a : PairSlot) :
    (CA2_4_10I1R2Raw a).Encloses (CA2_4_10I1R2Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA2_4_10I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1666218902803870836639108288981 / 20000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩ ⟨(20704230676447350293382511103893 / 100000000000000000000000000000000), (8820889587 / 100000000000000000000000000000000)⟩ ⟨(-124258767210039430807601364073447 / 50000000000000000000000000000000), (105879118967 / 100000000000000000000000000000000)⟩ ⟨-4, 1666218902803870836639108288981, 1250000000000000000000000000000⟩,
   .log ⟨(834848412561253226991378012811 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(1997656712969327772773907353117 / 50000000000000000000000000000000), (1414288253 / 100000000000000000000000000000000)⟩ ⟨(-239283764922144922338536586260167 / 50000000000000000000000000000000), (84703295031 / 50000000000000000000000000000000)⟩ ⟨-7, 834848412561253226991378012811, 781250000000000000000000000000⟩,
   .log ⟨(15168944938976278145996364796051 / 50000000000000000000000000000000), (7 / 6250000000000000000000000000000)⟩ ⟨(36186208753457450142976308090281 / 100000000000000000000000000000000), (3854578891 / 20000000000000000000000000000000)⟩ ⟨(-11927727636639303812062773998161 / 10000000000000000000000000000000), (63527471417 / 100000000000000000000000000000000)⟩ ⟨-2, 15168944938976278145996364796051, 12500000000000000000000000000000⟩]
lemma CA2_4_10I1R2Certificates_valid :
    CA2_4_10I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA2_4_10I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R2Certificates (CA2_4_10I1R2CertificateIndex a)).input
lemma CA2_4_10I1R2P_check : ∀ a : PairSlot, contains (CA2_4_10I1R2Raw a) (CA2_4_10I1R2P a) = true := by
  decide +kernel
lemma CA2_4_10I1R2P_sound (a : PairSlot) :
    (CA2_4_10I1R2P a).Encloses (CA2_4_10I1R2Value a) :=
  contains_sound (CA2_4_10I1R2Raw_sound a) (CA2_4_10I1R2P_check a)
def CA2_4_10I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R2Certificates (CA2_4_10I1R2CertificateIndex a)).output
lemma CA2_4_10I1R2Terms_sound (a : PairSlot) :
    (CA2_4_10I1R2Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R2Certificates_valid
    (CA2_4_10I1R2CertificateIndex a) (CA2_4_10I1R2P_sound a)
def CA2_4_10I1R2Entropy : Ball := ⟨(17117059391645892364167391942107 / 20000000000000000000000000000000), (7948650027 / 20000000000000000000000000000000)⟩
lemma CA2_4_10I1R2Entropy_sound : CA2_4_10I1R2Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R2Value CA2_4_10I1R2Terms CA2_4_10I1R2Terms_sound) (by decide +kernel)
def CA2_4_10I1R2Mass : Ball := ⟨(24334887865556885556183284253767 / 50000000000000000000000000000000), (107 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I1R2Mass_sound : CA2_4_10I1R2Mass.Encloses (∑ a, CA2_4_10I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R2P CA2_4_10I1R2Value CA2_4_10I1R2P_sound) (by decide +kernel)
def CA2_4_10I1R2MassTermLogWitness : LogWitness := ⟨-2, 24334887865556885556183284253767, 12500000000000000000000000000000⟩
def CA2_4_10I1R2MassTermLog : Ball := ⟨(-36005598505125881559196550427071 / 50000000000000000000000000000000), (496308371 / 781250000000000000000000000000)⟩
lemma CA2_4_10I1R2MassTermLog_sound : CA2_4_10I1R2MassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I1R2Mass_sound) (w := CA2_4_10I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I1R2MassTerm : Ball := ⟨(1401907523447201525122493550069 / 4000000000000000000000000000000), (3864834757 / 12500000000000000000000000000000)⟩
lemma CA2_4_10I1R2MassTerm_sound : CA2_4_10I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I1R2Mass_sound) CA2_4_10I1R2MassTermLog_sound) (by decide +kernel)
def CA2_4_10I1R2H : Ball := ⟨(5053760887204942369277462095881 / 10000000000000000000000000000000), (70661928191 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1R2H_sound : CA2_4_10I1R2H.Encloses (homogeneousEntropy CA2_4_10I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R2Value CA2_4_10I1R2MassTerm_sound CA2_4_10I1R2Entropy_sound) (by decide +kernel)
def CA2_4_10I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA2_4_10I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA2_4_10I1R3Raw_sound (a : PairSlot) :
    (CA2_4_10I1R3Raw a).Encloses (CA2_4_10I1R3Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA2_4_10I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(60600842512749909065437114167 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1291810010488538332237728883911 / 50000000000000000000000000000000), (92395641 / 10000000000000000000000000000000)⟩ ⟨(-133229378186527722279815598415293 / 25000000000000000000000000000000), (190582413971 / 100000000000000000000000000000000)⟩ ⟨-8, 60600842512749909065437114167, 48828125000000000000000000000⟩,
   .log ⟨(2528984564228431434820444687137 / 25000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩ ⟨(11588100436761011118615419373789 / 50000000000000000000000000000000), (10710666447 / 100000000000000000000000000000000)⟩ ⟨(-22910579607069345094217912558909 / 10000000000000000000000000000000), (52939559509 / 50000000000000000000000000000000)⟩ ⟨-4, 2528984564228431434820444687137, 1562500000000000000000000000000⟩,
   .log ⟨(979366327384147748594306366969 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(4530567931002738314260469072711 / 100000000000000000000000000000000), (207388891 / 12500000000000000000000000000000)⟩ ⟨(-462601970715464802661539595680587 / 100000000000000000000000000000000), (42351647519 / 25000000000000000000000000000000)⟩ ⟨-7, 979366327384147748594306366969, 781250000000000000000000000000⟩]
lemma CA2_4_10I1R3Certificates_valid :
    CA2_4_10I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA2_4_10I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R3Certificates (CA2_4_10I1R3CertificateIndex a)).input
lemma CA2_4_10I1R3P_check : ∀ a : PairSlot, contains (CA2_4_10I1R3Raw a) (CA2_4_10I1R3P a) = true := by
  decide +kernel
lemma CA2_4_10I1R3P_sound (a : PairSlot) :
    (CA2_4_10I1R3P a).Encloses (CA2_4_10I1R3Value a) :=
  contains_sound (CA2_4_10I1R3Raw_sound a) (CA2_4_10I1R3P_check a)
def CA2_4_10I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R3Certificates (CA2_4_10I1R3CertificateIndex a)).output
lemma CA2_4_10I1R3Terms_sound (a : PairSlot) :
    (CA2_4_10I1R3Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R3Certificates_valid
    (CA2_4_10I1R3CertificateIndex a) (CA2_4_10I1R3P_sound a)
def CA2_4_10I1R3Entropy : Ball := ⟨(30290388825501837215966765588111 / 50000000000000000000000000000000), (2658746797 / 10000000000000000000000000000000)⟩
lemma CA2_4_10I1R3Entropy_sound : CA2_4_10I1R3Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R3Value CA2_4_10I1R3Terms CA2_4_10I1R3Terms_sound) (by decide +kernel)
def CA2_4_10I1R3Mass : Ball := ⟨(11580111324399872760399582028853 / 50000000000000000000000000000000), (71 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I1R3Mass_sound : CA2_4_10I1R3Mass.Encloses (∑ a, CA2_4_10I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R3P CA2_4_10I1R3Value CA2_4_10I1R3P_sound) (by decide +kernel)
def CA2_4_10I1R3MassTermLogWitness : LogWitness := ⟨-3, 11580111324399872760399582028853, 6250000000000000000000000000000⟩
def CA2_4_10I1R3MassTermLog : Ball := ⟨(-14627339198234724098301207124197 / 10000000000000000000000000000000), (16940659069 / 20000000000000000000000000000000)⟩
lemma CA2_4_10I1R3MassTermLog_sound : CA2_4_10I1R3MassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I1R3Mass_sound) (w := CA2_4_10I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I1R3MassTerm : Ball := ⟨(4234655407382902096081315647709 / 12500000000000000000000000000000), (19617472001 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1R3MassTerm_sound : CA2_4_10I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I1R3Mass_sound) CA2_4_10I1R3MassTermLog_sound) (by decide +kernel)
def CA2_4_10I1R3H : Ball := ⟨(534070687838809153265660119891 / 2000000000000000000000000000000), (46204939971 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1R3H_sound : CA2_4_10I1R3H.Encloses (homogeneousEntropy CA2_4_10I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R3Value CA2_4_10I1R3MassTerm_sound CA2_4_10I1R3Entropy_sound) (by decide +kernel)
def CA2_4_10I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA2_4_10I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA2_4_10I1R4Raw_sound (a : PairSlot) :
    (CA2_4_10I1R4Raw a).Encloses (CA2_4_10I1R4Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA2_4_10I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(4295678730458672526115271023 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(43194406613782287477000663553 / 100000000000000000000000000000000), (7277169 / 50000000000000000000000000000000)⟩ ⟨(-502765794698643470656208650110853 / 50000000000000000000000000000000), (338813202207 / 100000000000000000000000000000000)⟩ ⟨-15, 4295678730458672526115271023, 3051757812500000000000000000⟩,
   .log ⟨(303667440279865518063022157441 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1760357815737784962170102391733 / 100000000000000000000000000000000), (643040839 / 100000000000000000000000000000000)⟩ ⟨(-144924807720199332735360433851017 / 25000000000000000000000000000000), (105879118909 / 50000000000000000000000000000000)⟩ ⟨-9, 303667440279865518063022157441, 195312500000000000000000000000⟩,
   .log ⟨(1570267050551735974943873725333 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(1304554149917839056437223571411 / 20000000000000000000000000000000), (2327618947 / 100000000000000000000000000000000)⟩ ⟨(-415392448519971536465802051772989 / 100000000000000000000000000000000), (9264422917 / 6250000000000000000000000000000)⟩ ⟨-6, 1570267050551735974943873725333, 1562500000000000000000000000000⟩,
   .log ⟨(3034387089383124528122128843 / 2000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(984794096329826778408729518697 / 100000000000000000000000000000000), (353406069 / 100000000000000000000000000000000)⟩ ⟨(-81136162536371588356964125744811 / 12500000000000000000000000000000), (232934061831 / 100000000000000000000000000000000)⟩ ⟨-10, 3034387089383124528122128843, 1953125000000000000000000000⟩,
   .log ⟨(953593008292007130199388873 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(134080594248960785344959468161 / 100000000000000000000000000000000), (45232593 / 100000000000000000000000000000000)⟩ ⟨(-878785505733692706370894943601029 / 100000000000000000000000000000000), (59292307623 / 20000000000000000000000000000000)⟩ ⟨-13, 953593008292007130199388873, 762939453125000000000000000⟩]
lemma CA2_4_10I1R4Certificates_valid :
    CA2_4_10I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 5 => 1
  | 1, 4 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 4, 1 => 2
  | 5, 0 => 1
  | _, _ => 0
def CA2_4_10I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R4Certificates (CA2_4_10I1R4CertificateIndex a)).input
lemma CA2_4_10I1R4P_check : ∀ a : PairSlot, contains (CA2_4_10I1R4Raw a) (CA2_4_10I1R4P a) = true := by
  decide +kernel
lemma CA2_4_10I1R4P_sound (a : PairSlot) :
    (CA2_4_10I1R4P a).Encloses (CA2_4_10I1R4Value a) :=
  contains_sound (CA2_4_10I1R4Raw_sound a) (CA2_4_10I1R4P_check a)
def CA2_4_10I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R4Certificates (CA2_4_10I1R4CertificateIndex a)).output
lemma CA2_4_10I1R4Terms_sound (a : PairSlot) :
    (CA2_4_10I1R4Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R4Certificates_valid
    (CA2_4_10I1R4CertificateIndex a) (CA2_4_10I1R4P_sound a)
def CA2_4_10I1R4Entropy : Ball := ⟨(6116771990600472061821371236591 / 50000000000000000000000000000000), (274678377 / 6250000000000000000000000000000)⟩
lemma CA2_4_10I1R4Entropy_sound : CA2_4_10I1R4Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R4Value CA2_4_10I1R4Terms CA2_4_10I1R4Terms_sound) (by decide +kernel)
def CA2_4_10I1R4Mass : Ball := ⟨(2504889485643368923017551688529 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1R4Mass_sound : CA2_4_10I1R4Mass.Encloses (∑ a, CA2_4_10I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R4P CA2_4_10I1R4Value CA2_4_10I1R4P_sound) (by decide +kernel)
def CA2_4_10I1R4MassTermLogWitness : LogWitness := ⟨-6, 2504889485643368923017551688529, 1562500000000000000000000000000⟩
def CA2_4_10I1R4MassTermLog : Ball := ⟨(-92173139248302656677203865689727 / 25000000000000000000000000000000), (148230766859 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1R4MassTermLog_sound : CA2_4_10I1R4MassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I1R4Mass_sound) (w := CA2_4_10I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I1R4MassTerm : Ball := ⟨(9235341094472618485504812256113 / 100000000000000000000000000000000), (1856508497 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I1R4MassTerm_sound : CA2_4_10I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I1R4Mass_sound) CA2_4_10I1R4MassTermLog_sound) (by decide +kernel)
def CA2_4_10I1R4H : Ball := ⟨(2998202886728325638137930217069 / 100000000000000000000000000000000), (4053935513 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I1R4H_sound : CA2_4_10I1R4H.Encloses (homogeneousEntropy CA2_4_10I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R4Value CA2_4_10I1R4MassTerm_sound CA2_4_10I1R4Entropy_sound) (by decide +kernel)
def CA2_4_10I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA2_4_10I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA2_4_10I1R5Raw_sound (a : PairSlot) :
    (CA2_4_10I1R5Raw a).Encloses (CA2_4_10I1R5Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA2_4_10I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R5Certificates_valid :
    CA2_4_10I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R5Certificates (CA2_4_10I1R5CertificateIndex a)).input
lemma CA2_4_10I1R5P_check : ∀ a : PairSlot, contains (CA2_4_10I1R5Raw a) (CA2_4_10I1R5P a) = true := by
  decide +kernel
lemma CA2_4_10I1R5P_sound (a : PairSlot) :
    (CA2_4_10I1R5P a).Encloses (CA2_4_10I1R5Value a) :=
  contains_sound (CA2_4_10I1R5Raw_sound a) (CA2_4_10I1R5P_check a)
def CA2_4_10I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R5Certificates (CA2_4_10I1R5CertificateIndex a)).output
lemma CA2_4_10I1R5Terms_sound (a : PairSlot) :
    (CA2_4_10I1R5Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R5Certificates_valid
    (CA2_4_10I1R5CertificateIndex a) (CA2_4_10I1R5P_sound a)
def CA2_4_10I1R5Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R5Entropy_sound : CA2_4_10I1R5Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R5Value CA2_4_10I1R5Terms CA2_4_10I1R5Terms_sound) (by decide +kernel)
def CA2_4_10I1R5Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R5Mass_sound : CA2_4_10I1R5Mass.Encloses (∑ a, CA2_4_10I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R5P CA2_4_10I1R5Value CA2_4_10I1R5P_sound) (by decide +kernel)
def CA2_4_10I1R5MassTerm : Ball := .exact 0
lemma CA2_4_10I1R5MassTerm_sound : CA2_4_10I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R5Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R5Mass_sound)
def CA2_4_10I1R5H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R5H_sound : CA2_4_10I1R5H.Encloses (homogeneousEntropy CA2_4_10I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R5Value CA2_4_10I1R5MassTerm_sound CA2_4_10I1R5Entropy_sound) (by decide +kernel)
def CA2_4_10I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA2_4_10I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA2_4_10I1R6Raw_sound (a : PairSlot) :
    (CA2_4_10I1R6Raw a).Encloses (CA2_4_10I1R6Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA2_4_10I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R6Certificates_valid :
    CA2_4_10I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R6Certificates (CA2_4_10I1R6CertificateIndex a)).input
lemma CA2_4_10I1R6P_check : ∀ a : PairSlot, contains (CA2_4_10I1R6Raw a) (CA2_4_10I1R6P a) = true := by
  decide +kernel
lemma CA2_4_10I1R6P_sound (a : PairSlot) :
    (CA2_4_10I1R6P a).Encloses (CA2_4_10I1R6Value a) :=
  contains_sound (CA2_4_10I1R6Raw_sound a) (CA2_4_10I1R6P_check a)
def CA2_4_10I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R6Certificates (CA2_4_10I1R6CertificateIndex a)).output
lemma CA2_4_10I1R6Terms_sound (a : PairSlot) :
    (CA2_4_10I1R6Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R6Certificates_valid
    (CA2_4_10I1R6CertificateIndex a) (CA2_4_10I1R6P_sound a)
def CA2_4_10I1R6Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R6Entropy_sound : CA2_4_10I1R6Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R6Value CA2_4_10I1R6Terms CA2_4_10I1R6Terms_sound) (by decide +kernel)
def CA2_4_10I1R6Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R6Mass_sound : CA2_4_10I1R6Mass.Encloses (∑ a, CA2_4_10I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R6P CA2_4_10I1R6Value CA2_4_10I1R6P_sound) (by decide +kernel)
def CA2_4_10I1R6MassTerm : Ball := .exact 0
lemma CA2_4_10I1R6MassTerm_sound : CA2_4_10I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R6Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R6Mass_sound)
def CA2_4_10I1R6H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R6H_sound : CA2_4_10I1R6H.Encloses (homogeneousEntropy CA2_4_10I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R6Value CA2_4_10I1R6MassTerm_sound CA2_4_10I1R6Entropy_sound) (by decide +kernel)
def CA2_4_10I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA2_4_10I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA2_4_10I1R7Raw_sound (a : PairSlot) :
    (CA2_4_10I1R7Raw a).Encloses (CA2_4_10I1R7Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA2_4_10I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R7Certificates_valid :
    CA2_4_10I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R7Certificates (CA2_4_10I1R7CertificateIndex a)).input
lemma CA2_4_10I1R7P_check : ∀ a : PairSlot, contains (CA2_4_10I1R7Raw a) (CA2_4_10I1R7P a) = true := by
  decide +kernel
lemma CA2_4_10I1R7P_sound (a : PairSlot) :
    (CA2_4_10I1R7P a).Encloses (CA2_4_10I1R7Value a) :=
  contains_sound (CA2_4_10I1R7Raw_sound a) (CA2_4_10I1R7P_check a)
def CA2_4_10I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R7Certificates (CA2_4_10I1R7CertificateIndex a)).output
lemma CA2_4_10I1R7Terms_sound (a : PairSlot) :
    (CA2_4_10I1R7Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R7Certificates_valid
    (CA2_4_10I1R7CertificateIndex a) (CA2_4_10I1R7P_sound a)
def CA2_4_10I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R7Entropy_sound : CA2_4_10I1R7Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R7Value CA2_4_10I1R7Terms CA2_4_10I1R7Terms_sound) (by decide +kernel)
def CA2_4_10I1R7Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R7Mass_sound : CA2_4_10I1R7Mass.Encloses (∑ a, CA2_4_10I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R7P CA2_4_10I1R7Value CA2_4_10I1R7P_sound) (by decide +kernel)
def CA2_4_10I1R7MassTerm : Ball := .exact 0
lemma CA2_4_10I1R7MassTerm_sound : CA2_4_10I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R7Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R7Mass_sound)
def CA2_4_10I1R7H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R7H_sound : CA2_4_10I1R7H.Encloses (homogeneousEntropy CA2_4_10I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R7Value CA2_4_10I1R7MassTerm_sound CA2_4_10I1R7Entropy_sound) (by decide +kernel)
def CA2_4_10I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA2_4_10I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA2_4_10I1R8Raw_sound (a : PairSlot) :
    (CA2_4_10I1R8Raw a).Encloses (CA2_4_10I1R8Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA2_4_10I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R8Certificates_valid :
    CA2_4_10I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R8Certificates (CA2_4_10I1R8CertificateIndex a)).input
lemma CA2_4_10I1R8P_check : ∀ a : PairSlot, contains (CA2_4_10I1R8Raw a) (CA2_4_10I1R8P a) = true := by
  decide +kernel
lemma CA2_4_10I1R8P_sound (a : PairSlot) :
    (CA2_4_10I1R8P a).Encloses (CA2_4_10I1R8Value a) :=
  contains_sound (CA2_4_10I1R8Raw_sound a) (CA2_4_10I1R8P_check a)
def CA2_4_10I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R8Certificates (CA2_4_10I1R8CertificateIndex a)).output
lemma CA2_4_10I1R8Terms_sound (a : PairSlot) :
    (CA2_4_10I1R8Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R8Certificates_valid
    (CA2_4_10I1R8CertificateIndex a) (CA2_4_10I1R8P_sound a)
def CA2_4_10I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R8Entropy_sound : CA2_4_10I1R8Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R8Value CA2_4_10I1R8Terms CA2_4_10I1R8Terms_sound) (by decide +kernel)
def CA2_4_10I1R8Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R8Mass_sound : CA2_4_10I1R8Mass.Encloses (∑ a, CA2_4_10I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R8P CA2_4_10I1R8Value CA2_4_10I1R8P_sound) (by decide +kernel)
def CA2_4_10I1R8MassTerm : Ball := .exact 0
lemma CA2_4_10I1R8MassTerm_sound : CA2_4_10I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R8Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R8Mass_sound)
def CA2_4_10I1R8H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R8H_sound : CA2_4_10I1R8H.Encloses (homogeneousEntropy CA2_4_10I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R8Value CA2_4_10I1R8MassTerm_sound CA2_4_10I1R8Entropy_sound) (by decide +kernel)
def CA2_4_10I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA2_4_10I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA2_4_10I1R9Raw_sound (a : PairSlot) :
    (CA2_4_10I1R9Raw a).Encloses (CA2_4_10I1R9Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA2_4_10I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R9Certificates_valid :
    CA2_4_10I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R9Certificates (CA2_4_10I1R9CertificateIndex a)).input
lemma CA2_4_10I1R9P_check : ∀ a : PairSlot, contains (CA2_4_10I1R9Raw a) (CA2_4_10I1R9P a) = true := by
  decide +kernel
lemma CA2_4_10I1R9P_sound (a : PairSlot) :
    (CA2_4_10I1R9P a).Encloses (CA2_4_10I1R9Value a) :=
  contains_sound (CA2_4_10I1R9Raw_sound a) (CA2_4_10I1R9P_check a)
def CA2_4_10I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R9Certificates (CA2_4_10I1R9CertificateIndex a)).output
lemma CA2_4_10I1R9Terms_sound (a : PairSlot) :
    (CA2_4_10I1R9Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R9Certificates_valid
    (CA2_4_10I1R9CertificateIndex a) (CA2_4_10I1R9P_sound a)
def CA2_4_10I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R9Entropy_sound : CA2_4_10I1R9Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R9Value CA2_4_10I1R9Terms CA2_4_10I1R9Terms_sound) (by decide +kernel)
def CA2_4_10I1R9Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R9Mass_sound : CA2_4_10I1R9Mass.Encloses (∑ a, CA2_4_10I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R9P CA2_4_10I1R9Value CA2_4_10I1R9P_sound) (by decide +kernel)
def CA2_4_10I1R9MassTerm : Ball := .exact 0
lemma CA2_4_10I1R9MassTerm_sound : CA2_4_10I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R9Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R9Mass_sound)
def CA2_4_10I1R9H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R9H_sound : CA2_4_10I1R9H.Encloses (homogeneousEntropy CA2_4_10I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R9Value CA2_4_10I1R9MassTerm_sound CA2_4_10I1R9Entropy_sound) (by decide +kernel)
def CA2_4_10I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA2_4_10I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA2_4_10I1R10Raw_sound (a : PairSlot) :
    (CA2_4_10I1R10Raw a).Encloses (CA2_4_10I1R10Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA2_4_10I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R10Certificates_valid :
    CA2_4_10I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R10Certificates (CA2_4_10I1R10CertificateIndex a)).input
lemma CA2_4_10I1R10P_check : ∀ a : PairSlot, contains (CA2_4_10I1R10Raw a) (CA2_4_10I1R10P a) = true := by
  decide +kernel
lemma CA2_4_10I1R10P_sound (a : PairSlot) :
    (CA2_4_10I1R10P a).Encloses (CA2_4_10I1R10Value a) :=
  contains_sound (CA2_4_10I1R10Raw_sound a) (CA2_4_10I1R10P_check a)
def CA2_4_10I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R10Certificates (CA2_4_10I1R10CertificateIndex a)).output
lemma CA2_4_10I1R10Terms_sound (a : PairSlot) :
    (CA2_4_10I1R10Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R10Certificates_valid
    (CA2_4_10I1R10CertificateIndex a) (CA2_4_10I1R10P_sound a)
def CA2_4_10I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R10Entropy_sound : CA2_4_10I1R10Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R10Value CA2_4_10I1R10Terms CA2_4_10I1R10Terms_sound) (by decide +kernel)
def CA2_4_10I1R10Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R10Mass_sound : CA2_4_10I1R10Mass.Encloses (∑ a, CA2_4_10I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R10P CA2_4_10I1R10Value CA2_4_10I1R10P_sound) (by decide +kernel)
def CA2_4_10I1R10MassTerm : Ball := .exact 0
lemma CA2_4_10I1R10MassTerm_sound : CA2_4_10I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R10Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R10Mass_sound)
def CA2_4_10I1R10H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R10H_sound : CA2_4_10I1R10H.Encloses (homogeneousEntropy CA2_4_10I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R10Value CA2_4_10I1R10MassTerm_sound CA2_4_10I1R10Entropy_sound) (by decide +kernel)
def CA2_4_10I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA2_4_10I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA2_4_10I1R11Raw_sound (a : PairSlot) :
    (CA2_4_10I1R11Raw a).Encloses (CA2_4_10I1R11Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA2_4_10I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R11Certificates_valid :
    CA2_4_10I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R11Certificates (CA2_4_10I1R11CertificateIndex a)).input
lemma CA2_4_10I1R11P_check : ∀ a : PairSlot, contains (CA2_4_10I1R11Raw a) (CA2_4_10I1R11P a) = true := by
  decide +kernel
lemma CA2_4_10I1R11P_sound (a : PairSlot) :
    (CA2_4_10I1R11P a).Encloses (CA2_4_10I1R11Value a) :=
  contains_sound (CA2_4_10I1R11Raw_sound a) (CA2_4_10I1R11P_check a)
def CA2_4_10I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R11Certificates (CA2_4_10I1R11CertificateIndex a)).output
lemma CA2_4_10I1R11Terms_sound (a : PairSlot) :
    (CA2_4_10I1R11Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R11Certificates_valid
    (CA2_4_10I1R11CertificateIndex a) (CA2_4_10I1R11P_sound a)
def CA2_4_10I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R11Entropy_sound : CA2_4_10I1R11Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R11Value CA2_4_10I1R11Terms CA2_4_10I1R11Terms_sound) (by decide +kernel)
def CA2_4_10I1R11Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R11Mass_sound : CA2_4_10I1R11Mass.Encloses (∑ a, CA2_4_10I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R11P CA2_4_10I1R11Value CA2_4_10I1R11P_sound) (by decide +kernel)
def CA2_4_10I1R11MassTerm : Ball := .exact 0
lemma CA2_4_10I1R11MassTerm_sound : CA2_4_10I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R11Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R11Mass_sound)
def CA2_4_10I1R11H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R11H_sound : CA2_4_10I1R11H.Encloses (homogeneousEntropy CA2_4_10I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R11Value CA2_4_10I1R11MassTerm_sound CA2_4_10I1R11Entropy_sound) (by decide +kernel)
def CA2_4_10I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA2_4_10I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA2_4_10I1R12Raw_sound (a : PairSlot) :
    (CA2_4_10I1R12Raw a).Encloses (CA2_4_10I1R12Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA2_4_10I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R12Certificates_valid :
    CA2_4_10I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R12Certificates (CA2_4_10I1R12CertificateIndex a)).input
lemma CA2_4_10I1R12P_check : ∀ a : PairSlot, contains (CA2_4_10I1R12Raw a) (CA2_4_10I1R12P a) = true := by
  decide +kernel
lemma CA2_4_10I1R12P_sound (a : PairSlot) :
    (CA2_4_10I1R12P a).Encloses (CA2_4_10I1R12Value a) :=
  contains_sound (CA2_4_10I1R12Raw_sound a) (CA2_4_10I1R12P_check a)
def CA2_4_10I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R12Certificates (CA2_4_10I1R12CertificateIndex a)).output
lemma CA2_4_10I1R12Terms_sound (a : PairSlot) :
    (CA2_4_10I1R12Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R12Certificates_valid
    (CA2_4_10I1R12CertificateIndex a) (CA2_4_10I1R12P_sound a)
def CA2_4_10I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R12Entropy_sound : CA2_4_10I1R12Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R12Value CA2_4_10I1R12Terms CA2_4_10I1R12Terms_sound) (by decide +kernel)
def CA2_4_10I1R12Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R12Mass_sound : CA2_4_10I1R12Mass.Encloses (∑ a, CA2_4_10I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R12P CA2_4_10I1R12Value CA2_4_10I1R12P_sound) (by decide +kernel)
def CA2_4_10I1R12MassTerm : Ball := .exact 0
lemma CA2_4_10I1R12MassTerm_sound : CA2_4_10I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R12Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R12Mass_sound)
def CA2_4_10I1R12H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R12H_sound : CA2_4_10I1R12H.Encloses (homogeneousEntropy CA2_4_10I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R12Value CA2_4_10I1R12MassTerm_sound CA2_4_10I1R12Entropy_sound) (by decide +kernel)
def CA2_4_10I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA2_4_10I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA2_4_10I1R13Raw_sound (a : PairSlot) :
    (CA2_4_10I1R13Raw a).Encloses (CA2_4_10I1R13Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA2_4_10I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R13Certificates_valid :
    CA2_4_10I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R13Certificates (CA2_4_10I1R13CertificateIndex a)).input
lemma CA2_4_10I1R13P_check : ∀ a : PairSlot, contains (CA2_4_10I1R13Raw a) (CA2_4_10I1R13P a) = true := by
  decide +kernel
lemma CA2_4_10I1R13P_sound (a : PairSlot) :
    (CA2_4_10I1R13P a).Encloses (CA2_4_10I1R13Value a) :=
  contains_sound (CA2_4_10I1R13Raw_sound a) (CA2_4_10I1R13P_check a)
def CA2_4_10I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R13Certificates (CA2_4_10I1R13CertificateIndex a)).output
lemma CA2_4_10I1R13Terms_sound (a : PairSlot) :
    (CA2_4_10I1R13Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R13Certificates_valid
    (CA2_4_10I1R13CertificateIndex a) (CA2_4_10I1R13P_sound a)
def CA2_4_10I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R13Entropy_sound : CA2_4_10I1R13Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R13Value CA2_4_10I1R13Terms CA2_4_10I1R13Terms_sound) (by decide +kernel)
def CA2_4_10I1R13Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R13Mass_sound : CA2_4_10I1R13Mass.Encloses (∑ a, CA2_4_10I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R13P CA2_4_10I1R13Value CA2_4_10I1R13P_sound) (by decide +kernel)
def CA2_4_10I1R13MassTerm : Ball := .exact 0
lemma CA2_4_10I1R13MassTerm_sound : CA2_4_10I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R13Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R13Mass_sound)
def CA2_4_10I1R13H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R13H_sound : CA2_4_10I1R13H.Encloses (homogeneousEntropy CA2_4_10I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R13Value CA2_4_10I1R13MassTerm_sound CA2_4_10I1R13Entropy_sound) (by decide +kernel)
def CA2_4_10I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA2_4_10I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA2_4_10I1R14Raw_sound (a : PairSlot) :
    (CA2_4_10I1R14Raw a).Encloses (CA2_4_10I1R14Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA2_4_10I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R14Certificates_valid :
    CA2_4_10I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R14Certificates (CA2_4_10I1R14CertificateIndex a)).input
lemma CA2_4_10I1R14P_check : ∀ a : PairSlot, contains (CA2_4_10I1R14Raw a) (CA2_4_10I1R14P a) = true := by
  decide +kernel
lemma CA2_4_10I1R14P_sound (a : PairSlot) :
    (CA2_4_10I1R14P a).Encloses (CA2_4_10I1R14Value a) :=
  contains_sound (CA2_4_10I1R14Raw_sound a) (CA2_4_10I1R14P_check a)
def CA2_4_10I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R14Certificates (CA2_4_10I1R14CertificateIndex a)).output
lemma CA2_4_10I1R14Terms_sound (a : PairSlot) :
    (CA2_4_10I1R14Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R14Certificates_valid
    (CA2_4_10I1R14CertificateIndex a) (CA2_4_10I1R14P_sound a)
def CA2_4_10I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R14Entropy_sound : CA2_4_10I1R14Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R14Value CA2_4_10I1R14Terms CA2_4_10I1R14Terms_sound) (by decide +kernel)
def CA2_4_10I1R14Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R14Mass_sound : CA2_4_10I1R14Mass.Encloses (∑ a, CA2_4_10I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R14P CA2_4_10I1R14Value CA2_4_10I1R14P_sound) (by decide +kernel)
def CA2_4_10I1R14MassTerm : Ball := .exact 0
lemma CA2_4_10I1R14MassTerm_sound : CA2_4_10I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R14Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R14Mass_sound)
def CA2_4_10I1R14H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R14H_sound : CA2_4_10I1R14H.Encloses (homogeneousEntropy CA2_4_10I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R14Value CA2_4_10I1R14MassTerm_sound CA2_4_10I1R14Entropy_sound) (by decide +kernel)
def CA2_4_10I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA2_4_10I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA2_4_10I1R15Raw_sound (a : PairSlot) :
    (CA2_4_10I1R15Raw a).Encloses (CA2_4_10I1R15Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA2_4_10I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R15Certificates_valid :
    CA2_4_10I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R15Certificates (CA2_4_10I1R15CertificateIndex a)).input
lemma CA2_4_10I1R15P_check : ∀ a : PairSlot, contains (CA2_4_10I1R15Raw a) (CA2_4_10I1R15P a) = true := by
  decide +kernel
lemma CA2_4_10I1R15P_sound (a : PairSlot) :
    (CA2_4_10I1R15P a).Encloses (CA2_4_10I1R15Value a) :=
  contains_sound (CA2_4_10I1R15Raw_sound a) (CA2_4_10I1R15P_check a)
def CA2_4_10I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R15Certificates (CA2_4_10I1R15CertificateIndex a)).output
lemma CA2_4_10I1R15Terms_sound (a : PairSlot) :
    (CA2_4_10I1R15Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R15Certificates_valid
    (CA2_4_10I1R15CertificateIndex a) (CA2_4_10I1R15P_sound a)
def CA2_4_10I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R15Entropy_sound : CA2_4_10I1R15Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R15Value CA2_4_10I1R15Terms CA2_4_10I1R15Terms_sound) (by decide +kernel)
def CA2_4_10I1R15Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R15Mass_sound : CA2_4_10I1R15Mass.Encloses (∑ a, CA2_4_10I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R15P CA2_4_10I1R15Value CA2_4_10I1R15P_sound) (by decide +kernel)
def CA2_4_10I1R15MassTerm : Ball := .exact 0
lemma CA2_4_10I1R15MassTerm_sound : CA2_4_10I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R15Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R15Mass_sound)
def CA2_4_10I1R15H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R15H_sound : CA2_4_10I1R15H.Encloses (homogeneousEntropy CA2_4_10I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R15Value CA2_4_10I1R15MassTerm_sound CA2_4_10I1R15Entropy_sound) (by decide +kernel)
def CA2_4_10I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA2_4_10I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA2_4_10I1R16Raw_sound (a : PairSlot) :
    (CA2_4_10I1R16Raw a).Encloses (CA2_4_10I1R16Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA2_4_10I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I1R16Certificates_valid :
    CA2_4_10I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R16Certificates (CA2_4_10I1R16CertificateIndex a)).input
lemma CA2_4_10I1R16P_check : ∀ a : PairSlot, contains (CA2_4_10I1R16Raw a) (CA2_4_10I1R16P a) = true := by
  decide +kernel
lemma CA2_4_10I1R16P_sound (a : PairSlot) :
    (CA2_4_10I1R16P a).Encloses (CA2_4_10I1R16Value a) :=
  contains_sound (CA2_4_10I1R16Raw_sound a) (CA2_4_10I1R16P_check a)
def CA2_4_10I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I1R16Certificates (CA2_4_10I1R16CertificateIndex a)).output
lemma CA2_4_10I1R16Terms_sound (a : PairSlot) :
    (CA2_4_10I1R16Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I1R16Certificates_valid
    (CA2_4_10I1R16CertificateIndex a) (CA2_4_10I1R16P_sound a)
def CA2_4_10I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R16Entropy_sound : CA2_4_10I1R16Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I1R16Value CA2_4_10I1R16Terms CA2_4_10I1R16Terms_sound) (by decide +kernel)
def CA2_4_10I1R16Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R16Mass_sound : CA2_4_10I1R16Mass.Encloses (∑ a, CA2_4_10I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I1R16P CA2_4_10I1R16Value CA2_4_10I1R16P_sound) (by decide +kernel)
def CA2_4_10I1R16MassTerm : Ball := .exact 0
lemma CA2_4_10I1R16MassTerm_sound : CA2_4_10I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I1R16Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I1R16Mass_sound)
def CA2_4_10I1R16H : Ball := ⟨0, 0⟩
lemma CA2_4_10I1R16H_sound : CA2_4_10I1R16H.Encloses (homogeneousEntropy CA2_4_10I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I1R16Value CA2_4_10I1R16MassTerm_sound CA2_4_10I1R16Entropy_sound) (by decide +kernel)
def CA2_4_10I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_4_10I1R0H
  | 1 => CA2_4_10I1R1H
  | 2 => CA2_4_10I1R2H
  | 3 => CA2_4_10I1R3H
  | 4 => CA2_4_10I1R4H
  | 5 => CA2_4_10I1R5H
  | 6 => CA2_4_10I1R6H
  | 7 => CA2_4_10I1R7H
  | 8 => CA2_4_10I1R8H
  | 9 => CA2_4_10I1R9H
  | 10 => CA2_4_10I1R10H
  | 11 => CA2_4_10I1R11H
  | 12 => CA2_4_10I1R12H
  | 13 => CA2_4_10I1R13H
  | 14 => CA2_4_10I1R14H
  | 15 => CA2_4_10I1R15H
  | 16 => CA2_4_10I1R16H
  | _ => (.exact 0)
lemma CA2_4_10I1ResidualEntropies_sound (k : Fin 17) :
    (CA2_4_10I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_4_10I1R0H_sound
  · exact CA2_4_10I1R1H_sound
  · exact CA2_4_10I1R2H_sound
  · exact CA2_4_10I1R3H_sound
  · exact CA2_4_10I1R4H_sound
  · exact CA2_4_10I1R5H_sound
  · exact CA2_4_10I1R6H_sound
  · exact CA2_4_10I1R7H_sound
  · exact CA2_4_10I1R8H_sound
  · exact CA2_4_10I1R9H_sound
  · exact CA2_4_10I1R10H_sound
  · exact CA2_4_10I1R11H_sound
  · exact CA2_4_10I1R12H_sound
  · exact CA2_4_10I1R13H_sound
  · exact CA2_4_10I1R14H_sound
  · exact CA2_4_10I1R15H_sound
  · exact CA2_4_10I1R16H_sound
def CA2_4_10I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
lemma CA2_4_10I1Singles_sound (u : Shape) (hu : u ∈ below (shape 2 4 10))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA2_4_10I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A2_4_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 0 8) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 1 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 4 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 0 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 0 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 4 2) by decide +kernel) hd |>.elim
def CA2_4_10I1Singleton : Ball := ⟨0, 0⟩
lemma CA2_4_10I1Singleton_sound : CA2_4_10I1Singleton.Encloses
    (singletonEntropy (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA2_4_10I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_4_10Law_sound u) CA2_4_10I1Singles_sound) (by decide +kernel)
def CA2_4_10I1Group : Ball := ⟨(19258557836174867804781857094959 / 20000000000000000000000000000000), (22067510623 / 12500000000000000000000000000000)⟩
lemma CA2_4_10I1Group_sound : CA2_4_10I1Group.Encloses
    (groupedEntropy (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_4_10I1Singleton_sound
    (finSumBall_sound 17 CA2_4_10I1ResidualEntropies _ CA2_4_10I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA2_4_10I1H : Ball := ⟨(121272854904680328155082525730649 / 100000000000000000000000000000000), (526079246751 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I1_sound : CA2_4_10I1H.Encloses (stageACapacity (shape 2 4 10) 1) := by
  have hb := contains_sound (Ball.add_sound CA2_4_10I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA2_4_10I1Group_sound)))
    (show contains (.add CA2_4_10I1PairH (.neg (.mul (.exact 2) CA2_4_10I1Group))) CA2_4_10I1H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg]
  exact hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
