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
def CA3_4_9I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 3 4 9)) (shape 3 4 9) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA3_4_9I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 3 4 9) A3_4_9Law 1 a
lemma CA3_4_9I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA3_4_9I1PairRaw a).Encloses (CA3_4_9I1PairValue a) := by
  exact stageAPairBall_sound (shape 3 4 9) (by decide +kernel) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (fun u _ => A3_4_9Law_sound u) 1 a
def CA3_4_9I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(292857264085756312241011408043 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1708306744624285742802727879751 / 100000000000000000000000000000000), (3100747 / 500000000000000000000000000000)⟩ ⟨(-72915501599272631539291127246699 / 12500000000000000000000000000000), (105879118927 / 50000000000000000000000000000000)⟩ ⟨-9, 292857264085756312241011408043, 195312500000000000000000000000⟩,
   .log ⟨(1885575878487842349807621027 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1920561796943324412147676313 / 5000000000000000000000000000000), (12777171 / 100000000000000000000000000000000)⟩ ⟨(-254638625108465456202777856275343 / 25000000000000000000000000000000), (84703301361 / 25000000000000000000000000000000)⟩ ⟨-15, 1885575878487842349807621027, 1525878906250000000000000000⟩,
   .log ⟨(841509810611295391142428923819 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(6874429315078938315221032438319 / 100000000000000000000000000000000), (498950587 / 20000000000000000000000000000000)⟩ ⟨(-3191078603411668648692810823379 / 781250000000000000000000000000), (148230766493 / 100000000000000000000000000000000)⟩ ⟨-6, 841509810611295391142428923819, 781250000000000000000000000000⟩,
   .log ⟨(14706810017409610410934150259 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(239795630012192420696149077293 / 25000000000000000000000000000000), (342571713 / 100000000000000000000000000000000)⟩ ⟨(-652202971897583308566276690454327 / 100000000000000000000000000000000), (14558378867 / 6250000000000000000000000000000)⟩ ⟨-10, 14706810017409610410934150259, 9765625000000000000000000000⟩,
   .log ⟨(6512532435152937635412385023 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(58261440120041247146646050737 / 50000000000000000000000000000000), (19307159 / 50000000000000000000000000000000)⟩ ⟨(-894604989689745160234788813902721 / 100000000000000000000000000000000), (296461539239 / 100000000000000000000000000000000)⟩ ⟨-13, 6512532435152937635412385023, 6103515625000000000000000000⟩,
   .log ⟨(2551518495124812919643556648547 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩ ⟨(94895257318236553266192335441 / 625000000000000000000000000000), (6483660793 / 100000000000000000000000000000000)⟩ ⟨(-148766716760318135495281997652377 / 50000000000000000000000000000000), (31763735647 / 25000000000000000000000000000000)⟩ ⟨-5, 2551518495124812919643556648547, 1562500000000000000000000000000⟩,
   .log ⟨(477235717337443166844245563137 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2550784310638338466641438747857 / 100000000000000000000000000000000), (454763683 / 50000000000000000000000000000000)⟩ ⟨(-534491492981597906304914361761911 / 100000000000000000000000000000000), (7623296551 / 4000000000000000000000000000000)⟩ ⟨-8, 477235717337443166844245563137, 390625000000000000000000000000⟩,
   .log ⟨(197401741563142660985948151703 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1229355769265801328866234541451 / 100000000000000000000000000000000), (418014463 / 100000000000000000000000000000000)⟩ ⟨(-155692112887536095619562721419211 / 25000000000000000000000000000000), (105879118921 / 50000000000000000000000000000000)⟩ ⟨-9, 197401741563142660985948151703, 195312500000000000000000000000⟩,
   .log ⟨(32123053480794354222066256883 / 625000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩ ⟨(7627754480821433172880193405681 / 50000000000000000000000000000000), (1632557107 / 25000000000000000000000000000000)⟩ ⟨(-59363554007886382395582449412141 / 20000000000000000000000000000000), (127054942623 / 100000000000000000000000000000000)⟩ ⟨-5, 32123053480794354222066256883, 19531250000000000000000000000⟩,
   .log ⟨(68297117279496336545355678441 / 5000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(5864435284800964772208620123351 / 100000000000000000000000000000000), (462799279 / 20000000000000000000000000000000)⟩ ⟨(-429332563247258962245902814892459 / 100000000000000000000000000000000), (42351647549 / 25000000000000000000000000000000)⟩ ⟨-7, 68297117279496336545355678441, 39062500000000000000000000000⟩,
   .log ⟨(6868278761850895068649910837 / 5000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(905277556564862264997319906539 / 100000000000000000000000000000000), (79992807 / 25000000000000000000000000000000)⟩ ⟨(-82378495758748872339109756633499 / 12500000000000000000000000000000), (14558378873 / 6250000000000000000000000000000)⟩ ⟨-10, 6868278761850895068649910837, 4882812500000000000000000000⟩,
   .log ⟨(51942877695133887313949975319 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1366148525864748611102187376993 / 50000000000000000000000000000000), (989939923 / 100000000000000000000000000000000)⟩ ⟨(-526019576305735613015829243946971 / 100000000000000000000000000000000), (47645603479 / 25000000000000000000000000000000)⟩ ⟨-8, 51942877695133887313949975319, 39062500000000000000000000000⟩,
   .log ⟨(13932265331896540711495502853 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(123700655928616729544354072211 / 100000000000000000000000000000000), (20651909 / 50000000000000000000000000000000)⟩ ⟨(-443935903393313710537678197278661 / 50000000000000000000000000000000), (296461538739 / 100000000000000000000000000000000)⟩ ⟨-13, 13932265331896540711495502853, 12207031250000000000000000000⟩,
   .log ⟨(9678418294724011225805740309959 / 50000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩ ⟨(15893167965574704805083629831923 / 50000000000000000000000000000000), (1024742407 / 6250000000000000000000000000000)⟩ ⟨(-82106225839807602248031070671817 / 50000000000000000000000000000000), (21175823763 / 25000000000000000000000000000000)⟩ ⟨-3, 9678418294724011225805740309959, 6250000000000000000000000000000⟩]
lemma CA3_4_9I1PairCertificates_valid :
    CA3_4_9I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 4, 1 => 1
  | 0, 0, 5, 0 => 2
  | 0, 0, 2, 2 => 3
  | 0, 0, 2, 3 => 4
  | 0, 0, 3, 2 => 4
  | 0, 0, 3, 3 => 5
  | 0, 0, 1, 4 => 1
  | 0, 0, 0, 5 => 2
  | 1, 0, 2, 1 => 6
  | 1, 0, 3, 1 => 7
  | 1, 0, 4, 0 => 8
  | 1, 0, 1, 2 => 6
  | 1, 0, 1, 3 => 7
  | 1, 0, 0, 4 => 8
  | 0, 1, 2, 1 => 6
  | 0, 1, 3, 1 => 7
  | 0, 1, 4, 0 => 8
  | 0, 1, 1, 2 => 6
  | 0, 1, 1, 3 => 7
  | 0, 1, 0, 4 => 8
  | 2, 0, 1, 1 => 9
  | 2, 0, 2, 0 => 10
  | 2, 0, 3, 0 => 11
  | 2, 0, 0, 2 => 10
  | 2, 0, 0, 3 => 11
  | 3, 0, 1, 1 => 12
  | 3, 0, 2, 0 => 11
  | 3, 0, 3, 0 => 13
  | 3, 0, 0, 2 => 11
  | 3, 0, 0, 3 => 13
  | 1, 1, 1, 1 => 14
  | 1, 1, 2, 0 => 9
  | 1, 1, 3, 0 => 12
  | 1, 1, 0, 2 => 9
  | 1, 1, 0, 3 => 12
  | 0, 2, 1, 1 => 9
  | 0, 2, 2, 0 => 10
  | 0, 2, 3, 0 => 11
  | 0, 2, 0, 2 => 10
  | 0, 2, 0, 3 => 11
  | 0, 3, 1, 1 => 12
  | 0, 3, 2, 0 => 11
  | 0, 3, 3, 0 => 13
  | 0, 3, 0, 2 => 11
  | 0, 3, 0, 3 => 13
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
  | 0, 5, 0, 0 => 2
  | 1, 4, 0, 0 => 1
  | 2, 2, 0, 0 => 3
  | 2, 3, 0, 0 => 4
  | 3, 2, 0, 0 => 4
  | 3, 3, 0, 0 => 5
  | 4, 1, 0, 0 => 1
  | 5, 0, 0, 0 => 2
  | _, _, _, _ => 0
def CA3_4_9I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1PairCertificates (CA3_4_9I1PairCertificateIndex a)).input
lemma CA3_4_9I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((0,0),(k,l))) (CA3_4_9I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((0,1),(k,l))) (CA3_4_9I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((0,2),(k,l))) (CA3_4_9I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((0,3),(k,l))) (CA3_4_9I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((0,4),(k,l))) (CA3_4_9I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((0,5),(k,l))) (CA3_4_9I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((1,0),(k,l))) (CA3_4_9I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((1,1),(k,l))) (CA3_4_9I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((1,2),(k,l))) (CA3_4_9I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((1,3),(k,l))) (CA3_4_9I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((1,4),(k,l))) (CA3_4_9I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((1,5),(k,l))) (CA3_4_9I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((2,0),(k,l))) (CA3_4_9I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((2,1),(k,l))) (CA3_4_9I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((2,2),(k,l))) (CA3_4_9I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((2,3),(k,l))) (CA3_4_9I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((2,4),(k,l))) (CA3_4_9I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((2,5),(k,l))) (CA3_4_9I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((3,0),(k,l))) (CA3_4_9I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((3,1),(k,l))) (CA3_4_9I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((3,2),(k,l))) (CA3_4_9I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((3,3),(k,l))) (CA3_4_9I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((3,4),(k,l))) (CA3_4_9I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((3,5),(k,l))) (CA3_4_9I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((4,0),(k,l))) (CA3_4_9I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((4,1),(k,l))) (CA3_4_9I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((4,2),(k,l))) (CA3_4_9I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((4,3),(k,l))) (CA3_4_9I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((4,4),(k,l))) (CA3_4_9I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((4,5),(k,l))) (CA3_4_9I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((5,0),(k,l))) (CA3_4_9I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((5,1),(k,l))) (CA3_4_9I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((5,2),(k,l))) (CA3_4_9I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((5,3),(k,l))) (CA3_4_9I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((5,4),(k,l))) (CA3_4_9I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA3_4_9I1PairRaw ((5,5),(k,l))) (CA3_4_9I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA3_4_9I1PairP_check (a : PairSlot × PairSlot) : contains (CA3_4_9I1PairRaw a) (CA3_4_9I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA3_4_9I1PairP_check_0_0 k l) (CA3_4_9I1PairP_check_0_1 k l) (CA3_4_9I1PairP_check_0_2 k l) (CA3_4_9I1PairP_check_0_3 k l) (CA3_4_9I1PairP_check_0_4 k l) (CA3_4_9I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA3_4_9I1PairP_check_1_0 k l) (CA3_4_9I1PairP_check_1_1 k l) (CA3_4_9I1PairP_check_1_2 k l) (CA3_4_9I1PairP_check_1_3 k l) (CA3_4_9I1PairP_check_1_4 k l) (CA3_4_9I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA3_4_9I1PairP_check_2_0 k l) (CA3_4_9I1PairP_check_2_1 k l) (CA3_4_9I1PairP_check_2_2 k l) (CA3_4_9I1PairP_check_2_3 k l) (CA3_4_9I1PairP_check_2_4 k l) (CA3_4_9I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA3_4_9I1PairP_check_3_0 k l) (CA3_4_9I1PairP_check_3_1 k l) (CA3_4_9I1PairP_check_3_2 k l) (CA3_4_9I1PairP_check_3_3 k l) (CA3_4_9I1PairP_check_3_4 k l) (CA3_4_9I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA3_4_9I1PairP_check_4_0 k l) (CA3_4_9I1PairP_check_4_1 k l) (CA3_4_9I1PairP_check_4_2 k l) (CA3_4_9I1PairP_check_4_3 k l) (CA3_4_9I1PairP_check_4_4 k l) (CA3_4_9I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA3_4_9I1PairP_check_5_0 k l) (CA3_4_9I1PairP_check_5_1 k l) (CA3_4_9I1PairP_check_5_2 k l) (CA3_4_9I1PairP_check_5_3 k l) (CA3_4_9I1PairP_check_5_4 k l) (CA3_4_9I1PairP_check_5_5 k l)
lemma CA3_4_9I1PairP_sound (a : PairSlot × PairSlot) :
    (CA3_4_9I1PairP a).Encloses (CA3_4_9I1PairValue a) :=
  contains_sound (CA3_4_9I1PairRaw_sound a) (CA3_4_9I1PairP_check a)
def CA3_4_9I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1PairCertificates (CA3_4_9I1PairCertificateIndex a)).output
lemma CA3_4_9I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA3_4_9I1PairTerms a).Encloses (Foundation.entropyTerm (CA3_4_9I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1PairCertificates_valid
    (CA3_4_9I1PairCertificateIndex a) (CA3_4_9I1PairP_sound a)
def CA3_4_9I1PairEntropy : Ball := ⟨(15572244029986886191407704878953 / 5000000000000000000000000000000), (12991587121 / 10000000000000000000000000000000)⟩
lemma CA3_4_9I1PairEntropy_sound : CA3_4_9I1PairEntropy.Encloses (Foundation.finiteEntropy CA3_4_9I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA3_4_9I1PairValue CA3_4_9I1PairTerms CA3_4_9I1PairTerms_sound) (by decide +kernel)
def CA3_4_9I1PairMass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (67 / 12500000000000000000000000000000)⟩
lemma CA3_4_9I1PairMass_sound : CA3_4_9I1PairMass.Encloses (∑ a, CA3_4_9I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA3_4_9I1PairP CA3_4_9I1PairValue CA3_4_9I1PairP_sound) (by decide +kernel)
def CA3_4_9I1PairMassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA3_4_9I1PairMassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (21175823951 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I1PairMassTermLog_sound : CA3_4_9I1PairMassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I1PairMass_sound) (w := CA3_4_9I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I1PairMassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (42351647903 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1PairMassTerm_sound : CA3_4_9I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I1PairMass_sound) CA3_4_9I1PairMassTermLog_sound) (by decide +kernel)
def CA3_4_9I1PairH : Ball := ⟨(311444880599737723828154097579059 / 100000000000000000000000000000000), (172267519113 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1PairH_sound : CA3_4_9I1PairH.Encloses (homogeneousEntropy CA3_4_9I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1PairValue CA3_4_9I1PairMassTerm_sound CA3_4_9I1PairEntropy_sound) (by decide +kernel)

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
def CA3_4_9I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA3_4_9I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA3_4_9I1R0Raw_sound (a : PairSlot) :
    (CA3_4_9I1R0Raw a).Encloses (CA3_4_9I1R0Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA3_4_9I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(129171885906327642982780946153 / 5000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(9445175467426299895193937865993 / 100000000000000000000000000000000), (3829449579 / 100000000000000000000000000000000)⟩ ⟨(-45700615313631960038590227361989 / 12500000000000000000000000000000), (148230766323 / 100000000000000000000000000000000)⟩ ⟨-6, 129171885906327642982780946153, 78125000000000000000000000000⟩]
lemma CA3_4_9I1R0Certificates_valid :
    CA3_4_9I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA3_4_9I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R0Certificates (CA3_4_9I1R0CertificateIndex a)).input
lemma CA3_4_9I1R0P_check : ∀ a : PairSlot, contains (CA3_4_9I1R0Raw a) (CA3_4_9I1R0P a) = true := by
  decide +kernel
lemma CA3_4_9I1R0P_sound (a : PairSlot) :
    (CA3_4_9I1R0P a).Encloses (CA3_4_9I1R0Value a) :=
  contains_sound (CA3_4_9I1R0Raw_sound a) (CA3_4_9I1R0P_check a)
def CA3_4_9I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R0Certificates (CA3_4_9I1R0CertificateIndex a)).output
lemma CA3_4_9I1R0Terms_sound (a : PairSlot) :
    (CA3_4_9I1R0Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R0Certificates_valid
    (CA3_4_9I1R0CertificateIndex a) (CA3_4_9I1R0P_sound a)
def CA3_4_9I1R0Entropy : Ball := ⟨(9445175467426299895193937865993 / 100000000000000000000000000000000), (3829449579 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1R0Entropy_sound : CA3_4_9I1R0Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R0Value CA3_4_9I1R0Terms CA3_4_9I1R0Terms_sound) (by decide +kernel)
def CA3_4_9I1R0Mass : Ball := ⟨(129171885906327642982780946153 / 5000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I1R0Mass_sound : CA3_4_9I1R0Mass.Encloses (∑ a, CA3_4_9I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R0P CA3_4_9I1R0Value CA3_4_9I1R0P_sound) (by decide +kernel)
def CA3_4_9I1R0MassTermLogWitness : LogWitness := ⟨-6, 129171885906327642982780946153, 78125000000000000000000000000⟩
def CA3_4_9I1R0MassTermLog : Ball := ⟨(-45700615313631960038590227361989 / 12500000000000000000000000000000), (148230766323 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1R0MassTermLog_sound : CA3_4_9I1R0MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I1R0Mass_sound) (w := CA3_4_9I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I1R0MassTerm : Ball := ⟨(9445175467426299895193937865993 / 100000000000000000000000000000000), (3829449579 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1R0MassTerm_sound : CA3_4_9I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I1R0Mass_sound) CA3_4_9I1R0MassTermLog_sound) (by decide +kernel)
def CA3_4_9I1R0H : Ball := ⟨0, (3829449579 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I1R0H_sound : CA3_4_9I1R0H.Encloses (homogeneousEntropy CA3_4_9I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R0Value CA3_4_9I1R0MassTerm_sound CA3_4_9I1R0Entropy_sound) (by decide +kernel)
def CA3_4_9I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA3_4_9I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA3_4_9I1R1Raw_sound (a : PairSlot) :
    (CA3_4_9I1R1Raw a).Encloses (CA3_4_9I1R1Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA3_4_9I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(11555348898300423334234614023867 / 100000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩ ⟨(24936694229921582604765072396319 / 100000000000000000000000000000000), (12234701683 / 100000000000000000000000000000000)⟩ ⟨(-215802174814378006466983161722997 / 100000000000000000000000000000000), (26469779699 / 25000000000000000000000000000000)⟩ ⟨-4, 11555348898300423334234614023867, 6250000000000000000000000000000⟩]
lemma CA3_4_9I1R1Certificates_valid :
    CA3_4_9I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA3_4_9I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R1Certificates (CA3_4_9I1R1CertificateIndex a)).input
lemma CA3_4_9I1R1P_check : ∀ a : PairSlot, contains (CA3_4_9I1R1Raw a) (CA3_4_9I1R1P a) = true := by
  decide +kernel
lemma CA3_4_9I1R1P_sound (a : PairSlot) :
    (CA3_4_9I1R1P a).Encloses (CA3_4_9I1R1Value a) :=
  contains_sound (CA3_4_9I1R1Raw_sound a) (CA3_4_9I1R1P_check a)
def CA3_4_9I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R1Certificates (CA3_4_9I1R1CertificateIndex a)).output
lemma CA3_4_9I1R1Terms_sound (a : PairSlot) :
    (CA3_4_9I1R1Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R1Certificates_valid
    (CA3_4_9I1R1CertificateIndex a) (CA3_4_9I1R1P_sound a)
def CA3_4_9I1R1Entropy : Ball := ⟨(24936694229921582604765072396319 / 50000000000000000000000000000000), (12234701683 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I1R1Entropy_sound : CA3_4_9I1R1Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R1Value CA3_4_9I1R1Terms CA3_4_9I1R1Terms_sound) (by decide +kernel)
def CA3_4_9I1R1Mass : Ball := ⟨(11555348898300423334234614023867 / 50000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
lemma CA3_4_9I1R1Mass_sound : CA3_4_9I1R1Mass.Encloses (∑ a, CA3_4_9I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R1P CA3_4_9I1R1Value CA3_4_9I1R1P_sound) (by decide +kernel)
def CA3_4_9I1R1MassTermLogWitness : LogWitness := ⟨-3, 11555348898300423334234614023867, 6250000000000000000000000000000⟩
def CA3_4_9I1R1MassTermLog : Ball := ⟨(-146487456758383475525259968672667 / 100000000000000000000000000000000), (84703295113 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1R1MassTermLog_sound : CA3_4_9I1R1MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I1R1Mass_sound) (w := CA3_4_9I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I1R1MassTerm : Ball := ⟨(33854273441356347927102503160183 / 100000000000000000000000000000000), (19575522687 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1R1MassTerm_sound : CA3_4_9I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I1R1Mass_sound) CA3_4_9I1R1MassTermLog_sound) (by decide +kernel)
def CA3_4_9I1R1H : Ball := ⟨(3203823003697363456485528326491 / 20000000000000000000000000000000), (44044926053 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1R1H_sound : CA3_4_9I1R1H.Encloses (homogeneousEntropy CA3_4_9I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R1Value CA3_4_9I1R1MassTerm_sound CA3_4_9I1R1Entropy_sound) (by decide +kernel)
def CA3_4_9I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA3_4_9I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA3_4_9I1R2Raw_sound (a : PairSlot) :
    (CA3_4_9I1R2Raw a).Encloses (CA3_4_9I1R2Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA3_4_9I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(20365760996452464850227061681 / 250000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩ ⟨(1021386011832927298843292887369 / 5000000000000000000000000000000), (2156308851 / 25000000000000000000000000000000)⟩ ⟨(-25076058096008386179872407245093 / 10000000000000000000000000000000), (26469779711 / 25000000000000000000000000000000)⟩ ⟨-4, 20365760996452464850227061681, 15625000000000000000000000000⟩,
   .log ⟨(822024458089167757308487192377 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(3946667096828867111605776669259 / 100000000000000000000000000000000), (1392563623 / 100000000000000000000000000000000)⟩ ⟨(-240057765799515837495263368876237 / 50000000000000000000000000000000), (3388131799 / 2000000000000000000000000000000)⟩ ⟨-7, 822024458089167757308487192377, 781250000000000000000000000000⟩,
   .log ⟨(30675071257204893548951682328859 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩ ⟨(36249341292555436934643008586237 / 100000000000000000000000000000000), (1217943573 / 6250000000000000000000000000000)⟩ ⟨(-118171987242054966862292732949783 / 100000000000000000000000000000000), (794093391 / 1250000000000000000000000000000)⟩ ⟨-2, 30675071257204893548951682328859, 25000000000000000000000000000000⟩]
lemma CA3_4_9I1R2Certificates_valid :
    CA3_4_9I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA3_4_9I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R2Certificates (CA3_4_9I1R2CertificateIndex a)).input
lemma CA3_4_9I1R2P_check : ∀ a : PairSlot, contains (CA3_4_9I1R2Raw a) (CA3_4_9I1R2P a) = true := by
  decide +kernel
lemma CA3_4_9I1R2P_sound (a : PairSlot) :
    (CA3_4_9I1R2P a).Encloses (CA3_4_9I1R2Value a) :=
  contains_sound (CA3_4_9I1R2Raw_sound a) (CA3_4_9I1R2P_check a)
def CA3_4_9I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R2Certificates (CA3_4_9I1R2CertificateIndex a)).output
lemma CA3_4_9I1R2Terms_sound (a : PairSlot) :
    (CA3_4_9I1R2Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R2Certificates_valid
    (CA3_4_9I1R2CertificateIndex a) (CA3_4_9I1R2P_sound a)
def CA3_4_9I1R2Entropy : Ball := ⟨(16999623191906052622317255483903 / 20000000000000000000000000000000), (19761347611 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I1R2Entropy_sound : CA3_4_9I1R2Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R2Value CA3_4_9I1R2Terms CA3_4_9I1R2Terms_sound) (by decide +kernel)
def CA3_4_9I1R2Mass : Ball := ⟨(48611728970545200943750306058413 / 100000000000000000000000000000000), (149 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1R2Mass_sound : CA3_4_9I1R2Mass.Encloses (∑ a, CA3_4_9I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R2P CA3_4_9I1R2Value CA3_4_9I1R2P_sound) (by decide +kernel)
def CA3_4_9I1R2MassTermLogWitness : LogWitness := ⟨-2, 48611728970545200943750306058413, 25000000000000000000000000000000⟩
def CA3_4_9I1R2MassTermLog : Ball := ⟨(-14426106947124012552068567061067 / 20000000000000000000000000000000), (12705494271 / 20000000000000000000000000000000)⟩
lemma CA3_4_9I1R2MassTermLog_sound : CA3_4_9I1R2MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I1R2Mass_sound) (w := CA3_4_9I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I1R2MassTerm : Ball := ⟨(35063900050684587314112502652597 / 100000000000000000000000000000000), (6176360461 / 20000000000000000000000000000000)⟩
lemma CA3_4_9I1R2MassTerm_sound : CA3_4_9I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I1R2Mass_sound) CA3_4_9I1R2MassTermLog_sound) (by decide +kernel)
def CA3_4_9I1R2H : Ball := ⟨(24967107954422837898736887383459 / 50000000000000000000000000000000), (70404497527 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1R2H_sound : CA3_4_9I1R2H.Encloses (homogeneousEntropy CA3_4_9I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R2Value CA3_4_9I1R2MassTerm_sound CA3_4_9I1R2Entropy_sound) (by decide +kernel)
def CA3_4_9I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA3_4_9I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA3_4_9I1R3Raw_sound (a : PairSlot) :
    (CA3_4_9I1R3Raw a).Encloses (CA3_4_9I1R3Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA3_4_9I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(197401741563142660985948151703 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(17480436938618976355312867047 / 800000000000000000000000000000), (376213013 / 50000000000000000000000000000000)⟩ ⟨(-276726866747074925768263846313257 / 50000000000000000000000000000000), (95291206953 / 50000000000000000000000000000000)⟩ ⟨-8, 197401741563142660985948151703, 195312500000000000000000000000⟩,
   .log ⟨(10206073980499251678574226594187 / 100000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩ ⟨(4658434187533284499824348470301 / 20000000000000000000000000000000), (10806101291 / 100000000000000000000000000000000)⟩ ⟨(-114109357732320870024420401127217 / 50000000000000000000000000000000), (3308722463 / 3125000000000000000000000000000)⟩ ⟨-4, 10206073980499251678574226594187, 6250000000000000000000000000000⟩,
   .log ⟨(477235717337443166844245563137 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2219989718703386725723611185563 / 50000000000000000000000000000000), (202117191 / 12500000000000000000000000000000)⟩ ⟨(-465176774925603375363191168711581 / 100000000000000000000000000000000), (84703294941 / 50000000000000000000000000000000)⟩ ⟨-7, 477235717337443166844245563137, 390625000000000000000000000000⟩]
lemma CA3_4_9I1R3Certificates_valid :
    CA3_4_9I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA3_4_9I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R3Certificates (CA3_4_9I1R3CertificateIndex a)).input
lemma CA3_4_9I1R3P_check : ∀ a : PairSlot, contains (CA3_4_9I1R3Raw a) (CA3_4_9I1R3P a) = true := by
  decide +kernel
lemma CA3_4_9I1R3P_sound (a : PairSlot) :
    (CA3_4_9I1R3P a).Encloses (CA3_4_9I1R3Value a) :=
  contains_sound (CA3_4_9I1R3Raw_sound a) (CA3_4_9I1R3P_check a)
def CA3_4_9I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R3Certificates (CA3_4_9I1R3CertificateIndex a)).output
lemma CA3_4_9I1R3Terms_sound (a : PairSlot) :
    (CA3_4_9I1R3Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R3Certificates_valid
    (CA3_4_9I1R3CertificateIndex a) (CA3_4_9I1R3P_sound a)
def CA3_4_9I1R3Entropy : Ball := ⟨(14958602496200283997491536551753 / 25000000000000000000000000000000), (2635092969 / 10000000000000000000000000000000)⟩
lemma CA3_4_9I1R3Entropy_sound : CA3_4_9I1R3Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R3Value CA3_4_9I1R3Terms CA3_4_9I1R3Terms_sound) (by decide +kernel)
def CA3_4_9I1R3Mass : Ball := ⟨(11555348898300423334234614023867 / 50000000000000000000000000000000), (3 / 3125000000000000000000000000000)⟩
lemma CA3_4_9I1R3Mass_sound : CA3_4_9I1R3Mass.Encloses (∑ a, CA3_4_9I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R3P CA3_4_9I1R3Value CA3_4_9I1R3P_sound) (by decide +kernel)
def CA3_4_9I1R3MassTermLogWitness : LogWitness := ⟨-3, 11555348898300423334234614023867, 6250000000000000000000000000000⟩
def CA3_4_9I1R3MassTermLog : Ball := ⟨(-146487456758383475525259968672667 / 100000000000000000000000000000000), (84703295147 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1R3MassTermLog_sound : CA3_4_9I1R3MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I1R3Mass_sound) (w := CA3_4_9I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I1R3MassTerm : Ball := ⟨(33854273441356347927102503160183 / 100000000000000000000000000000000), (9787761353 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I1R3MassTerm_sound : CA3_4_9I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I1R3Mass_sound) CA3_4_9I1R3MassTermLog_sound) (by decide +kernel)
def CA3_4_9I1R3H : Ball := ⟨(25980136543444788062863643046829 / 100000000000000000000000000000000), (11481613099 / 25000000000000000000000000000000)⟩
lemma CA3_4_9I1R3H_sound : CA3_4_9I1R3H.Encloses (homogeneousEntropy CA3_4_9I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R3Value CA3_4_9I1R3MassTerm_sound CA3_4_9I1R3Entropy_sound) (by decide +kernel)
def CA3_4_9I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA3_4_9I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA3_4_9I1R4Raw_sound (a : PairSlot) :
    (CA3_4_9I1R4Raw a).Encloses (CA3_4_9I1R4Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA3_4_9I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1885575878487842349807621027 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1920561796943324412147676313 / 5000000000000000000000000000000), (12777171 / 100000000000000000000000000000000)⟩ ⟨(-254638625108465456202777856275343 / 25000000000000000000000000000000), (84703301361 / 25000000000000000000000000000000)⟩ ⟨-15, 1885575878487842349807621027, 1525878906250000000000000000⟩,
   .log ⟨(292857264085756312241011408043 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1708306744624285742802727879751 / 100000000000000000000000000000000), (3100747 / 500000000000000000000000000000)⟩ ⟨(-72915501599272631539291127246699 / 12500000000000000000000000000000), (105879118927 / 50000000000000000000000000000000)⟩ ⟨-9, 292857264085756312241011408043, 195312500000000000000000000000⟩,
   .log ⟨(841509810611295391142428923819 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(6874429315078938315221032438319 / 100000000000000000000000000000000), (498950587 / 20000000000000000000000000000000)⟩ ⟨(-3191078603411668648692810823379 / 781250000000000000000000000000), (148230766493 / 100000000000000000000000000000000)⟩ ⟨-6, 841509810611295391142428923819, 781250000000000000000000000000⟩,
   .log ⟨(14706810017409610410934150259 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(239795630012192420696149077293 / 25000000000000000000000000000000), (342571713 / 100000000000000000000000000000000)⟩ ⟨(-652202971897583308566276690454327 / 100000000000000000000000000000000), (14558378867 / 6250000000000000000000000000000)⟩ ⟨-10, 14706810017409610410934150259, 9765625000000000000000000000⟩,
   .log ⟨(6512532435152937635412385023 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(58261440120041247146646050737 / 50000000000000000000000000000000), (19307159 / 50000000000000000000000000000000)⟩ ⟨(-894604989689745160234788813902721 / 100000000000000000000000000000000), (296461539239 / 100000000000000000000000000000000)⟩ ⟨-13, 6512532435152937635412385023, 6103515625000000000000000000⟩]
lemma CA3_4_9I1R4Certificates_valid :
    CA3_4_9I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA3_4_9I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R4Certificates (CA3_4_9I1R4CertificateIndex a)).input
lemma CA3_4_9I1R4P_check : ∀ a : PairSlot, contains (CA3_4_9I1R4Raw a) (CA3_4_9I1R4P a) = true := by
  decide +kernel
lemma CA3_4_9I1R4P_sound (a : PairSlot) :
    (CA3_4_9I1R4P a).Encloses (CA3_4_9I1R4Value a) :=
  contains_sound (CA3_4_9I1R4Raw_sound a) (CA3_4_9I1R4P_check a)
def CA3_4_9I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R4Certificates (CA3_4_9I1R4CertificateIndex a)).output
lemma CA3_4_9I1R4Terms_sound (a : PairSlot) :
    (CA3_4_9I1R4Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R4Certificates_valid
    (CA3_4_9I1R4CertificateIndex a) (CA3_4_9I1R4P_sound a)
def CA3_4_9I1R4Entropy : Ball := ⟨(12402753196542864637174879970159 / 100000000000000000000000000000000), (4484363821 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1R4Entropy_sound : CA3_4_9I1R4Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R4Value CA3_4_9I1R4Terms CA3_4_9I1R4Terms_sound) (by decide +kernel)
def CA3_4_9I1R4Mass : Ball := ⟨(1291718859063276429827809461529 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
lemma CA3_4_9I1R4Mass_sound : CA3_4_9I1R4Mass.Encloses (∑ a, CA3_4_9I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R4P CA3_4_9I1R4Value CA3_4_9I1R4P_sound) (by decide +kernel)
def CA3_4_9I1R4MassTermLogWitness : LogWitness := ⟨-6, 1291718859063276429827809461529, 781250000000000000000000000000⟩
def CA3_4_9I1R4MassTermLog : Ball := ⟨(-36560492250905568030872181889599 / 10000000000000000000000000000000), (37057691687 / 25000000000000000000000000000000)⟩
lemma CA3_4_9I1R4MassTermLog_sound : CA3_4_9I1R4MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I1R4Mass_sound) (w := CA3_4_9I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I1R4MassTerm : Ball := ⟨(2361293866856574973798484466497 / 25000000000000000000000000000000), (382944963 / 10000000000000000000000000000000)⟩
lemma CA3_4_9I1R4MassTerm_sound : CA3_4_9I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I1R4Mass_sound) CA3_4_9I1R4MassTermLog_sound) (by decide +kernel)
def CA3_4_9I1R4H : Ball := ⟨(2957577729116564741980942104171 / 100000000000000000000000000000000), (8313813451 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1R4H_sound : CA3_4_9I1R4H.Encloses (homogeneousEntropy CA3_4_9I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R4Value CA3_4_9I1R4MassTerm_sound CA3_4_9I1R4Entropy_sound) (by decide +kernel)
def CA3_4_9I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA3_4_9I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA3_4_9I1R5Raw_sound (a : PairSlot) :
    (CA3_4_9I1R5Raw a).Encloses (CA3_4_9I1R5Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA3_4_9I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R5Certificates_valid :
    CA3_4_9I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R5Certificates (CA3_4_9I1R5CertificateIndex a)).input
lemma CA3_4_9I1R5P_check : ∀ a : PairSlot, contains (CA3_4_9I1R5Raw a) (CA3_4_9I1R5P a) = true := by
  decide +kernel
lemma CA3_4_9I1R5P_sound (a : PairSlot) :
    (CA3_4_9I1R5P a).Encloses (CA3_4_9I1R5Value a) :=
  contains_sound (CA3_4_9I1R5Raw_sound a) (CA3_4_9I1R5P_check a)
def CA3_4_9I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R5Certificates (CA3_4_9I1R5CertificateIndex a)).output
lemma CA3_4_9I1R5Terms_sound (a : PairSlot) :
    (CA3_4_9I1R5Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R5Certificates_valid
    (CA3_4_9I1R5CertificateIndex a) (CA3_4_9I1R5P_sound a)
def CA3_4_9I1R5Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R5Entropy_sound : CA3_4_9I1R5Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R5Value CA3_4_9I1R5Terms CA3_4_9I1R5Terms_sound) (by decide +kernel)
def CA3_4_9I1R5Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R5Mass_sound : CA3_4_9I1R5Mass.Encloses (∑ a, CA3_4_9I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R5P CA3_4_9I1R5Value CA3_4_9I1R5P_sound) (by decide +kernel)
def CA3_4_9I1R5MassTerm : Ball := .exact 0
lemma CA3_4_9I1R5MassTerm_sound : CA3_4_9I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R5Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R5Mass_sound)
def CA3_4_9I1R5H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R5H_sound : CA3_4_9I1R5H.Encloses (homogeneousEntropy CA3_4_9I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R5Value CA3_4_9I1R5MassTerm_sound CA3_4_9I1R5Entropy_sound) (by decide +kernel)
def CA3_4_9I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA3_4_9I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA3_4_9I1R6Raw_sound (a : PairSlot) :
    (CA3_4_9I1R6Raw a).Encloses (CA3_4_9I1R6Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA3_4_9I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R6Certificates_valid :
    CA3_4_9I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R6Certificates (CA3_4_9I1R6CertificateIndex a)).input
lemma CA3_4_9I1R6P_check : ∀ a : PairSlot, contains (CA3_4_9I1R6Raw a) (CA3_4_9I1R6P a) = true := by
  decide +kernel
lemma CA3_4_9I1R6P_sound (a : PairSlot) :
    (CA3_4_9I1R6P a).Encloses (CA3_4_9I1R6Value a) :=
  contains_sound (CA3_4_9I1R6Raw_sound a) (CA3_4_9I1R6P_check a)
def CA3_4_9I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R6Certificates (CA3_4_9I1R6CertificateIndex a)).output
lemma CA3_4_9I1R6Terms_sound (a : PairSlot) :
    (CA3_4_9I1R6Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R6Certificates_valid
    (CA3_4_9I1R6CertificateIndex a) (CA3_4_9I1R6P_sound a)
def CA3_4_9I1R6Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R6Entropy_sound : CA3_4_9I1R6Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R6Value CA3_4_9I1R6Terms CA3_4_9I1R6Terms_sound) (by decide +kernel)
def CA3_4_9I1R6Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R6Mass_sound : CA3_4_9I1R6Mass.Encloses (∑ a, CA3_4_9I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R6P CA3_4_9I1R6Value CA3_4_9I1R6P_sound) (by decide +kernel)
def CA3_4_9I1R6MassTerm : Ball := .exact 0
lemma CA3_4_9I1R6MassTerm_sound : CA3_4_9I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R6Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R6Mass_sound)
def CA3_4_9I1R6H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R6H_sound : CA3_4_9I1R6H.Encloses (homogeneousEntropy CA3_4_9I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R6Value CA3_4_9I1R6MassTerm_sound CA3_4_9I1R6Entropy_sound) (by decide +kernel)
def CA3_4_9I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA3_4_9I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA3_4_9I1R7Raw_sound (a : PairSlot) :
    (CA3_4_9I1R7Raw a).Encloses (CA3_4_9I1R7Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA3_4_9I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R7Certificates_valid :
    CA3_4_9I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R7Certificates (CA3_4_9I1R7CertificateIndex a)).input
lemma CA3_4_9I1R7P_check : ∀ a : PairSlot, contains (CA3_4_9I1R7Raw a) (CA3_4_9I1R7P a) = true := by
  decide +kernel
lemma CA3_4_9I1R7P_sound (a : PairSlot) :
    (CA3_4_9I1R7P a).Encloses (CA3_4_9I1R7Value a) :=
  contains_sound (CA3_4_9I1R7Raw_sound a) (CA3_4_9I1R7P_check a)
def CA3_4_9I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R7Certificates (CA3_4_9I1R7CertificateIndex a)).output
lemma CA3_4_9I1R7Terms_sound (a : PairSlot) :
    (CA3_4_9I1R7Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R7Certificates_valid
    (CA3_4_9I1R7CertificateIndex a) (CA3_4_9I1R7P_sound a)
def CA3_4_9I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R7Entropy_sound : CA3_4_9I1R7Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R7Value CA3_4_9I1R7Terms CA3_4_9I1R7Terms_sound) (by decide +kernel)
def CA3_4_9I1R7Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R7Mass_sound : CA3_4_9I1R7Mass.Encloses (∑ a, CA3_4_9I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R7P CA3_4_9I1R7Value CA3_4_9I1R7P_sound) (by decide +kernel)
def CA3_4_9I1R7MassTerm : Ball := .exact 0
lemma CA3_4_9I1R7MassTerm_sound : CA3_4_9I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R7Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R7Mass_sound)
def CA3_4_9I1R7H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R7H_sound : CA3_4_9I1R7H.Encloses (homogeneousEntropy CA3_4_9I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R7Value CA3_4_9I1R7MassTerm_sound CA3_4_9I1R7Entropy_sound) (by decide +kernel)
def CA3_4_9I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA3_4_9I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA3_4_9I1R8Raw_sound (a : PairSlot) :
    (CA3_4_9I1R8Raw a).Encloses (CA3_4_9I1R8Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA3_4_9I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R8Certificates_valid :
    CA3_4_9I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R8Certificates (CA3_4_9I1R8CertificateIndex a)).input
lemma CA3_4_9I1R8P_check : ∀ a : PairSlot, contains (CA3_4_9I1R8Raw a) (CA3_4_9I1R8P a) = true := by
  decide +kernel
lemma CA3_4_9I1R8P_sound (a : PairSlot) :
    (CA3_4_9I1R8P a).Encloses (CA3_4_9I1R8Value a) :=
  contains_sound (CA3_4_9I1R8Raw_sound a) (CA3_4_9I1R8P_check a)
def CA3_4_9I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R8Certificates (CA3_4_9I1R8CertificateIndex a)).output
lemma CA3_4_9I1R8Terms_sound (a : PairSlot) :
    (CA3_4_9I1R8Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R8Certificates_valid
    (CA3_4_9I1R8CertificateIndex a) (CA3_4_9I1R8P_sound a)
def CA3_4_9I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R8Entropy_sound : CA3_4_9I1R8Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R8Value CA3_4_9I1R8Terms CA3_4_9I1R8Terms_sound) (by decide +kernel)
def CA3_4_9I1R8Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R8Mass_sound : CA3_4_9I1R8Mass.Encloses (∑ a, CA3_4_9I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R8P CA3_4_9I1R8Value CA3_4_9I1R8P_sound) (by decide +kernel)
def CA3_4_9I1R8MassTerm : Ball := .exact 0
lemma CA3_4_9I1R8MassTerm_sound : CA3_4_9I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R8Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R8Mass_sound)
def CA3_4_9I1R8H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R8H_sound : CA3_4_9I1R8H.Encloses (homogeneousEntropy CA3_4_9I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R8Value CA3_4_9I1R8MassTerm_sound CA3_4_9I1R8Entropy_sound) (by decide +kernel)
def CA3_4_9I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA3_4_9I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA3_4_9I1R9Raw_sound (a : PairSlot) :
    (CA3_4_9I1R9Raw a).Encloses (CA3_4_9I1R9Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA3_4_9I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R9Certificates_valid :
    CA3_4_9I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R9Certificates (CA3_4_9I1R9CertificateIndex a)).input
lemma CA3_4_9I1R9P_check : ∀ a : PairSlot, contains (CA3_4_9I1R9Raw a) (CA3_4_9I1R9P a) = true := by
  decide +kernel
lemma CA3_4_9I1R9P_sound (a : PairSlot) :
    (CA3_4_9I1R9P a).Encloses (CA3_4_9I1R9Value a) :=
  contains_sound (CA3_4_9I1R9Raw_sound a) (CA3_4_9I1R9P_check a)
def CA3_4_9I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R9Certificates (CA3_4_9I1R9CertificateIndex a)).output
lemma CA3_4_9I1R9Terms_sound (a : PairSlot) :
    (CA3_4_9I1R9Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R9Certificates_valid
    (CA3_4_9I1R9CertificateIndex a) (CA3_4_9I1R9P_sound a)
def CA3_4_9I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R9Entropy_sound : CA3_4_9I1R9Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R9Value CA3_4_9I1R9Terms CA3_4_9I1R9Terms_sound) (by decide +kernel)
def CA3_4_9I1R9Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R9Mass_sound : CA3_4_9I1R9Mass.Encloses (∑ a, CA3_4_9I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R9P CA3_4_9I1R9Value CA3_4_9I1R9P_sound) (by decide +kernel)
def CA3_4_9I1R9MassTerm : Ball := .exact 0
lemma CA3_4_9I1R9MassTerm_sound : CA3_4_9I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R9Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R9Mass_sound)
def CA3_4_9I1R9H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R9H_sound : CA3_4_9I1R9H.Encloses (homogeneousEntropy CA3_4_9I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R9Value CA3_4_9I1R9MassTerm_sound CA3_4_9I1R9Entropy_sound) (by decide +kernel)
def CA3_4_9I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA3_4_9I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA3_4_9I1R10Raw_sound (a : PairSlot) :
    (CA3_4_9I1R10Raw a).Encloses (CA3_4_9I1R10Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA3_4_9I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R10Certificates_valid :
    CA3_4_9I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R10Certificates (CA3_4_9I1R10CertificateIndex a)).input
lemma CA3_4_9I1R10P_check : ∀ a : PairSlot, contains (CA3_4_9I1R10Raw a) (CA3_4_9I1R10P a) = true := by
  decide +kernel
lemma CA3_4_9I1R10P_sound (a : PairSlot) :
    (CA3_4_9I1R10P a).Encloses (CA3_4_9I1R10Value a) :=
  contains_sound (CA3_4_9I1R10Raw_sound a) (CA3_4_9I1R10P_check a)
def CA3_4_9I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R10Certificates (CA3_4_9I1R10CertificateIndex a)).output
lemma CA3_4_9I1R10Terms_sound (a : PairSlot) :
    (CA3_4_9I1R10Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R10Certificates_valid
    (CA3_4_9I1R10CertificateIndex a) (CA3_4_9I1R10P_sound a)
def CA3_4_9I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R10Entropy_sound : CA3_4_9I1R10Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R10Value CA3_4_9I1R10Terms CA3_4_9I1R10Terms_sound) (by decide +kernel)
def CA3_4_9I1R10Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R10Mass_sound : CA3_4_9I1R10Mass.Encloses (∑ a, CA3_4_9I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R10P CA3_4_9I1R10Value CA3_4_9I1R10P_sound) (by decide +kernel)
def CA3_4_9I1R10MassTerm : Ball := .exact 0
lemma CA3_4_9I1R10MassTerm_sound : CA3_4_9I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R10Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R10Mass_sound)
def CA3_4_9I1R10H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R10H_sound : CA3_4_9I1R10H.Encloses (homogeneousEntropy CA3_4_9I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R10Value CA3_4_9I1R10MassTerm_sound CA3_4_9I1R10Entropy_sound) (by decide +kernel)
def CA3_4_9I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA3_4_9I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA3_4_9I1R11Raw_sound (a : PairSlot) :
    (CA3_4_9I1R11Raw a).Encloses (CA3_4_9I1R11Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA3_4_9I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R11Certificates_valid :
    CA3_4_9I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R11Certificates (CA3_4_9I1R11CertificateIndex a)).input
lemma CA3_4_9I1R11P_check : ∀ a : PairSlot, contains (CA3_4_9I1R11Raw a) (CA3_4_9I1R11P a) = true := by
  decide +kernel
lemma CA3_4_9I1R11P_sound (a : PairSlot) :
    (CA3_4_9I1R11P a).Encloses (CA3_4_9I1R11Value a) :=
  contains_sound (CA3_4_9I1R11Raw_sound a) (CA3_4_9I1R11P_check a)
def CA3_4_9I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R11Certificates (CA3_4_9I1R11CertificateIndex a)).output
lemma CA3_4_9I1R11Terms_sound (a : PairSlot) :
    (CA3_4_9I1R11Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R11Certificates_valid
    (CA3_4_9I1R11CertificateIndex a) (CA3_4_9I1R11P_sound a)
def CA3_4_9I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R11Entropy_sound : CA3_4_9I1R11Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R11Value CA3_4_9I1R11Terms CA3_4_9I1R11Terms_sound) (by decide +kernel)
def CA3_4_9I1R11Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R11Mass_sound : CA3_4_9I1R11Mass.Encloses (∑ a, CA3_4_9I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R11P CA3_4_9I1R11Value CA3_4_9I1R11P_sound) (by decide +kernel)
def CA3_4_9I1R11MassTerm : Ball := .exact 0
lemma CA3_4_9I1R11MassTerm_sound : CA3_4_9I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R11Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R11Mass_sound)
def CA3_4_9I1R11H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R11H_sound : CA3_4_9I1R11H.Encloses (homogeneousEntropy CA3_4_9I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R11Value CA3_4_9I1R11MassTerm_sound CA3_4_9I1R11Entropy_sound) (by decide +kernel)
def CA3_4_9I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA3_4_9I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA3_4_9I1R12Raw_sound (a : PairSlot) :
    (CA3_4_9I1R12Raw a).Encloses (CA3_4_9I1R12Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA3_4_9I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R12Certificates_valid :
    CA3_4_9I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R12Certificates (CA3_4_9I1R12CertificateIndex a)).input
lemma CA3_4_9I1R12P_check : ∀ a : PairSlot, contains (CA3_4_9I1R12Raw a) (CA3_4_9I1R12P a) = true := by
  decide +kernel
lemma CA3_4_9I1R12P_sound (a : PairSlot) :
    (CA3_4_9I1R12P a).Encloses (CA3_4_9I1R12Value a) :=
  contains_sound (CA3_4_9I1R12Raw_sound a) (CA3_4_9I1R12P_check a)
def CA3_4_9I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R12Certificates (CA3_4_9I1R12CertificateIndex a)).output
lemma CA3_4_9I1R12Terms_sound (a : PairSlot) :
    (CA3_4_9I1R12Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R12Certificates_valid
    (CA3_4_9I1R12CertificateIndex a) (CA3_4_9I1R12P_sound a)
def CA3_4_9I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R12Entropy_sound : CA3_4_9I1R12Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R12Value CA3_4_9I1R12Terms CA3_4_9I1R12Terms_sound) (by decide +kernel)
def CA3_4_9I1R12Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R12Mass_sound : CA3_4_9I1R12Mass.Encloses (∑ a, CA3_4_9I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R12P CA3_4_9I1R12Value CA3_4_9I1R12P_sound) (by decide +kernel)
def CA3_4_9I1R12MassTerm : Ball := .exact 0
lemma CA3_4_9I1R12MassTerm_sound : CA3_4_9I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R12Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R12Mass_sound)
def CA3_4_9I1R12H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R12H_sound : CA3_4_9I1R12H.Encloses (homogeneousEntropy CA3_4_9I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R12Value CA3_4_9I1R12MassTerm_sound CA3_4_9I1R12Entropy_sound) (by decide +kernel)
def CA3_4_9I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA3_4_9I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA3_4_9I1R13Raw_sound (a : PairSlot) :
    (CA3_4_9I1R13Raw a).Encloses (CA3_4_9I1R13Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA3_4_9I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R13Certificates_valid :
    CA3_4_9I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R13Certificates (CA3_4_9I1R13CertificateIndex a)).input
lemma CA3_4_9I1R13P_check : ∀ a : PairSlot, contains (CA3_4_9I1R13Raw a) (CA3_4_9I1R13P a) = true := by
  decide +kernel
lemma CA3_4_9I1R13P_sound (a : PairSlot) :
    (CA3_4_9I1R13P a).Encloses (CA3_4_9I1R13Value a) :=
  contains_sound (CA3_4_9I1R13Raw_sound a) (CA3_4_9I1R13P_check a)
def CA3_4_9I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R13Certificates (CA3_4_9I1R13CertificateIndex a)).output
lemma CA3_4_9I1R13Terms_sound (a : PairSlot) :
    (CA3_4_9I1R13Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R13Certificates_valid
    (CA3_4_9I1R13CertificateIndex a) (CA3_4_9I1R13P_sound a)
def CA3_4_9I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R13Entropy_sound : CA3_4_9I1R13Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R13Value CA3_4_9I1R13Terms CA3_4_9I1R13Terms_sound) (by decide +kernel)
def CA3_4_9I1R13Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R13Mass_sound : CA3_4_9I1R13Mass.Encloses (∑ a, CA3_4_9I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R13P CA3_4_9I1R13Value CA3_4_9I1R13P_sound) (by decide +kernel)
def CA3_4_9I1R13MassTerm : Ball := .exact 0
lemma CA3_4_9I1R13MassTerm_sound : CA3_4_9I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R13Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R13Mass_sound)
def CA3_4_9I1R13H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R13H_sound : CA3_4_9I1R13H.Encloses (homogeneousEntropy CA3_4_9I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R13Value CA3_4_9I1R13MassTerm_sound CA3_4_9I1R13Entropy_sound) (by decide +kernel)
def CA3_4_9I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA3_4_9I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA3_4_9I1R14Raw_sound (a : PairSlot) :
    (CA3_4_9I1R14Raw a).Encloses (CA3_4_9I1R14Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA3_4_9I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R14Certificates_valid :
    CA3_4_9I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R14Certificates (CA3_4_9I1R14CertificateIndex a)).input
lemma CA3_4_9I1R14P_check : ∀ a : PairSlot, contains (CA3_4_9I1R14Raw a) (CA3_4_9I1R14P a) = true := by
  decide +kernel
lemma CA3_4_9I1R14P_sound (a : PairSlot) :
    (CA3_4_9I1R14P a).Encloses (CA3_4_9I1R14Value a) :=
  contains_sound (CA3_4_9I1R14Raw_sound a) (CA3_4_9I1R14P_check a)
def CA3_4_9I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R14Certificates (CA3_4_9I1R14CertificateIndex a)).output
lemma CA3_4_9I1R14Terms_sound (a : PairSlot) :
    (CA3_4_9I1R14Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R14Certificates_valid
    (CA3_4_9I1R14CertificateIndex a) (CA3_4_9I1R14P_sound a)
def CA3_4_9I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R14Entropy_sound : CA3_4_9I1R14Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R14Value CA3_4_9I1R14Terms CA3_4_9I1R14Terms_sound) (by decide +kernel)
def CA3_4_9I1R14Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R14Mass_sound : CA3_4_9I1R14Mass.Encloses (∑ a, CA3_4_9I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R14P CA3_4_9I1R14Value CA3_4_9I1R14P_sound) (by decide +kernel)
def CA3_4_9I1R14MassTerm : Ball := .exact 0
lemma CA3_4_9I1R14MassTerm_sound : CA3_4_9I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R14Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R14Mass_sound)
def CA3_4_9I1R14H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R14H_sound : CA3_4_9I1R14H.Encloses (homogeneousEntropy CA3_4_9I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R14Value CA3_4_9I1R14MassTerm_sound CA3_4_9I1R14Entropy_sound) (by decide +kernel)
def CA3_4_9I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA3_4_9I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA3_4_9I1R15Raw_sound (a : PairSlot) :
    (CA3_4_9I1R15Raw a).Encloses (CA3_4_9I1R15Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA3_4_9I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R15Certificates_valid :
    CA3_4_9I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R15Certificates (CA3_4_9I1R15CertificateIndex a)).input
lemma CA3_4_9I1R15P_check : ∀ a : PairSlot, contains (CA3_4_9I1R15Raw a) (CA3_4_9I1R15P a) = true := by
  decide +kernel
lemma CA3_4_9I1R15P_sound (a : PairSlot) :
    (CA3_4_9I1R15P a).Encloses (CA3_4_9I1R15Value a) :=
  contains_sound (CA3_4_9I1R15Raw_sound a) (CA3_4_9I1R15P_check a)
def CA3_4_9I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R15Certificates (CA3_4_9I1R15CertificateIndex a)).output
lemma CA3_4_9I1R15Terms_sound (a : PairSlot) :
    (CA3_4_9I1R15Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R15Certificates_valid
    (CA3_4_9I1R15CertificateIndex a) (CA3_4_9I1R15P_sound a)
def CA3_4_9I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R15Entropy_sound : CA3_4_9I1R15Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R15Value CA3_4_9I1R15Terms CA3_4_9I1R15Terms_sound) (by decide +kernel)
def CA3_4_9I1R15Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R15Mass_sound : CA3_4_9I1R15Mass.Encloses (∑ a, CA3_4_9I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R15P CA3_4_9I1R15Value CA3_4_9I1R15P_sound) (by decide +kernel)
def CA3_4_9I1R15MassTerm : Ball := .exact 0
lemma CA3_4_9I1R15MassTerm_sound : CA3_4_9I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R15Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R15Mass_sound)
def CA3_4_9I1R15H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R15H_sound : CA3_4_9I1R15H.Encloses (homogeneousEntropy CA3_4_9I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R15Value CA3_4_9I1R15MassTerm_sound CA3_4_9I1R15Entropy_sound) (by decide +kernel)
def CA3_4_9I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA3_4_9I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA3_4_9I1R16Raw_sound (a : PairSlot) :
    (CA3_4_9I1R16Raw a).Encloses (CA3_4_9I1R16Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA3_4_9I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I1R16Certificates_valid :
    CA3_4_9I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R16Certificates (CA3_4_9I1R16CertificateIndex a)).input
lemma CA3_4_9I1R16P_check : ∀ a : PairSlot, contains (CA3_4_9I1R16Raw a) (CA3_4_9I1R16P a) = true := by
  decide +kernel
lemma CA3_4_9I1R16P_sound (a : PairSlot) :
    (CA3_4_9I1R16P a).Encloses (CA3_4_9I1R16Value a) :=
  contains_sound (CA3_4_9I1R16Raw_sound a) (CA3_4_9I1R16P_check a)
def CA3_4_9I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I1R16Certificates (CA3_4_9I1R16CertificateIndex a)).output
lemma CA3_4_9I1R16Terms_sound (a : PairSlot) :
    (CA3_4_9I1R16Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I1R16Certificates_valid
    (CA3_4_9I1R16CertificateIndex a) (CA3_4_9I1R16P_sound a)
def CA3_4_9I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R16Entropy_sound : CA3_4_9I1R16Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I1R16Value CA3_4_9I1R16Terms CA3_4_9I1R16Terms_sound) (by decide +kernel)
def CA3_4_9I1R16Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R16Mass_sound : CA3_4_9I1R16Mass.Encloses (∑ a, CA3_4_9I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I1R16P CA3_4_9I1R16Value CA3_4_9I1R16P_sound) (by decide +kernel)
def CA3_4_9I1R16MassTerm : Ball := .exact 0
lemma CA3_4_9I1R16MassTerm_sound : CA3_4_9I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R16Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I1R16Mass_sound)
def CA3_4_9I1R16H : Ball := ⟨0, 0⟩
lemma CA3_4_9I1R16H_sound : CA3_4_9I1R16H.Encloses (homogeneousEntropy CA3_4_9I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I1R16Value CA3_4_9I1R16MassTerm_sound CA3_4_9I1R16Entropy_sound) (by decide +kernel)
def CA3_4_9I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_4_9I1R0H
  | 1 => CA3_4_9I1R1H
  | 2 => CA3_4_9I1R2H
  | 3 => CA3_4_9I1R3H
  | 4 => CA3_4_9I1R4H
  | 5 => CA3_4_9I1R5H
  | 6 => CA3_4_9I1R6H
  | 7 => CA3_4_9I1R7H
  | 8 => CA3_4_9I1R8H
  | 9 => CA3_4_9I1R9H
  | 10 => CA3_4_9I1R10H
  | 11 => CA3_4_9I1R11H
  | 12 => CA3_4_9I1R12H
  | 13 => CA3_4_9I1R13H
  | 14 => CA3_4_9I1R14H
  | 15 => CA3_4_9I1R15H
  | 16 => CA3_4_9I1R16H
  | _ => (.exact 0)
lemma CA3_4_9I1ResidualEntropies_sound (k : Fin 17) :
    (CA3_4_9I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA3_4_9I1R0H_sound
  · exact CA3_4_9I1R1H_sound
  · exact CA3_4_9I1R2H_sound
  · exact CA3_4_9I1R3H_sound
  · exact CA3_4_9I1R4H_sound
  · exact CA3_4_9I1R5H_sound
  · exact CA3_4_9I1R6H_sound
  · exact CA3_4_9I1R7H_sound
  · exact CA3_4_9I1R8H_sound
  · exact CA3_4_9I1R9H_sound
  · exact CA3_4_9I1R10H_sound
  · exact CA3_4_9I1R11H_sound
  · exact CA3_4_9I1R12H_sound
  · exact CA3_4_9I1R13H_sound
  · exact CA3_4_9I1R14H_sound
  · exact CA3_4_9I1R15H_sound
  · exact CA3_4_9I1R16H_sound
def CA3_4_9I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
lemma CA3_4_9I1Singles_sound (u : Shape) (hu : u ∈ below (shape 3 4 9))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA3_4_9I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A3_4_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 0 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 4 1) by decide +kernel) hd |>.elim
def CA3_4_9I1Singleton : Ball := ⟨0, 0⟩
lemma CA3_4_9I1Singleton_sound : CA3_4_9I1Singleton.Encloses
    (singletonEntropy (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA3_4_9I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_4_9Law_sound u) CA3_4_9I1Singles_sound) (by decide +kernel)
def CA3_4_9I1Group : Ball := ⟨(94891045199893845884746001550373 / 100000000000000000000000000000000), (35269717717 / 20000000000000000000000000000000)⟩
lemma CA3_4_9I1Group_sound : CA3_4_9I1Group.Encloses
    (groupedEntropy (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA3_4_9I1Singleton_sound
    (finSumBall_sound 17 CA3_4_9I1ResidualEntropies _ CA3_4_9I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA3_4_9I1H : Ball := ⟨(121662790199950032058662094478313 / 100000000000000000000000000000000), (524964696283 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I1_sound : CA3_4_9I1H.Encloses (stageACapacity (shape 3 4 9) 1) := by
  have hb := contains_sound (Ball.add_sound CA3_4_9I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA3_4_9I1Group_sound)))
    (show contains (.add CA3_4_9I1PairH (.neg (.mul (.exact 2) CA3_4_9I1Group))) CA3_4_9I1H = true by decide +kernel)
  unfold CA3_4_9I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
