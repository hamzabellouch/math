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
def CA2_5_9I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 2 5 9)) (shape 2 5 9) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA2_5_9I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 5 9) A2_5_9Law 1 a
lemma CA2_5_9I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA2_5_9I1PairRaw a).Encloses (CA2_5_9I1PairValue a) := by
  exact stageAPairBall_sound (shape 2 5 9) (by decide +kernel) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (fun u _ => A2_5_9Law_sound u) 1 a
def CA2_5_9I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(58767960382992480839007727889 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(396459325333626947251218852751 / 50000000000000000000000000000000), (273781217 / 100000000000000000000000000000000)⟩ ⟨(-168654536736467528425815810214747 / 25000000000000000000000000000000), (46586812613 / 20000000000000000000000000000000)⟩ ⟨-10, 58767960382992480839007727889, 48828125000000000000000000000⟩,
   .log ⟨(2590606933834850275205243681 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1485508891101424430870622729 / 1562500000000000000000000000000), (4114369 / 12500000000000000000000000000000)⟩ ⟨(-114684236477545441583647027058547 / 12500000000000000000000000000000), (63527472979 / 20000000000000000000000000000000)⟩ ⟨-14, 2590606933834850275205243681, 1525878906250000000000000000⟩,
   .log ⟨(2745981867591502035041794869 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(53874184830190808013575710667 / 100000000000000000000000000000000), (18607509 / 100000000000000000000000000000000)⟩ ⟨(-61310247376837881701171708132229 / 6250000000000000000000000000000), (21175824821 / 6250000000000000000000000000000)⟩ ⟨-15, 2745981867591502035041794869, 1525878906250000000000000000⟩,
   .log ⟨(2710065051726081673498148871531 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩ ⟨(4889225036002306408609940163453 / 50000000000000000000000000000000), (4017150263 / 100000000000000000000000000000000)⟩ ⟨(-180409877352880683747476075364579 / 50000000000000000000000000000000), (29646153289 / 20000000000000000000000000000000)⟩ ⟨-6, 2710065051726081673498148871531, 1562500000000000000000000000000⟩,
   .log ⟨(122436640021604194836528458687 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1472223366299340295692474895703 / 100000000000000000000000000000000), (103707871 / 20000000000000000000000000000000)⟩ ⟨(-30060923062727862349196471705593 / 5000000000000000000000000000000), (105879118823 / 50000000000000000000000000000000)⟩ ⟨-9, 122436640021604194836528458687, 97656250000000000000000000000⟩,
   .log ⟨(22690538983199886514026113531 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(190395800079647067579218983299 / 100000000000000000000000000000000), (6726873 / 10000000000000000000000000000000)⟩ ⟨(-167819548244857859359923598914237 / 20000000000000000000000000000000), (296461535969 / 100000000000000000000000000000000)⟩ ⟨-13, 22690538983199886514026113531, 12207031250000000000000000000⟩,
   .log ⟨(97690066787711583919526744233 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(519876023827647474286509979471 / 20000000000000000000000000000000), (46545023 / 5000000000000000000000000000000)⟩ ⟨(-532168766920162026766045173909017 / 100000000000000000000000000000000), (38116482793 / 20000000000000000000000000000000)⟩ ⟨-8, 97690066787711583919526744233, 78125000000000000000000000000⟩,
   .log ⟨(406470096200288560025402877 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(31348865236553908515014699977 / 50000000000000000000000000000000), (165261 / 800000000000000000000000000000)⟩ ⟨(-964058165951361978172570358174491 / 100000000000000000000000000000000), (15881868531 / 5000000000000000000000000000000)⟩ ⟨-14, 406470096200288560025402877, 381469726562500000000000000⟩,
   .log ⟨(1526102126905491530775405243131 / 50000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩ ⟨(1065007507457345083364980474119 / 10000000000000000000000000000000), (565538227 / 12500000000000000000000000000000)⟩ ⟨(-174465307511379099196382779562173 / 50000000000000000000000000000000), (74115383169 / 50000000000000000000000000000000)⟩ ⟨-6, 1526102126905491530775405243131, 781250000000000000000000000000⟩,
   .log ⟨(14426086594155923331676518207 / 5000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(843659912352658416356605933641 / 50000000000000000000000000000000), (610968547 / 100000000000000000000000000000000)⟩ ⟨(-116963101094156620609246396633903 / 20000000000000000000000000000000), (211758237523 / 100000000000000000000000000000000)⟩ ⟨-9, 14426086594155923331676518207, 9765625000000000000000000000⟩,
   .log ⟨(25406989929180182184981337909 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(33885115586459414464013650327 / 4000000000000000000000000000000), (295907683 / 100000000000000000000000000000000)⟩ ⟨(-666846322230836564386804567371771 / 100000000000000000000000000000000), (232934062087 / 100000000000000000000000000000000)⟩ ⟨-10, 25406989929180182184981337909, 19531250000000000000000000000⟩,
   .log ⟨(313674041300645300353004729543 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(452049078582313622232021177403 / 25000000000000000000000000000000), (8302883 / 1250000000000000000000000000000)⟩ ⟨(-115291422065504188673213000984231 / 20000000000000000000000000000000), (105879118893 / 50000000000000000000000000000000)⟩ ⟨-9, 313674041300645300353004729543, 195312500000000000000000000000⟩,
   .log ⟨(7443132397103191994943809537 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(241733270217311075975632152167 / 100000000000000000000000000000000), (81959529 / 100000000000000000000000000000000)⟩ ⟨(-405966966124691911560485573444577 / 50000000000000000000000000000000), (275285711237 / 100000000000000000000000000000000)⟩ ⟨-12, 7443132397103191994943809537, 6103515625000000000000000000⟩,
   .log ⟨(12963860454615978603929701577 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(14504550359301825659170257197 / 12500000000000000000000000000000), (3843287 / 10000000000000000000000000000000)⟩ ⟨(-44753799719086797514775048483007 / 5000000000000000000000000000000), (11858461571 / 4000000000000000000000000000000)⟩ ⟨-13, 12963860454615978603929701577, 12207031250000000000000000000⟩,
   .log ⟨(5721259318218938554569654511383 / 50000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩ ⟨(6201370418763669015022762180797 / 25000000000000000000000000000000), (12115237991 / 100000000000000000000000000000000)⟩ ⟨(-21678340637404255434211268008519 / 10000000000000000000000000000000), (52939559391 / 50000000000000000000000000000000)⟩ ⟨-4, 5721259318218938554569654511383, 3125000000000000000000000000000⟩,
   .log ⟨(1086258372234227801232634232139 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(4912528624539643401614980383279 / 100000000000000000000000000000000), (1840193289 / 100000000000000000000000000000000)⟩ ⟨(-452243108095498693500220823300617 / 100000000000000000000000000000000), (42351647481 / 25000000000000000000000000000000)⟩ ⟨-7, 1086258372234227801232634232139, 781250000000000000000000000000⟩,
   .log ⟨(477080083972811338212853152219 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(255010807152888463961905473887 / 10000000000000000000000000000000), (909230763 / 100000000000000000000000000000000)⟩ ⟨(-534524109724566618459559269887467 / 100000000000000000000000000000000), (38116482797 / 20000000000000000000000000000000)⟩ ⟨-8, 477080083972811338212853152219, 390625000000000000000000000000⟩]
lemma CA2_5_9I1PairCertificates_valid :
    CA2_5_9I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 4, 2 => 1
  | 0, 0, 4, 3 => 2
  | 0, 0, 5, 1 => 3
  | 0, 0, 2, 4 => 1
  | 0, 0, 3, 4 => 2
  | 0, 0, 1, 5 => 3
  | 1, 0, 2, 2 => 4
  | 1, 0, 2, 3 => 5
  | 1, 0, 3, 2 => 5
  | 1, 0, 3, 3 => 6
  | 1, 0, 4, 1 => 7
  | 1, 0, 5, 0 => 8
  | 1, 0, 1, 4 => 7
  | 1, 0, 0, 5 => 8
  | 0, 1, 2, 2 => 4
  | 0, 1, 2, 3 => 5
  | 0, 1, 3, 2 => 5
  | 0, 1, 3, 3 => 6
  | 0, 1, 4, 1 => 7
  | 0, 1, 5, 0 => 8
  | 0, 1, 1, 4 => 7
  | 0, 1, 0, 5 => 8
  | 2, 0, 1, 2 => 9
  | 2, 0, 1, 3 => 10
  | 2, 0, 2, 1 => 9
  | 2, 0, 3, 1 => 10
  | 2, 0, 4, 0 => 11
  | 2, 0, 0, 4 => 11
  | 3, 0, 1, 2 => 12
  | 3, 0, 1, 3 => 13
  | 3, 0, 2, 1 => 12
  | 3, 0, 3, 1 => 13
  | 3, 0, 4, 0 => 14
  | 3, 0, 0, 4 => 14
  | 1, 1, 1, 2 => 15
  | 1, 1, 1, 3 => 16
  | 1, 1, 2, 1 => 15
  | 1, 1, 3, 1 => 16
  | 1, 1, 4, 0 => 17
  | 1, 1, 0, 4 => 17
  | 0, 2, 1, 2 => 9
  | 0, 2, 1, 3 => 10
  | 0, 2, 2, 1 => 9
  | 0, 2, 3, 1 => 10
  | 0, 2, 4, 0 => 11
  | 0, 2, 0, 4 => 11
  | 0, 3, 1, 2 => 12
  | 0, 3, 1, 3 => 13
  | 0, 3, 2, 1 => 12
  | 0, 3, 3, 1 => 13
  | 0, 3, 4, 0 => 14
  | 0, 3, 0, 4 => 14
  | 4, 0, 0, 2 => 11
  | 4, 0, 0, 3 => 14
  | 4, 0, 1, 1 => 17
  | 4, 0, 2, 0 => 11
  | 4, 0, 3, 0 => 14
  | 2, 1, 0, 2 => 9
  | 2, 1, 0, 3 => 12
  | 2, 1, 1, 1 => 15
  | 2, 1, 2, 0 => 9
  | 2, 1, 3, 0 => 12
  | 3, 1, 0, 2 => 10
  | 3, 1, 0, 3 => 13
  | 3, 1, 1, 1 => 16
  | 3, 1, 2, 0 => 10
  | 3, 1, 3, 0 => 13
  | 1, 2, 0, 2 => 9
  | 1, 2, 0, 3 => 12
  | 1, 2, 1, 1 => 15
  | 1, 2, 2, 0 => 9
  | 1, 2, 3, 0 => 12
  | 1, 3, 0, 2 => 10
  | 1, 3, 0, 3 => 13
  | 1, 3, 1, 1 => 16
  | 1, 3, 2, 0 => 10
  | 1, 3, 3, 0 => 13
  | 0, 4, 0, 2 => 11
  | 0, 4, 0, 3 => 14
  | 0, 4, 1, 1 => 17
  | 0, 4, 2, 0 => 11
  | 0, 4, 3, 0 => 14
  | 0, 5, 0, 1 => 8
  | 0, 5, 1, 0 => 8
  | 1, 4, 0, 1 => 7
  | 1, 4, 1, 0 => 7
  | 2, 2, 0, 1 => 4
  | 2, 2, 1, 0 => 4
  | 2, 3, 0, 1 => 5
  | 2, 3, 1, 0 => 5
  | 3, 2, 0, 1 => 5
  | 3, 2, 1, 0 => 5
  | 3, 3, 0, 1 => 6
  | 3, 3, 1, 0 => 6
  | 4, 1, 0, 1 => 7
  | 4, 1, 1, 0 => 7
  | 5, 0, 0, 1 => 8
  | 5, 0, 1, 0 => 8
  | 1, 5, 0, 0 => 3
  | 2, 4, 0, 0 => 1
  | 3, 4, 0, 0 => 2
  | 4, 2, 0, 0 => 1
  | 4, 3, 0, 0 => 2
  | 5, 1, 0, 0 => 3
  | _, _, _, _ => 0
def CA2_5_9I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1PairCertificates (CA2_5_9I1PairCertificateIndex a)).input
lemma CA2_5_9I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((0,0),(k,l))) (CA2_5_9I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((0,1),(k,l))) (CA2_5_9I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((0,2),(k,l))) (CA2_5_9I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((0,3),(k,l))) (CA2_5_9I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((0,4),(k,l))) (CA2_5_9I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((0,5),(k,l))) (CA2_5_9I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((1,0),(k,l))) (CA2_5_9I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((1,1),(k,l))) (CA2_5_9I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((1,2),(k,l))) (CA2_5_9I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((1,3),(k,l))) (CA2_5_9I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((1,4),(k,l))) (CA2_5_9I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((1,5),(k,l))) (CA2_5_9I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((2,0),(k,l))) (CA2_5_9I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((2,1),(k,l))) (CA2_5_9I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((2,2),(k,l))) (CA2_5_9I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((2,3),(k,l))) (CA2_5_9I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((2,4),(k,l))) (CA2_5_9I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((2,5),(k,l))) (CA2_5_9I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((3,0),(k,l))) (CA2_5_9I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((3,1),(k,l))) (CA2_5_9I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((3,2),(k,l))) (CA2_5_9I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((3,3),(k,l))) (CA2_5_9I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((3,4),(k,l))) (CA2_5_9I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((3,5),(k,l))) (CA2_5_9I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((4,0),(k,l))) (CA2_5_9I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((4,1),(k,l))) (CA2_5_9I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((4,2),(k,l))) (CA2_5_9I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((4,3),(k,l))) (CA2_5_9I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((4,4),(k,l))) (CA2_5_9I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((4,5),(k,l))) (CA2_5_9I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((5,0),(k,l))) (CA2_5_9I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((5,1),(k,l))) (CA2_5_9I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((5,2),(k,l))) (CA2_5_9I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((5,3),(k,l))) (CA2_5_9I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((5,4),(k,l))) (CA2_5_9I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA2_5_9I1PairRaw ((5,5),(k,l))) (CA2_5_9I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA2_5_9I1PairP_check (a : PairSlot × PairSlot) : contains (CA2_5_9I1PairRaw a) (CA2_5_9I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA2_5_9I1PairP_check_0_0 k l) (CA2_5_9I1PairP_check_0_1 k l) (CA2_5_9I1PairP_check_0_2 k l) (CA2_5_9I1PairP_check_0_3 k l) (CA2_5_9I1PairP_check_0_4 k l) (CA2_5_9I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA2_5_9I1PairP_check_1_0 k l) (CA2_5_9I1PairP_check_1_1 k l) (CA2_5_9I1PairP_check_1_2 k l) (CA2_5_9I1PairP_check_1_3 k l) (CA2_5_9I1PairP_check_1_4 k l) (CA2_5_9I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA2_5_9I1PairP_check_2_0 k l) (CA2_5_9I1PairP_check_2_1 k l) (CA2_5_9I1PairP_check_2_2 k l) (CA2_5_9I1PairP_check_2_3 k l) (CA2_5_9I1PairP_check_2_4 k l) (CA2_5_9I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA2_5_9I1PairP_check_3_0 k l) (CA2_5_9I1PairP_check_3_1 k l) (CA2_5_9I1PairP_check_3_2 k l) (CA2_5_9I1PairP_check_3_3 k l) (CA2_5_9I1PairP_check_3_4 k l) (CA2_5_9I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA2_5_9I1PairP_check_4_0 k l) (CA2_5_9I1PairP_check_4_1 k l) (CA2_5_9I1PairP_check_4_2 k l) (CA2_5_9I1PairP_check_4_3 k l) (CA2_5_9I1PairP_check_4_4 k l) (CA2_5_9I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA2_5_9I1PairP_check_5_0 k l) (CA2_5_9I1PairP_check_5_1 k l) (CA2_5_9I1PairP_check_5_2 k l) (CA2_5_9I1PairP_check_5_3 k l) (CA2_5_9I1PairP_check_5_4 k l) (CA2_5_9I1PairP_check_5_5 k l)
lemma CA2_5_9I1PairP_sound (a : PairSlot × PairSlot) :
    (CA2_5_9I1PairP a).Encloses (CA2_5_9I1PairValue a) :=
  contains_sound (CA2_5_9I1PairRaw_sound a) (CA2_5_9I1PairP_check a)
def CA2_5_9I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1PairCertificates (CA2_5_9I1PairCertificateIndex a)).output
lemma CA2_5_9I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA2_5_9I1PairTerms a).Encloses (Foundation.entropyTerm (CA2_5_9I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1PairCertificates_valid
    (CA2_5_9I1PairCertificateIndex a) (CA2_5_9I1PairP_sound a)
def CA2_5_9I1PairEntropy : Ball := ⟨(16429681926455847443361379676879 / 5000000000000000000000000000000), (8661547441 / 6250000000000000000000000000000)⟩
lemma CA2_5_9I1PairEntropy_sound : CA2_5_9I1PairEntropy.Encloses (Foundation.finiteEntropy CA2_5_9I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA2_5_9I1PairValue CA2_5_9I1PairTerms CA2_5_9I1PairTerms_sound) (by decide +kernel)
def CA2_5_9I1PairMass : Ball := ⟨(12499999999999999999999999999999 / 12500000000000000000000000000000), (141 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I1PairMass_sound : CA2_5_9I1PairMass.Encloses (∑ a, CA2_5_9I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA2_5_9I1PairP CA2_5_9I1PairValue CA2_5_9I1PairP_sound) (by decide +kernel)
def CA2_5_9I1PairMassTermLogWitness : LogWitness := ⟨-1, 12499999999999999999999999999999, 6250000000000000000000000000000⟩
def CA2_5_9I1PairMassTermLog : Ball := ⟨(-7 / 100000000000000000000000000000000), (4235164793 / 10000000000000000000000000000000)⟩
lemma CA2_5_9I1PairMassTermLog_sound : CA2_5_9I1PairMassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I1PairMass_sound) (w := CA2_5_9I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I1PairMassTerm : Ball := ⟨(7 / 100000000000000000000000000000000), (42351647931 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I1PairMassTerm_sound : CA2_5_9I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I1PairMass_sound) CA2_5_9I1PairMassTermLog_sound) (by decide +kernel)
def CA2_5_9I1PairH : Ball := ⟨(328593638529116948867227593537573 / 100000000000000000000000000000000), (180936406987 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I1PairH_sound : CA2_5_9I1PairH.Encloses (homogeneousEntropy CA2_5_9I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1PairValue CA2_5_9I1PairMassTerm_sound CA2_5_9I1PairEntropy_sound) (by decide +kernel)

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
def CA2_5_9I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA2_5_9I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA2_5_9I1R0Raw_sound (a : PairSlot) :
    (CA2_5_9I1R0Raw a).Encloses (CA2_5_9I1R0Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA2_5_9I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1667378902956342085611500253 / 625000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(158107504426140389340504222457 / 10000000000000000000000000000000), (22597199 / 4000000000000000000000000000000)⟩ ⟨(-148162469387027396464920609740599 / 25000000000000000000000000000000), (211758238329 / 100000000000000000000000000000000)⟩ ⟨-9, 1667378902956342085611500253, 1220703125000000000000000000⟩]
lemma CA2_5_9I1R0Certificates_valid :
    CA2_5_9I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA2_5_9I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R0Certificates (CA2_5_9I1R0CertificateIndex a)).input
lemma CA2_5_9I1R0P_check : ∀ a : PairSlot, contains (CA2_5_9I1R0Raw a) (CA2_5_9I1R0P a) = true := by
  decide +kernel
lemma CA2_5_9I1R0P_sound (a : PairSlot) :
    (CA2_5_9I1R0P a).Encloses (CA2_5_9I1R0Value a) :=
  contains_sound (CA2_5_9I1R0Raw_sound a) (CA2_5_9I1R0P_check a)
def CA2_5_9I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R0Certificates (CA2_5_9I1R0CertificateIndex a)).output
lemma CA2_5_9I1R0Terms_sound (a : PairSlot) :
    (CA2_5_9I1R0Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R0Certificates_valid
    (CA2_5_9I1R0CertificateIndex a) (CA2_5_9I1R0P_sound a)
def CA2_5_9I1R0Entropy : Ball := ⟨(158107504426140389340504222457 / 10000000000000000000000000000000), (22597199 / 4000000000000000000000000000000)⟩
lemma CA2_5_9I1R0Entropy_sound : CA2_5_9I1R0Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R0Value CA2_5_9I1R0Terms CA2_5_9I1R0Terms_sound) (by decide +kernel)
def CA2_5_9I1R0Mass : Ball := ⟨(1667378902956342085611500253 / 625000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I1R0Mass_sound : CA2_5_9I1R0Mass.Encloses (∑ a, CA2_5_9I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R0P CA2_5_9I1R0Value CA2_5_9I1R0P_sound) (by decide +kernel)
def CA2_5_9I1R0MassTermLogWitness : LogWitness := ⟨-9, 1667378902956342085611500253, 1220703125000000000000000000⟩
def CA2_5_9I1R0MassTermLog : Ball := ⟨(-148162469387027396464920609740599 / 25000000000000000000000000000000), (211758238329 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I1R0MassTermLog_sound : CA2_5_9I1R0MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I1R0Mass_sound) (w := CA2_5_9I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I1R0MassTerm : Ball := ⟨(158107504426140389340504222457 / 10000000000000000000000000000000), (22597199 / 4000000000000000000000000000000)⟩
lemma CA2_5_9I1R0MassTerm_sound : CA2_5_9I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I1R0Mass_sound) CA2_5_9I1R0MassTermLog_sound) (by decide +kernel)
def CA2_5_9I1R0H : Ball := ⟨0, (22597199 / 2000000000000000000000000000000)⟩
lemma CA2_5_9I1R0H_sound : CA2_5_9I1R0H.Encloses (homogeneousEntropy CA2_5_9I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R0Value CA2_5_9I1R0MassTerm_sound CA2_5_9I1R0Entropy_sound) (by decide +kernel)
def CA2_5_9I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA2_5_9I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA2_5_9I1R1Raw_sound (a : PairSlot) :
    (CA2_5_9I1R1Raw a).Encloses (CA2_5_9I1R1Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA2_5_9I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1053102465437805853118592288551 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩ ⟨(6670635961056939163159896733377 / 50000000000000000000000000000000), (5352074999 / 100000000000000000000000000000000)⟩ ⟨(-316713528834241140507177538837023 / 100000000000000000000000000000000), (31763735649 / 25000000000000000000000000000000)⟩ ⟨-5, 1053102465437805853118592288551, 781250000000000000000000000000⟩]
lemma CA2_5_9I1R1Certificates_valid :
    CA2_5_9I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA2_5_9I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R1Certificates (CA2_5_9I1R1CertificateIndex a)).input
lemma CA2_5_9I1R1P_check : ∀ a : PairSlot, contains (CA2_5_9I1R1Raw a) (CA2_5_9I1R1P a) = true := by
  decide +kernel
lemma CA2_5_9I1R1P_sound (a : PairSlot) :
    (CA2_5_9I1R1P a).Encloses (CA2_5_9I1R1Value a) :=
  contains_sound (CA2_5_9I1R1Raw_sound a) (CA2_5_9I1R1P_check a)
def CA2_5_9I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R1Certificates (CA2_5_9I1R1CertificateIndex a)).output
lemma CA2_5_9I1R1Terms_sound (a : PairSlot) :
    (CA2_5_9I1R1Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R1Certificates_valid
    (CA2_5_9I1R1CertificateIndex a) (CA2_5_9I1R1P_sound a)
def CA2_5_9I1R1Entropy : Ball := ⟨(6670635961056939163159896733377 / 25000000000000000000000000000000), (5352074999 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I1R1Entropy_sound : CA2_5_9I1R1Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R1Value CA2_5_9I1R1Terms CA2_5_9I1R1Terms_sound) (by decide +kernel)
def CA2_5_9I1R1Mass : Ball := ⟨(1053102465437805853118592288551 / 12500000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I1R1Mass_sound : CA2_5_9I1R1Mass.Encloses (∑ a, CA2_5_9I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R1P CA2_5_9I1R1Value CA2_5_9I1R1P_sound) (by decide +kernel)
def CA2_5_9I1R1MassTermLogWitness : LogWitness := ⟨-4, 1053102465437805853118592288551, 781250000000000000000000000000⟩
def CA2_5_9I1R1MassTermLog : Ball := ⟨(-247398810778246609565454345786693 / 100000000000000000000000000000000), (105879118913 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I1R1MassTermLog_sound : CA2_5_9I1R1MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I1R1Mass_sound) (w := CA2_5_9I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I1R1MassTerm : Ball := ⟨(10421451903078108812982719691723 / 50000000000000000000000000000000), (4460062499 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I1R1MassTerm_sound : CA2_5_9I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I1R1Mass_sound) CA2_5_9I1R1MassTermLog_sound) (by decide +kernel)
def CA2_5_9I1R1H : Ball := ⟨(2919820019035769513337073775031 / 50000000000000000000000000000000), (4906068749 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I1R1H_sound : CA2_5_9I1R1H.Encloses (homogeneousEntropy CA2_5_9I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R1Value CA2_5_9I1R1MassTerm_sound CA2_5_9I1R1Entropy_sound) (by decide +kernel)
def CA2_5_9I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA2_5_9I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA2_5_9I1R2Raw_sound (a : PairSlot) :
    (CA2_5_9I1R2Raw a).Encloses (CA2_5_9I1R2Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA2_5_9I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1387104374136000975643699015979 / 20000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩ ⟨(18507536400064431315685081733191 / 100000000000000000000000000000000), (917908691 / 12500000000000000000000000000000)⟩ ⟨(-10674055533329219453488845751113 / 4000000000000000000000000000000), (105879118861 / 100000000000000000000000000000000)⟩ ⟨-4, 1387104374136000975643699015979, 1250000000000000000000000000000⟩,
   .log ⟨(712820862687348093873419338537 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(3523969163294129789506413610911 / 100000000000000000000000000000000), (679255613 / 50000000000000000000000000000000)⟩ ⟨(-247184766030044322285874091146451 / 50000000000000000000000000000000), (47645603427 / 25000000000000000000000000000000)⟩ ⟨-8, 712820862687348093873419338537, 390625000000000000000000000000⟩,
   .log ⟨(3251464273161229062146199101781 / 12500000000000000000000000000000), (33 / 50000000000000000000000000000000)⟩ ⟨(35027977893662315005374984049149 / 100000000000000000000000000000000), (8262292177 / 50000000000000000000000000000000)⟩ ⟨(-134662320384372698886236201504337 / 100000000000000000000000000000000), (31763735651 / 50000000000000000000000000000000)⟩ ⟨-2, 3251464273161229062146199101781, 3125000000000000000000000000000⟩]
lemma CA2_5_9I1R2Certificates_valid :
    CA2_5_9I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA2_5_9I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R2Certificates (CA2_5_9I1R2CertificateIndex a)).input
lemma CA2_5_9I1R2P_check : ∀ a : PairSlot, contains (CA2_5_9I1R2Raw a) (CA2_5_9I1R2P a) = true := by
  decide +kernel
lemma CA2_5_9I1R2P_sound (a : PairSlot) :
    (CA2_5_9I1R2P a).Encloses (CA2_5_9I1R2Value a) :=
  contains_sound (CA2_5_9I1R2Raw_sound a) (CA2_5_9I1R2P_check a)
def CA2_5_9I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R2Certificates (CA2_5_9I1R2CertificateIndex a)).output
lemma CA2_5_9I1R2Terms_sound (a : PairSlot) :
    (CA2_5_9I1R2Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R2Certificates_valid
    (CA2_5_9I1R2CertificateIndex a) (CA2_5_9I1R2P_sound a)
def CA2_5_9I1R2Entropy : Ball := ⟨(79090989020379437215757974737353 / 100000000000000000000000000000000), (16964072931 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I1R2Entropy_sound : CA2_5_9I1R2Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R2Value CA2_5_9I1R2Terms CA2_5_9I1R2Terms_sound) (by decide +kernel)
def CA2_5_9I1R2Mass : Ball := ⟨(5163549956503067305169177706389 / 12500000000000000000000000000000), (17 / 12500000000000000000000000000000)⟩
lemma CA2_5_9I1R2Mass_sound : CA2_5_9I1R2Mass.Encloses (∑ a, CA2_5_9I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R2P CA2_5_9I1R2Value CA2_5_9I1R2P_sound) (by decide +kernel)
def CA2_5_9I1R2MassTermLogWitness : LogWitness := ⟨-2, 5163549956503067305169177706389, 3125000000000000000000000000000⟩
def CA2_5_9I1R2MassTermLog : Ball := ⟨(-22102608132383648426747574327047 / 25000000000000000000000000000000), (31763735689 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I1R2MassTermLog_sound : CA2_5_9I1R2MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I1R2Mass_sound) (w := CA2_5_9I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I1R2MassTerm : Ball := ⟨(18260467401691828723107280068591 / 50000000000000000000000000000000), (26242181887 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I1R2MassTerm_sound : CA2_5_9I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I1R2Mass_sound) CA2_5_9I1R2MassTermLog_sound) (by decide +kernel)
def CA2_5_9I1R2H : Ball := ⟨(42570054216995779769543414600171 / 100000000000000000000000000000000), (60170327749 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I1R2H_sound : CA2_5_9I1R2H.Encloses (homogeneousEntropy CA2_5_9I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R2Value CA2_5_9I1R2MassTerm_sound CA2_5_9I1R2Entropy_sound) (by decide +kernel)
def CA2_5_9I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA2_5_9I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA2_5_9I1R3Raw_sound (a : PairSlot) :
    (CA2_5_9I1R3Raw a).Encloses (CA2_5_9I1R3Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA2_5_9I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(757077704173845117270525934463 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(1848579179567801739232915360923 / 50000000000000000000000000000000), (360714247 / 25000000000000000000000000000000)⟩ ⟨(-244172978463954201784196004312511 / 50000000000000000000000000000000), (190582413807 / 100000000000000000000000000000000)⟩ ⟨-8, 757077704173845117270525934463, 390625000000000000000000000000⟩,
   .log ⟨(18174275226661133832946939454377 / 100000000000000000000000000000000), (1 / 2000000000000000000000000000000)⟩ ⟨(30990102410762529748110608284967 / 100000000000000000000000000000000), (15394210047 / 100000000000000000000000000000000)⟩ ⟨(-170516304085133198098477550097527 / 100000000000000000000000000000000), (84703295007 / 100000000000000000000000000000000)⟩ ⟨-3, 18174275226661133832946939454377, 12500000000000000000000000000000⟩,
   .log ⟨(430711723794322567614811359179 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(6996812186136387755160203483507 / 100000000000000000000000000000000), (638447293 / 25000000000000000000000000000000)⟩ ⟨(-406119209183493807255103685890127 / 100000000000000000000000000000000), (14823076607 / 10000000000000000000000000000000)⟩ ⟨-6, 430711723794322567614811359179, 390625000000000000000000000000⟩]
lemma CA2_5_9I1R3Certificates_valid :
    CA2_5_9I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA2_5_9I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R3Certificates (CA2_5_9I1R3CertificateIndex a)).input
lemma CA2_5_9I1R3P_check : ∀ a : PairSlot, contains (CA2_5_9I1R3Raw a) (CA2_5_9I1R3P a) = true := by
  decide +kernel
lemma CA2_5_9I1R3P_sound (a : PairSlot) :
    (CA2_5_9I1R3P a).Encloses (CA2_5_9I1R3Value a) :=
  contains_sound (CA2_5_9I1R3Raw_sound a) (CA2_5_9I1R3P_check a)
def CA2_5_9I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R3Certificates (CA2_5_9I1R3CertificateIndex a)).output
lemma CA2_5_9I1R3Terms_sound (a : PairSlot) :
    (CA2_5_9I1R3Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R3Certificates_valid
    (CA2_5_9I1R3CertificateIndex a) (CA2_5_9I1R3P_sound a)
def CA2_5_9I1R3Entropy : Ball := ⟨(521050911950431512271708031129 / 625000000000000000000000000000), (19390856207 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I1R3Entropy_sound : CA2_5_9I1R3Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R3Value CA2_5_9I1R3Terms CA2_5_9I1R3Terms_sound) (by decide +kernel)
def CA2_5_9I1R3Mass : Ball := ⟨(5163549956503067305169177706389 / 12500000000000000000000000000000), (3 / 2500000000000000000000000000000)⟩
lemma CA2_5_9I1R3Mass_sound : CA2_5_9I1R3Mass.Encloses (∑ a, CA2_5_9I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R3P CA2_5_9I1R3Value CA2_5_9I1R3P_sound) (by decide +kernel)
def CA2_5_9I1R3MassTermLogWitness : LogWitness := ⟨-2, 5163549956503067305169177706389, 3125000000000000000000000000000⟩
def CA2_5_9I1R3MassTermLog : Ball := ⟨(-22102608132383648426747574327047 / 25000000000000000000000000000000), (63527471339 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I1R3MassTermLog_sound : CA2_5_9I1R3MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I1R3Mass_sound) (w := CA2_5_9I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I1R3MassTerm : Ball := ⟨(18260467401691828723107280068591 / 50000000000000000000000000000000), (820068183 / 3125000000000000000000000000000)⟩
lemma CA2_5_9I1R3MassTerm_sound : CA2_5_9I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I1R3Mass_sound) CA2_5_9I1R3MassTermLog_sound) (by decide +kernel)
def CA2_5_9I1R3H : Ball := ⟨(23423605554342692258629362421729 / 50000000000000000000000000000000), (6502389427 / 10000000000000000000000000000000)⟩
lemma CA2_5_9I1R3H_sound : CA2_5_9I1R3H.Encloses (homogeneousEntropy CA2_5_9I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R3Value CA2_5_9I1R3MassTerm_sound CA2_5_9I1R3Entropy_sound) (by decide +kernel)
def CA2_5_9I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA2_5_9I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA2_5_9I1R4Raw_sound (a : PairSlot) :
    (CA2_5_9I1R4Raw a).Encloses (CA2_5_9I1R4Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA2_5_9I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(406470096200288560025402877 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1818432276703039405011623079 / 1562500000000000000000000000000), (3856089 / 10000000000000000000000000000000)⟩ ⟨(-894743447895367447230847165124161 / 100000000000000000000000000000000), (296461539249 / 100000000000000000000000000000000)⟩ ⟨-13, 406470096200288560025402877, 381469726562500000000000000⟩,
   .log ⟨(97690066787711583919526744233 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(4521624294650324365649214543539 / 100000000000000000000000000000000), (827467069 / 50000000000000000000000000000000)⟩ ⟨(-462854048864167495824321980858687 / 100000000000000000000000000000000), (84703295039 / 50000000000000000000000000000000)⟩ ⟨-7, 97690066787711583919526744233, 78125000000000000000000000000⟩,
   .log ⟨(5420130103452163346996297743061 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩ ⟨(1974994030566659239713842560509 / 12500000000000000000000000000000), (6886543283 / 100000000000000000000000000000000)⟩ ⟨(-145752518324883418276614478839423 / 50000000000000000000000000000000), (127054942651 / 100000000000000000000000000000000)⟩ ⟨-5, 5420130103452163346996297743061, 3125000000000000000000000000000⟩,
   .log ⟨(122436640021604194836528458687 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(520996057057169791070579025991 / 20000000000000000000000000000000), (933370839 / 100000000000000000000000000000000)⟩ ⟨(-53190374319856271604220624106153 / 10000000000000000000000000000000), (190582413963 / 100000000000000000000000000000000)⟩ ⟨-8, 122436640021604194836528458687, 97656250000000000000000000000⟩,
   .log ⟨(22690538983199886514026113531 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(349335833916113075987820257223 / 100000000000000000000000000000000), (124927631 / 100000000000000000000000000000000)⟩ ⟨(-153956604633658953171578960304171 / 20000000000000000000000000000000), (137642855041 / 50000000000000000000000000000000)⟩ ⟨-12, 22690538983199886514026113531, 12207031250000000000000000000⟩]
lemma CA2_5_9I1R4Certificates_valid :
    CA2_5_9I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA2_5_9I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R4Certificates (CA2_5_9I1R4CertificateIndex a)).input
lemma CA2_5_9I1R4P_check : ∀ a : PairSlot, contains (CA2_5_9I1R4Raw a) (CA2_5_9I1R4P a) = true := by
  decide +kernel
lemma CA2_5_9I1R4P_sound (a : PairSlot) :
    (CA2_5_9I1R4P a).Encloses (CA2_5_9I1R4Value a) :=
  contains_sound (CA2_5_9I1R4Raw_sound a) (CA2_5_9I1R4P_check a)
def CA2_5_9I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R4Certificates (CA2_5_9I1R4CertificateIndex a)).output
lemma CA2_5_9I1R4Terms_sound (a : PairSlot) :
    (CA2_5_9I1R4Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R4Certificates_valid
    (CA2_5_9I1R4CertificateIndex a) (CA2_5_9I1R4P_sound a)
def CA2_5_9I1R4Entropy : Ball := ⟨(6127051313947944535908853568479 / 20000000000000000000000000000000), (1533150331 / 12500000000000000000000000000000)⟩
lemma CA2_5_9I1R4Entropy_sound : CA2_5_9I1R4Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R4Value CA2_5_9I1R4Terms CA2_5_9I1R4Terms_sound) (by decide +kernel)
def CA2_5_9I1R4Mass : Ball := ⟨(8424819723502446824948738308407 / 100000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I1R4Mass_sound : CA2_5_9I1R4Mass.Encloses (∑ a, CA2_5_9I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R4P CA2_5_9I1R4Value CA2_5_9I1R4P_sound) (by decide +kernel)
def CA2_5_9I1R4MassTermLogWitness : LogWitness := ⟨-4, 8424819723502446824948738308407, 6250000000000000000000000000000⟩
def CA2_5_9I1R4MassTermLog : Ball := ⟨(-49479762155649321913090869157341 / 20000000000000000000000000000000), (26469779761 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I1R4MassTermLog_sound : CA2_5_9I1R4MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I1R4Mass_sound) (w := CA2_5_9I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I1R4MassTerm : Ball := ⟨(4168580761231243525193087876689 / 20000000000000000000000000000000), (2230031259 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I1R4MassTerm_sound : CA2_5_9I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I1R4Mass_sound) CA2_5_9I1R4MassTermLog_sound) (by decide +kernel)
def CA2_5_9I1R4H : Ball := ⟨(195847055271670101071576569179 / 2000000000000000000000000000000), (5296331921 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I1R4H_sound : CA2_5_9I1R4H.Encloses (homogeneousEntropy CA2_5_9I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R4Value CA2_5_9I1R4MassTerm_sound CA2_5_9I1R4Entropy_sound) (by decide +kernel)
def CA2_5_9I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA2_5_9I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA2_5_9I1R5Raw_sound (a : PairSlot) :
    (CA2_5_9I1R5Raw a).Encloses (CA2_5_9I1R5Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA2_5_9I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2745981867591502035041794869 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(53874184830190808013575710667 / 100000000000000000000000000000000), (18607509 / 100000000000000000000000000000000)⟩ ⟨(-61310247376837881701171708132229 / 6250000000000000000000000000000), (21175824821 / 6250000000000000000000000000000)⟩ ⟨-15, 2745981867591502035041794869, 1525878906250000000000000000⟩,
   .log ⟨(58767960382992480839007727889 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(396459325333626947251218852751 / 50000000000000000000000000000000), (273781217 / 100000000000000000000000000000000)⟩ ⟨(-168654536736467528425815810214747 / 25000000000000000000000000000000), (46586812613 / 20000000000000000000000000000000)⟩ ⟨-10, 58767960382992480839007727889, 48828125000000000000000000000⟩,
   .log ⟨(2590606933834850275205243681 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1485508891101424430870622729 / 1562500000000000000000000000000), (4114369 / 12500000000000000000000000000000)⟩ ⟨(-114684236477545441583647027058547 / 12500000000000000000000000000000), (63527472979 / 20000000000000000000000000000000)⟩ ⟨-14, 2590606933834850275205243681, 1525878906250000000000000000⟩]
lemma CA2_5_9I1R5Certificates_valid :
    CA2_5_9I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA2_5_9I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R5Certificates (CA2_5_9I1R5CertificateIndex a)).input
lemma CA2_5_9I1R5P_check : ∀ a : PairSlot, contains (CA2_5_9I1R5Raw a) (CA2_5_9I1R5P a) = true := by
  decide +kernel
lemma CA2_5_9I1R5P_sound (a : PairSlot) :
    (CA2_5_9I1R5P a).Encloses (CA2_5_9I1R5Value a) :=
  contains_sound (CA2_5_9I1R5Raw_sound a) (CA2_5_9I1R5P_check a)
def CA2_5_9I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R5Certificates (CA2_5_9I1R5CertificateIndex a)).output
lemma CA2_5_9I1R5Terms_sound (a : PairSlot) :
    (CA2_5_9I1R5Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R5Certificates_valid
    (CA2_5_9I1R5CertificateIndex a) (CA2_5_9I1R5P_sound a)
def CA2_5_9I1R5Entropy : Ball := ⟨(37674616181117434643669330833 / 2000000000000000000000000000000), (162651839 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I1R5Entropy_sound : CA2_5_9I1R5Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R5Value CA2_5_9I1R5Terms CA2_5_9I1R5Terms_sound) (by decide +kernel)
def CA2_5_9I1R5Mass : Ball := ⟨(1667378902956342085611500253 / 625000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
lemma CA2_5_9I1R5Mass_sound : CA2_5_9I1R5Mass.Encloses (∑ a, CA2_5_9I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R5P CA2_5_9I1R5Value CA2_5_9I1R5P_sound) (by decide +kernel)
def CA2_5_9I1R5MassTermLogWitness : LogWitness := ⟨-9, 1667378902956342085611500253, 1220703125000000000000000000⟩
def CA2_5_9I1R5MassTermLog : Ball := ⟨(-148162469387027396464920609740599 / 25000000000000000000000000000000), (105879120289 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I1R5MassTermLog_sound : CA2_5_9I1R5MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I1R5Mass_sound) (w := CA2_5_9I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I1R5MassTerm : Ball := ⟨(158107504426140389340504222457 / 10000000000000000000000000000000), (564930017 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I1R5MassTerm_sound : CA2_5_9I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I1R5Mass_sound) CA2_5_9I1R5MassTermLog_sound) (by decide +kernel)
def CA2_5_9I1R5H : Ball := ⟨(7566394119861695969460607927 / 2500000000000000000000000000000), (1215537373 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I1R5H_sound : CA2_5_9I1R5H.Encloses (homogeneousEntropy CA2_5_9I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R5Value CA2_5_9I1R5MassTerm_sound CA2_5_9I1R5Entropy_sound) (by decide +kernel)
def CA2_5_9I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA2_5_9I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA2_5_9I1R6Raw_sound (a : PairSlot) :
    (CA2_5_9I1R6Raw a).Encloses (CA2_5_9I1R6Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA2_5_9I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I1R6Certificates_valid :
    CA2_5_9I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R6Certificates (CA2_5_9I1R6CertificateIndex a)).input
lemma CA2_5_9I1R6P_check : ∀ a : PairSlot, contains (CA2_5_9I1R6Raw a) (CA2_5_9I1R6P a) = true := by
  decide +kernel
lemma CA2_5_9I1R6P_sound (a : PairSlot) :
    (CA2_5_9I1R6P a).Encloses (CA2_5_9I1R6Value a) :=
  contains_sound (CA2_5_9I1R6Raw_sound a) (CA2_5_9I1R6P_check a)
def CA2_5_9I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R6Certificates (CA2_5_9I1R6CertificateIndex a)).output
lemma CA2_5_9I1R6Terms_sound (a : PairSlot) :
    (CA2_5_9I1R6Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R6Certificates_valid
    (CA2_5_9I1R6CertificateIndex a) (CA2_5_9I1R6P_sound a)
def CA2_5_9I1R6Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R6Entropy_sound : CA2_5_9I1R6Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R6Value CA2_5_9I1R6Terms CA2_5_9I1R6Terms_sound) (by decide +kernel)
def CA2_5_9I1R6Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R6Mass_sound : CA2_5_9I1R6Mass.Encloses (∑ a, CA2_5_9I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R6P CA2_5_9I1R6Value CA2_5_9I1R6P_sound) (by decide +kernel)
def CA2_5_9I1R6MassTerm : Ball := .exact 0
lemma CA2_5_9I1R6MassTerm_sound : CA2_5_9I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R6Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I1R6Mass_sound)
def CA2_5_9I1R6H : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R6H_sound : CA2_5_9I1R6H.Encloses (homogeneousEntropy CA2_5_9I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R6Value CA2_5_9I1R6MassTerm_sound CA2_5_9I1R6Entropy_sound) (by decide +kernel)
def CA2_5_9I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA2_5_9I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA2_5_9I1R7Raw_sound (a : PairSlot) :
    (CA2_5_9I1R7Raw a).Encloses (CA2_5_9I1R7Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA2_5_9I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I1R7Certificates_valid :
    CA2_5_9I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R7Certificates (CA2_5_9I1R7CertificateIndex a)).input
lemma CA2_5_9I1R7P_check : ∀ a : PairSlot, contains (CA2_5_9I1R7Raw a) (CA2_5_9I1R7P a) = true := by
  decide +kernel
lemma CA2_5_9I1R7P_sound (a : PairSlot) :
    (CA2_5_9I1R7P a).Encloses (CA2_5_9I1R7Value a) :=
  contains_sound (CA2_5_9I1R7Raw_sound a) (CA2_5_9I1R7P_check a)
def CA2_5_9I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R7Certificates (CA2_5_9I1R7CertificateIndex a)).output
lemma CA2_5_9I1R7Terms_sound (a : PairSlot) :
    (CA2_5_9I1R7Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R7Certificates_valid
    (CA2_5_9I1R7CertificateIndex a) (CA2_5_9I1R7P_sound a)
def CA2_5_9I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R7Entropy_sound : CA2_5_9I1R7Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R7Value CA2_5_9I1R7Terms CA2_5_9I1R7Terms_sound) (by decide +kernel)
def CA2_5_9I1R7Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R7Mass_sound : CA2_5_9I1R7Mass.Encloses (∑ a, CA2_5_9I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R7P CA2_5_9I1R7Value CA2_5_9I1R7P_sound) (by decide +kernel)
def CA2_5_9I1R7MassTerm : Ball := .exact 0
lemma CA2_5_9I1R7MassTerm_sound : CA2_5_9I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R7Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I1R7Mass_sound)
def CA2_5_9I1R7H : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R7H_sound : CA2_5_9I1R7H.Encloses (homogeneousEntropy CA2_5_9I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R7Value CA2_5_9I1R7MassTerm_sound CA2_5_9I1R7Entropy_sound) (by decide +kernel)
def CA2_5_9I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA2_5_9I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA2_5_9I1R8Raw_sound (a : PairSlot) :
    (CA2_5_9I1R8Raw a).Encloses (CA2_5_9I1R8Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA2_5_9I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I1R8Certificates_valid :
    CA2_5_9I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R8Certificates (CA2_5_9I1R8CertificateIndex a)).input
lemma CA2_5_9I1R8P_check : ∀ a : PairSlot, contains (CA2_5_9I1R8Raw a) (CA2_5_9I1R8P a) = true := by
  decide +kernel
lemma CA2_5_9I1R8P_sound (a : PairSlot) :
    (CA2_5_9I1R8P a).Encloses (CA2_5_9I1R8Value a) :=
  contains_sound (CA2_5_9I1R8Raw_sound a) (CA2_5_9I1R8P_check a)
def CA2_5_9I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R8Certificates (CA2_5_9I1R8CertificateIndex a)).output
lemma CA2_5_9I1R8Terms_sound (a : PairSlot) :
    (CA2_5_9I1R8Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R8Certificates_valid
    (CA2_5_9I1R8CertificateIndex a) (CA2_5_9I1R8P_sound a)
def CA2_5_9I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R8Entropy_sound : CA2_5_9I1R8Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R8Value CA2_5_9I1R8Terms CA2_5_9I1R8Terms_sound) (by decide +kernel)
def CA2_5_9I1R8Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R8Mass_sound : CA2_5_9I1R8Mass.Encloses (∑ a, CA2_5_9I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R8P CA2_5_9I1R8Value CA2_5_9I1R8P_sound) (by decide +kernel)
def CA2_5_9I1R8MassTerm : Ball := .exact 0
lemma CA2_5_9I1R8MassTerm_sound : CA2_5_9I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R8Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I1R8Mass_sound)
def CA2_5_9I1R8H : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R8H_sound : CA2_5_9I1R8H.Encloses (homogeneousEntropy CA2_5_9I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R8Value CA2_5_9I1R8MassTerm_sound CA2_5_9I1R8Entropy_sound) (by decide +kernel)
def CA2_5_9I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA2_5_9I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA2_5_9I1R9Raw_sound (a : PairSlot) :
    (CA2_5_9I1R9Raw a).Encloses (CA2_5_9I1R9Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA2_5_9I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I1R9Certificates_valid :
    CA2_5_9I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R9Certificates (CA2_5_9I1R9CertificateIndex a)).input
lemma CA2_5_9I1R9P_check : ∀ a : PairSlot, contains (CA2_5_9I1R9Raw a) (CA2_5_9I1R9P a) = true := by
  decide +kernel
lemma CA2_5_9I1R9P_sound (a : PairSlot) :
    (CA2_5_9I1R9P a).Encloses (CA2_5_9I1R9Value a) :=
  contains_sound (CA2_5_9I1R9Raw_sound a) (CA2_5_9I1R9P_check a)
def CA2_5_9I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R9Certificates (CA2_5_9I1R9CertificateIndex a)).output
lemma CA2_5_9I1R9Terms_sound (a : PairSlot) :
    (CA2_5_9I1R9Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R9Certificates_valid
    (CA2_5_9I1R9CertificateIndex a) (CA2_5_9I1R9P_sound a)
def CA2_5_9I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R9Entropy_sound : CA2_5_9I1R9Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R9Value CA2_5_9I1R9Terms CA2_5_9I1R9Terms_sound) (by decide +kernel)
def CA2_5_9I1R9Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R9Mass_sound : CA2_5_9I1R9Mass.Encloses (∑ a, CA2_5_9I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R9P CA2_5_9I1R9Value CA2_5_9I1R9P_sound) (by decide +kernel)
def CA2_5_9I1R9MassTerm : Ball := .exact 0
lemma CA2_5_9I1R9MassTerm_sound : CA2_5_9I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R9Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I1R9Mass_sound)
def CA2_5_9I1R9H : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R9H_sound : CA2_5_9I1R9H.Encloses (homogeneousEntropy CA2_5_9I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R9Value CA2_5_9I1R9MassTerm_sound CA2_5_9I1R9Entropy_sound) (by decide +kernel)
def CA2_5_9I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA2_5_9I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA2_5_9I1R10Raw_sound (a : PairSlot) :
    (CA2_5_9I1R10Raw a).Encloses (CA2_5_9I1R10Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA2_5_9I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I1R10Certificates_valid :
    CA2_5_9I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R10Certificates (CA2_5_9I1R10CertificateIndex a)).input
lemma CA2_5_9I1R10P_check : ∀ a : PairSlot, contains (CA2_5_9I1R10Raw a) (CA2_5_9I1R10P a) = true := by
  decide +kernel
lemma CA2_5_9I1R10P_sound (a : PairSlot) :
    (CA2_5_9I1R10P a).Encloses (CA2_5_9I1R10Value a) :=
  contains_sound (CA2_5_9I1R10Raw_sound a) (CA2_5_9I1R10P_check a)
def CA2_5_9I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R10Certificates (CA2_5_9I1R10CertificateIndex a)).output
lemma CA2_5_9I1R10Terms_sound (a : PairSlot) :
    (CA2_5_9I1R10Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R10Certificates_valid
    (CA2_5_9I1R10CertificateIndex a) (CA2_5_9I1R10P_sound a)
def CA2_5_9I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R10Entropy_sound : CA2_5_9I1R10Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R10Value CA2_5_9I1R10Terms CA2_5_9I1R10Terms_sound) (by decide +kernel)
def CA2_5_9I1R10Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R10Mass_sound : CA2_5_9I1R10Mass.Encloses (∑ a, CA2_5_9I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R10P CA2_5_9I1R10Value CA2_5_9I1R10P_sound) (by decide +kernel)
def CA2_5_9I1R10MassTerm : Ball := .exact 0
lemma CA2_5_9I1R10MassTerm_sound : CA2_5_9I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R10Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I1R10Mass_sound)
def CA2_5_9I1R10H : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R10H_sound : CA2_5_9I1R10H.Encloses (homogeneousEntropy CA2_5_9I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R10Value CA2_5_9I1R10MassTerm_sound CA2_5_9I1R10Entropy_sound) (by decide +kernel)
def CA2_5_9I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA2_5_9I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA2_5_9I1R11Raw_sound (a : PairSlot) :
    (CA2_5_9I1R11Raw a).Encloses (CA2_5_9I1R11Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA2_5_9I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I1R11Certificates_valid :
    CA2_5_9I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R11Certificates (CA2_5_9I1R11CertificateIndex a)).input
lemma CA2_5_9I1R11P_check : ∀ a : PairSlot, contains (CA2_5_9I1R11Raw a) (CA2_5_9I1R11P a) = true := by
  decide +kernel
lemma CA2_5_9I1R11P_sound (a : PairSlot) :
    (CA2_5_9I1R11P a).Encloses (CA2_5_9I1R11Value a) :=
  contains_sound (CA2_5_9I1R11Raw_sound a) (CA2_5_9I1R11P_check a)
def CA2_5_9I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R11Certificates (CA2_5_9I1R11CertificateIndex a)).output
lemma CA2_5_9I1R11Terms_sound (a : PairSlot) :
    (CA2_5_9I1R11Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R11Certificates_valid
    (CA2_5_9I1R11CertificateIndex a) (CA2_5_9I1R11P_sound a)
def CA2_5_9I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R11Entropy_sound : CA2_5_9I1R11Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R11Value CA2_5_9I1R11Terms CA2_5_9I1R11Terms_sound) (by decide +kernel)
def CA2_5_9I1R11Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R11Mass_sound : CA2_5_9I1R11Mass.Encloses (∑ a, CA2_5_9I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R11P CA2_5_9I1R11Value CA2_5_9I1R11P_sound) (by decide +kernel)
def CA2_5_9I1R11MassTerm : Ball := .exact 0
lemma CA2_5_9I1R11MassTerm_sound : CA2_5_9I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R11Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I1R11Mass_sound)
def CA2_5_9I1R11H : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R11H_sound : CA2_5_9I1R11H.Encloses (homogeneousEntropy CA2_5_9I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R11Value CA2_5_9I1R11MassTerm_sound CA2_5_9I1R11Entropy_sound) (by decide +kernel)
def CA2_5_9I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA2_5_9I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA2_5_9I1R12Raw_sound (a : PairSlot) :
    (CA2_5_9I1R12Raw a).Encloses (CA2_5_9I1R12Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA2_5_9I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I1R12Certificates_valid :
    CA2_5_9I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R12Certificates (CA2_5_9I1R12CertificateIndex a)).input
lemma CA2_5_9I1R12P_check : ∀ a : PairSlot, contains (CA2_5_9I1R12Raw a) (CA2_5_9I1R12P a) = true := by
  decide +kernel
lemma CA2_5_9I1R12P_sound (a : PairSlot) :
    (CA2_5_9I1R12P a).Encloses (CA2_5_9I1R12Value a) :=
  contains_sound (CA2_5_9I1R12Raw_sound a) (CA2_5_9I1R12P_check a)
def CA2_5_9I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R12Certificates (CA2_5_9I1R12CertificateIndex a)).output
lemma CA2_5_9I1R12Terms_sound (a : PairSlot) :
    (CA2_5_9I1R12Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R12Certificates_valid
    (CA2_5_9I1R12CertificateIndex a) (CA2_5_9I1R12P_sound a)
def CA2_5_9I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R12Entropy_sound : CA2_5_9I1R12Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R12Value CA2_5_9I1R12Terms CA2_5_9I1R12Terms_sound) (by decide +kernel)
def CA2_5_9I1R12Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R12Mass_sound : CA2_5_9I1R12Mass.Encloses (∑ a, CA2_5_9I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R12P CA2_5_9I1R12Value CA2_5_9I1R12P_sound) (by decide +kernel)
def CA2_5_9I1R12MassTerm : Ball := .exact 0
lemma CA2_5_9I1R12MassTerm_sound : CA2_5_9I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R12Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I1R12Mass_sound)
def CA2_5_9I1R12H : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R12H_sound : CA2_5_9I1R12H.Encloses (homogeneousEntropy CA2_5_9I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R12Value CA2_5_9I1R12MassTerm_sound CA2_5_9I1R12Entropy_sound) (by decide +kernel)
def CA2_5_9I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA2_5_9I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA2_5_9I1R13Raw_sound (a : PairSlot) :
    (CA2_5_9I1R13Raw a).Encloses (CA2_5_9I1R13Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA2_5_9I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I1R13Certificates_valid :
    CA2_5_9I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R13Certificates (CA2_5_9I1R13CertificateIndex a)).input
lemma CA2_5_9I1R13P_check : ∀ a : PairSlot, contains (CA2_5_9I1R13Raw a) (CA2_5_9I1R13P a) = true := by
  decide +kernel
lemma CA2_5_9I1R13P_sound (a : PairSlot) :
    (CA2_5_9I1R13P a).Encloses (CA2_5_9I1R13Value a) :=
  contains_sound (CA2_5_9I1R13Raw_sound a) (CA2_5_9I1R13P_check a)
def CA2_5_9I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R13Certificates (CA2_5_9I1R13CertificateIndex a)).output
lemma CA2_5_9I1R13Terms_sound (a : PairSlot) :
    (CA2_5_9I1R13Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R13Certificates_valid
    (CA2_5_9I1R13CertificateIndex a) (CA2_5_9I1R13P_sound a)
def CA2_5_9I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R13Entropy_sound : CA2_5_9I1R13Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R13Value CA2_5_9I1R13Terms CA2_5_9I1R13Terms_sound) (by decide +kernel)
def CA2_5_9I1R13Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R13Mass_sound : CA2_5_9I1R13Mass.Encloses (∑ a, CA2_5_9I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R13P CA2_5_9I1R13Value CA2_5_9I1R13P_sound) (by decide +kernel)
def CA2_5_9I1R13MassTerm : Ball := .exact 0
lemma CA2_5_9I1R13MassTerm_sound : CA2_5_9I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R13Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I1R13Mass_sound)
def CA2_5_9I1R13H : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R13H_sound : CA2_5_9I1R13H.Encloses (homogeneousEntropy CA2_5_9I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R13Value CA2_5_9I1R13MassTerm_sound CA2_5_9I1R13Entropy_sound) (by decide +kernel)
def CA2_5_9I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA2_5_9I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA2_5_9I1R14Raw_sound (a : PairSlot) :
    (CA2_5_9I1R14Raw a).Encloses (CA2_5_9I1R14Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA2_5_9I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I1R14Certificates_valid :
    CA2_5_9I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R14Certificates (CA2_5_9I1R14CertificateIndex a)).input
lemma CA2_5_9I1R14P_check : ∀ a : PairSlot, contains (CA2_5_9I1R14Raw a) (CA2_5_9I1R14P a) = true := by
  decide +kernel
lemma CA2_5_9I1R14P_sound (a : PairSlot) :
    (CA2_5_9I1R14P a).Encloses (CA2_5_9I1R14Value a) :=
  contains_sound (CA2_5_9I1R14Raw_sound a) (CA2_5_9I1R14P_check a)
def CA2_5_9I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R14Certificates (CA2_5_9I1R14CertificateIndex a)).output
lemma CA2_5_9I1R14Terms_sound (a : PairSlot) :
    (CA2_5_9I1R14Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R14Certificates_valid
    (CA2_5_9I1R14CertificateIndex a) (CA2_5_9I1R14P_sound a)
def CA2_5_9I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R14Entropy_sound : CA2_5_9I1R14Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R14Value CA2_5_9I1R14Terms CA2_5_9I1R14Terms_sound) (by decide +kernel)
def CA2_5_9I1R14Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R14Mass_sound : CA2_5_9I1R14Mass.Encloses (∑ a, CA2_5_9I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R14P CA2_5_9I1R14Value CA2_5_9I1R14P_sound) (by decide +kernel)
def CA2_5_9I1R14MassTerm : Ball := .exact 0
lemma CA2_5_9I1R14MassTerm_sound : CA2_5_9I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R14Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I1R14Mass_sound)
def CA2_5_9I1R14H : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R14H_sound : CA2_5_9I1R14H.Encloses (homogeneousEntropy CA2_5_9I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R14Value CA2_5_9I1R14MassTerm_sound CA2_5_9I1R14Entropy_sound) (by decide +kernel)
def CA2_5_9I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA2_5_9I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA2_5_9I1R15Raw_sound (a : PairSlot) :
    (CA2_5_9I1R15Raw a).Encloses (CA2_5_9I1R15Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA2_5_9I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I1R15Certificates_valid :
    CA2_5_9I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R15Certificates (CA2_5_9I1R15CertificateIndex a)).input
lemma CA2_5_9I1R15P_check : ∀ a : PairSlot, contains (CA2_5_9I1R15Raw a) (CA2_5_9I1R15P a) = true := by
  decide +kernel
lemma CA2_5_9I1R15P_sound (a : PairSlot) :
    (CA2_5_9I1R15P a).Encloses (CA2_5_9I1R15Value a) :=
  contains_sound (CA2_5_9I1R15Raw_sound a) (CA2_5_9I1R15P_check a)
def CA2_5_9I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R15Certificates (CA2_5_9I1R15CertificateIndex a)).output
lemma CA2_5_9I1R15Terms_sound (a : PairSlot) :
    (CA2_5_9I1R15Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R15Certificates_valid
    (CA2_5_9I1R15CertificateIndex a) (CA2_5_9I1R15P_sound a)
def CA2_5_9I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R15Entropy_sound : CA2_5_9I1R15Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R15Value CA2_5_9I1R15Terms CA2_5_9I1R15Terms_sound) (by decide +kernel)
def CA2_5_9I1R15Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R15Mass_sound : CA2_5_9I1R15Mass.Encloses (∑ a, CA2_5_9I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R15P CA2_5_9I1R15Value CA2_5_9I1R15P_sound) (by decide +kernel)
def CA2_5_9I1R15MassTerm : Ball := .exact 0
lemma CA2_5_9I1R15MassTerm_sound : CA2_5_9I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R15Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I1R15Mass_sound)
def CA2_5_9I1R15H : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R15H_sound : CA2_5_9I1R15H.Encloses (homogeneousEntropy CA2_5_9I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R15Value CA2_5_9I1R15MassTerm_sound CA2_5_9I1R15Entropy_sound) (by decide +kernel)
def CA2_5_9I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA2_5_9I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA2_5_9I1R16Raw_sound (a : PairSlot) :
    (CA2_5_9I1R16Raw a).Encloses (CA2_5_9I1R16Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA2_5_9I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I1R16Certificates_valid :
    CA2_5_9I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R16Certificates (CA2_5_9I1R16CertificateIndex a)).input
lemma CA2_5_9I1R16P_check : ∀ a : PairSlot, contains (CA2_5_9I1R16Raw a) (CA2_5_9I1R16P a) = true := by
  decide +kernel
lemma CA2_5_9I1R16P_sound (a : PairSlot) :
    (CA2_5_9I1R16P a).Encloses (CA2_5_9I1R16Value a) :=
  contains_sound (CA2_5_9I1R16Raw_sound a) (CA2_5_9I1R16P_check a)
def CA2_5_9I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I1R16Certificates (CA2_5_9I1R16CertificateIndex a)).output
lemma CA2_5_9I1R16Terms_sound (a : PairSlot) :
    (CA2_5_9I1R16Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1R16Certificates_valid
    (CA2_5_9I1R16CertificateIndex a) (CA2_5_9I1R16P_sound a)
def CA2_5_9I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R16Entropy_sound : CA2_5_9I1R16Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I1R16Value CA2_5_9I1R16Terms CA2_5_9I1R16Terms_sound) (by decide +kernel)
def CA2_5_9I1R16Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R16Mass_sound : CA2_5_9I1R16Mass.Encloses (∑ a, CA2_5_9I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I1R16P CA2_5_9I1R16Value CA2_5_9I1R16P_sound) (by decide +kernel)
def CA2_5_9I1R16MassTerm : Ball := .exact 0
lemma CA2_5_9I1R16MassTerm_sound : CA2_5_9I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1R16Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I1R16Mass_sound)
def CA2_5_9I1R16H : Ball := ⟨0, 0⟩
lemma CA2_5_9I1R16H_sound : CA2_5_9I1R16H.Encloses (homogeneousEntropy CA2_5_9I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1R16Value CA2_5_9I1R16MassTerm_sound CA2_5_9I1R16Entropy_sound) (by decide +kernel)
def CA2_5_9I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_5_9I1R0H
  | 1 => CA2_5_9I1R1H
  | 2 => CA2_5_9I1R2H
  | 3 => CA2_5_9I1R3H
  | 4 => CA2_5_9I1R4H
  | 5 => CA2_5_9I1R5H
  | 6 => CA2_5_9I1R6H
  | 7 => CA2_5_9I1R7H
  | 8 => CA2_5_9I1R8H
  | 9 => CA2_5_9I1R9H
  | 10 => CA2_5_9I1R10H
  | 11 => CA2_5_9I1R11H
  | 12 => CA2_5_9I1R12H
  | 13 => CA2_5_9I1R13H
  | 14 => CA2_5_9I1R14H
  | 15 => CA2_5_9I1R15H
  | 16 => CA2_5_9I1R16H
  | _ => (.exact 0)
lemma CA2_5_9I1ResidualEntropies_sound (k : Fin 17) :
    (CA2_5_9I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_5_9I1R0H_sound
  · exact CA2_5_9I1R1H_sound
  · exact CA2_5_9I1R2H_sound
  · exact CA2_5_9I1R3H_sound
  · exact CA2_5_9I1R4H_sound
  · exact CA2_5_9I1R5H_sound
  · exact CA2_5_9I1R6H_sound
  · exact CA2_5_9I1R7H_sound
  · exact CA2_5_9I1R8H_sound
  · exact CA2_5_9I1R9H_sound
  · exact CA2_5_9I1R10H_sound
  · exact CA2_5_9I1R11H_sound
  · exact CA2_5_9I1R12H_sound
  · exact CA2_5_9I1R13H_sound
  · exact CA2_5_9I1R14H_sound
  · exact CA2_5_9I1R15H_sound
  · exact CA2_5_9I1R16H_sound
def CA2_5_9I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
lemma CA2_5_9I1Singles_sound (u : Shape) (hu : u ∈ below (shape 2 5 9))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA2_5_9I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A2_5_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 0 8) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 1 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 4 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 5 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 0 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 0 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 5 1) by decide +kernel) hd |>.elim
def CA2_5_9I1Singleton : Ball := ⟨0, 0⟩
lemma CA2_5_9I1Singleton_sound : CA2_5_9I1Singleton.Encloses
    (singletonEntropy (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA2_5_9I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_5_9Law_sound u) CA2_5_9I1Singles_sound) (by decide +kernel)
def CA2_5_9I1Group : Ball := ⟨(105351913892130676205833539769721 / 100000000000000000000000000000000), (84174611011 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I1Group_sound : CA2_5_9I1Group.Encloses
    (groupedEntropy (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_5_9I1Singleton_sound
    (finSumBall_sound 17 CA2_5_9I1ResidualEntropies _ CA2_5_9I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA2_5_9I1H : Ball := ⟨(117889810744855596455560513998131 / 100000000000000000000000000000000), (517634851031 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I1_sound : CA2_5_9I1H.Encloses (stageACapacity (shape 2 5 9) 1) := by
  have hb := contains_sound (Ball.add_sound CA2_5_9I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA2_5_9I1Group_sound)))
    (show contains (.add CA2_5_9I1PairH (.neg (.mul (.exact 2) CA2_5_9I1Group))) CA2_5_9I1H = true by decide +kernel)
  unfold CA2_5_9I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
