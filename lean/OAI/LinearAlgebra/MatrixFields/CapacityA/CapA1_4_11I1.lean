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
def CA1_4_11I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 4 11)) (shape 1 4 11) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA1_4_11I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 4 11) A1_4_11Law 1 a
lemma CA1_4_11I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA1_4_11I1PairRaw a).Encloses (CA1_4_11I1PairValue a) := by
  exact stageAPairBall_sound (shape 1 4 11) (by decide +kernel) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (fun u _ => A1_4_11Law_sound u) 1 a
def CA1_4_11I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(11664977189338182042318946841 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(34046911231915542261283174941 / 2000000000000000000000000000000), (123507753 / 20000000000000000000000000000000)⟩ ⟨(-583745869010948486140178427050387 / 100000000000000000000000000000000), (42351647503 / 20000000000000000000000000000000)⟩ ⟨-9, 11664977189338182042318946841, 7812500000000000000000000000⟩,
   .log ⟨(1432041275913219638258759429603 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(6080546489257217219713937617783 / 100000000000000000000000000000000), (1212986169 / 50000000000000000000000000000000)⟩ ⟨(-106151732347582358530726446483411 / 25000000000000000000000000000000), (84703295081 / 50000000000000000000000000000000)⟩ ⟨-7, 1432041275913219638258759429603, 781250000000000000000000000000⟩,
   .log ⟨(72646759446330440509803789261 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(18987449595068623982609898379 / 2000000000000000000000000000000), (338438109 / 100000000000000000000000000000000)⟩ ⟨(-130683390007891982652220310067249 / 20000000000000000000000000000000), (232934061889 / 100000000000000000000000000000000)⟩ ⟨-10, 72646759446330440509803789261, 48828125000000000000000000000⟩,
   .log ⟨(15442796055875565115581455813 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(135522624707020123450557332547 / 100000000000000000000000000000000), (1144549 / 2500000000000000000000000000000)⟩ ⟨(-27424321390834174728384894737699 / 3125000000000000000000000000000), (296461538037 / 100000000000000000000000000000000)⟩ ⟨-13, 15442796055875565115581455813, 12207031250000000000000000000⟩,
   .log ⟨(858584694521010948985622169 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(8633891199949041081299899313 / 20000000000000000000000000000000), (7272501 / 50000000000000000000000000000000)⟩ ⟨(-201119150039489921776711304601741 / 20000000000000000000000000000000), (338813202221 / 100000000000000000000000000000000)⟩ ⟨-15, 858584694521010948985622169, 610351562500000000000000000⟩,
   .log ⟨(137888861593042178984912356271 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1625249205084484155605066075167 / 100000000000000000000000000000000), (583982059 / 100000000000000000000000000000000)⟩ ⟨(-589333027449728988868004776662241 / 100000000000000000000000000000000), (42351647511 / 20000000000000000000000000000000)⟩ ⟨-9, 137888861593042178984912356271, 97656250000000000000000000000⟩,
   .log ⟨(4904076801820583064126827285721 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩ ⟨(7393149139095214348214785328203 / 50000000000000000000000000000000), (3115436013 / 50000000000000000000000000000000)⟩ ⟨(-301510332642041467290155459800419 / 100000000000000000000000000000000), (63527471263 / 50000000000000000000000000000000)⟩ ⟨-5, 4904076801820583064126827285721, 3125000000000000000000000000000⟩,
   .log ⟨(482992777307967784909064602021 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1287881830273238117754698756549 / 50000000000000000000000000000000), (115062413 / 12500000000000000000000000000000)⟩ ⟨(-533292376524319641417441294797923 / 100000000000000000000000000000000), (4764560339 / 2500000000000000000000000000000)⟩ ⟨-8, 482992777307967784909064602021, 390625000000000000000000000000⟩,
   .log ⟨(1593584057043965232702681183837 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(6596138559921701501728336143231 / 100000000000000000000000000000000), (2362181893 / 100000000000000000000000000000000)⟩ ⟨(-82783691651098405640700492998221 / 20000000000000000000000000000000), (74115383141 / 50000000000000000000000000000000)⟩ ⟨-6, 1593584057043965232702681183837, 1562500000000000000000000000000⟩,
   .log ⟨(150556659524634014410605017567 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(978405396237944661934025336967 / 100000000000000000000000000000000), (87674439 / 25000000000000000000000000000000)⟩ ⟨(-649858597638358468854867514767903 / 100000000000000000000000000000000), (232934061841 / 100000000000000000000000000000000)⟩ ⟨-10, 150556659524634014410605017567, 97656250000000000000000000000⟩,
   .log ⟨(5469334159468324195833199519871 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩ ⟨(397348945626970979222896666589 / 2500000000000000000000000000000), (217158107 / 3125000000000000000000000000000)⟩ ⟨(-58120266056751215685901505382233 / 20000000000000000000000000000000), (25410988489 / 20000000000000000000000000000000)⟩ ⟨-5, 5469334159468324195833199519871, 3125000000000000000000000000000⟩,
   .log ⟨(2786939030381170203143835961 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(123719799583554885385098337861 / 100000000000000000000000000000000), (41311021 / 100000000000000000000000000000000)⟩ ⟨(-13872724501107235369479078733497 / 1562500000000000000000000000000), (148230769369 / 50000000000000000000000000000000)⟩ ⟨-13, 2786939030381170203143835961, 2441406250000000000000000000⟩,
   .log ⟨(25388704041102548051955395779 / 5000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2682514024359832963349767317973 / 100000000000000000000000000000000), (241932029 / 25000000000000000000000000000000)⟩ ⟨(-52828888391014939480636882266497 / 10000000000000000000000000000000), (190582413737 / 100000000000000000000000000000000)⟩ ⟨-8, 25388704041102548051955395779, 19531250000000000000000000000⟩,
   .log ⟨(18494448703007788912267876648421 / 100000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩ ⟨(31213073105727158527369908172863 / 100000000000000000000000000000000), (7832703747 / 50000000000000000000000000000000)⟩ ⟨(-168769956904154242112485802872997 / 100000000000000000000000000000000), (84703294931 / 100000000000000000000000000000000)⟩ ⟨-3, 18494448703007788912267876648421, 12500000000000000000000000000000⟩]
lemma CA1_4_11I1PairCertificates_valid :
    CA1_4_11I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 1, 4 => 1
  | 0, 0, 2, 2 => 2
  | 0, 0, 2, 3 => 3
  | 0, 0, 3, 2 => 3
  | 0, 0, 3, 3 => 4
  | 0, 0, 4, 1 => 1
  | 0, 0, 5, 0 => 5
  | 0, 0, 0, 5 => 5
  | 1, 0, 0, 4 => 6
  | 1, 0, 1, 2 => 7
  | 1, 0, 1, 3 => 8
  | 1, 0, 2, 1 => 7
  | 1, 0, 3, 1 => 8
  | 1, 0, 4, 0 => 6
  | 0, 1, 0, 4 => 6
  | 0, 1, 1, 2 => 7
  | 0, 1, 1, 3 => 8
  | 0, 1, 2, 1 => 7
  | 0, 1, 3, 1 => 8
  | 0, 1, 4, 0 => 6
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
  | 4, 0, 0, 1 => 6
  | 4, 0, 1, 0 => 6
  | 2, 1, 0, 1 => 7
  | 2, 1, 1, 0 => 7
  | 3, 1, 0, 1 => 8
  | 3, 1, 1, 0 => 8
  | 1, 2, 0, 1 => 7
  | 1, 2, 1, 0 => 7
  | 1, 3, 0, 1 => 8
  | 1, 3, 1, 0 => 8
  | 0, 4, 0, 1 => 6
  | 0, 4, 1, 0 => 6
  | 0, 5, 0, 0 => 5
  | 1, 4, 0, 0 => 1
  | 2, 2, 0, 0 => 2
  | 2, 3, 0, 0 => 3
  | 3, 2, 0, 0 => 3
  | 3, 3, 0, 0 => 4
  | 4, 1, 0, 0 => 1
  | 5, 0, 0, 0 => 5
  | _, _, _, _ => 0
def CA1_4_11I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1PairCertificates (CA1_4_11I1PairCertificateIndex a)).input
lemma CA1_4_11I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((0,0),(k,l))) (CA1_4_11I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((0,1),(k,l))) (CA1_4_11I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((0,2),(k,l))) (CA1_4_11I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((0,3),(k,l))) (CA1_4_11I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((0,4),(k,l))) (CA1_4_11I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((0,5),(k,l))) (CA1_4_11I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((1,0),(k,l))) (CA1_4_11I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((1,1),(k,l))) (CA1_4_11I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((1,2),(k,l))) (CA1_4_11I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((1,3),(k,l))) (CA1_4_11I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((1,4),(k,l))) (CA1_4_11I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((1,5),(k,l))) (CA1_4_11I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((2,0),(k,l))) (CA1_4_11I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((2,1),(k,l))) (CA1_4_11I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((2,2),(k,l))) (CA1_4_11I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((2,3),(k,l))) (CA1_4_11I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((2,4),(k,l))) (CA1_4_11I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((2,5),(k,l))) (CA1_4_11I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((3,0),(k,l))) (CA1_4_11I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((3,1),(k,l))) (CA1_4_11I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((3,2),(k,l))) (CA1_4_11I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((3,3),(k,l))) (CA1_4_11I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((3,4),(k,l))) (CA1_4_11I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((3,5),(k,l))) (CA1_4_11I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((4,0),(k,l))) (CA1_4_11I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((4,1),(k,l))) (CA1_4_11I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((4,2),(k,l))) (CA1_4_11I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((4,3),(k,l))) (CA1_4_11I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((4,4),(k,l))) (CA1_4_11I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((4,5),(k,l))) (CA1_4_11I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((5,0),(k,l))) (CA1_4_11I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((5,1),(k,l))) (CA1_4_11I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((5,2),(k,l))) (CA1_4_11I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((5,3),(k,l))) (CA1_4_11I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((5,4),(k,l))) (CA1_4_11I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA1_4_11I1PairRaw ((5,5),(k,l))) (CA1_4_11I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA1_4_11I1PairP_check (a : PairSlot × PairSlot) : contains (CA1_4_11I1PairRaw a) (CA1_4_11I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA1_4_11I1PairP_check_0_0 k l) (CA1_4_11I1PairP_check_0_1 k l) (CA1_4_11I1PairP_check_0_2 k l) (CA1_4_11I1PairP_check_0_3 k l) (CA1_4_11I1PairP_check_0_4 k l) (CA1_4_11I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA1_4_11I1PairP_check_1_0 k l) (CA1_4_11I1PairP_check_1_1 k l) (CA1_4_11I1PairP_check_1_2 k l) (CA1_4_11I1PairP_check_1_3 k l) (CA1_4_11I1PairP_check_1_4 k l) (CA1_4_11I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA1_4_11I1PairP_check_2_0 k l) (CA1_4_11I1PairP_check_2_1 k l) (CA1_4_11I1PairP_check_2_2 k l) (CA1_4_11I1PairP_check_2_3 k l) (CA1_4_11I1PairP_check_2_4 k l) (CA1_4_11I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA1_4_11I1PairP_check_3_0 k l) (CA1_4_11I1PairP_check_3_1 k l) (CA1_4_11I1PairP_check_3_2 k l) (CA1_4_11I1PairP_check_3_3 k l) (CA1_4_11I1PairP_check_3_4 k l) (CA1_4_11I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA1_4_11I1PairP_check_4_0 k l) (CA1_4_11I1PairP_check_4_1 k l) (CA1_4_11I1PairP_check_4_2 k l) (CA1_4_11I1PairP_check_4_3 k l) (CA1_4_11I1PairP_check_4_4 k l) (CA1_4_11I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA1_4_11I1PairP_check_5_0 k l) (CA1_4_11I1PairP_check_5_1 k l) (CA1_4_11I1PairP_check_5_2 k l) (CA1_4_11I1PairP_check_5_3 k l) (CA1_4_11I1PairP_check_5_4 k l) (CA1_4_11I1PairP_check_5_5 k l)
lemma CA1_4_11I1PairP_sound (a : PairSlot × PairSlot) :
    (CA1_4_11I1PairP a).Encloses (CA1_4_11I1PairValue a) :=
  contains_sound (CA1_4_11I1PairRaw_sound a) (CA1_4_11I1PairP_check a)
def CA1_4_11I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1PairCertificates (CA1_4_11I1PairCertificateIndex a)).output
lemma CA1_4_11I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA1_4_11I1PairTerms a).Encloses (Foundation.entropyTerm (CA1_4_11I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1PairCertificates_valid
    (CA1_4_11I1PairCertificateIndex a) (CA1_4_11I1PairP_sound a)
def CA1_4_11I1PairEntropy : Ball := ⟨(315335814479301831357444261227387 / 100000000000000000000000000000000), (13046053457 / 10000000000000000000000000000000)⟩
lemma CA1_4_11I1PairEntropy_sound : CA1_4_11I1PairEntropy.Encloses (Foundation.finiteEntropy CA1_4_11I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA1_4_11I1PairValue CA1_4_11I1PairTerms CA1_4_11I1PairTerms_sound) (by decide +kernel)
def CA1_4_11I1PairMass : Ball := ⟨(100000000000000000000000000000001 / 100000000000000000000000000000000), (419 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I1PairMass_sound : CA1_4_11I1PairMass.Encloses (∑ a, CA1_4_11I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA1_4_11I1PairP CA1_4_11I1PairValue CA1_4_11I1PairP_sound) (by decide +kernel)
def CA1_4_11I1PairMassTermLogWitness : LogWitness := ⟨0, 100000000000000000000000000000001, 100000000000000000000000000000000⟩
def CA1_4_11I1PairMassTermLog : Ball := ⟨(1 / 100000000000000000000000000000000), (21175824101 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I1PairMassTermLog_sound : CA1_4_11I1PairMassTermLog.Encloses (Real.log ((∑ a, CA1_4_11I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_4_11I1PairMass_sound) (w := CA1_4_11I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_4_11I1PairMassTerm : Ball := ⟨(-1 / 100000000000000000000000000000000), (10587912051 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I1PairMassTerm_sound : CA1_4_11I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA1_4_11I1PairMass_sound) CA1_4_11I1PairMassTermLog_sound) (by decide +kernel)
def CA1_4_11I1PairH : Ball := ⟨(78833953619825457839361065306847 / 25000000000000000000000000000000), (9477272417 / 6250000000000000000000000000000)⟩
lemma CA1_4_11I1PairH_sound : CA1_4_11I1PairH.Encloses (homogeneousEntropy CA1_4_11I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1PairValue CA1_4_11I1PairMassTerm_sound CA1_4_11I1PairEntropy_sound) (by decide +kernel)

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
def CA1_4_11I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA1_4_11I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA1_4_11I1R0Raw_sound (a : PairSlot) :
    (CA1_4_11I1R0Raw a).Encloses (CA1_4_11I1R0Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA1_4_11I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(11649529080832680885096798031 / 500000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(437945679318023839001681305581 / 5000000000000000000000000000000), (1726818641 / 50000000000000000000000000000000)⟩ ⟨(-375934234147360499072534355300923 / 100000000000000000000000000000000), (148230766209 / 100000000000000000000000000000000)⟩ ⟨-6, 11649529080832680885096798031, 7812500000000000000000000000⟩]
lemma CA1_4_11I1R0Certificates_valid :
    CA1_4_11I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_4_11I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R0Certificates (CA1_4_11I1R0CertificateIndex a)).input
lemma CA1_4_11I1R0P_check : ∀ a : PairSlot, contains (CA1_4_11I1R0Raw a) (CA1_4_11I1R0P a) = true := by
  decide +kernel
lemma CA1_4_11I1R0P_sound (a : PairSlot) :
    (CA1_4_11I1R0P a).Encloses (CA1_4_11I1R0Value a) :=
  contains_sound (CA1_4_11I1R0Raw_sound a) (CA1_4_11I1R0P_check a)
def CA1_4_11I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R0Certificates (CA1_4_11I1R0CertificateIndex a)).output
lemma CA1_4_11I1R0Terms_sound (a : PairSlot) :
    (CA1_4_11I1R0Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R0Certificates_valid
    (CA1_4_11I1R0CertificateIndex a) (CA1_4_11I1R0P_sound a)
def CA1_4_11I1R0Entropy : Ball := ⟨(437945679318023839001681305581 / 5000000000000000000000000000000), (1726818641 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I1R0Entropy_sound : CA1_4_11I1R0Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R0Value CA1_4_11I1R0Terms CA1_4_11I1R0Terms_sound) (by decide +kernel)
def CA1_4_11I1R0Mass : Ball := ⟨(11649529080832680885096798031 / 500000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
lemma CA1_4_11I1R0Mass_sound : CA1_4_11I1R0Mass.Encloses (∑ a, CA1_4_11I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R0P CA1_4_11I1R0Value CA1_4_11I1R0P_sound) (by decide +kernel)
def CA1_4_11I1R0MassTermLogWitness : LogWitness := ⟨-6, 11649529080832680885096798031, 7812500000000000000000000000⟩
def CA1_4_11I1R0MassTermLog : Ball := ⟨(-375934234147360499072534355300923 / 100000000000000000000000000000000), (148230766209 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I1R0MassTermLog_sound : CA1_4_11I1R0MassTermLog.Encloses (Real.log ((∑ a, CA1_4_11I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_4_11I1R0Mass_sound) (w := CA1_4_11I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_4_11I1R0MassTerm : Ball := ⟨(437945679318023839001681305581 / 5000000000000000000000000000000), (1726818641 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I1R0MassTerm_sound : CA1_4_11I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_4_11I1R0Mass_sound) CA1_4_11I1R0MassTermLog_sound) (by decide +kernel)
def CA1_4_11I1R0H : Ball := ⟨0, (1726818641 / 25000000000000000000000000000000)⟩
lemma CA1_4_11I1R0H_sound : CA1_4_11I1R0H.Encloses (homogeneousEntropy CA1_4_11I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R0Value CA1_4_11I1R0MassTerm_sound CA1_4_11I1R0Entropy_sound) (by decide +kernel)
def CA1_4_11I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA1_4_11I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA1_4_11I1R1Raw_sound (a : PairSlot) :
    (CA1_4_11I1R1Raw a).Encloses (CA1_4_11I1R1Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA1_4_11I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1415711825578658801751429150071 / 12500000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩ ⟨(3083556523177856507528997814397 / 12500000000000000000000000000000), (2398309139 / 20000000000000000000000000000000)⟩ ⟨(-217809618275773177236479388037759 / 100000000000000000000000000000000), (105879118671 / 100000000000000000000000000000000)⟩ ⟨-4, 1415711825578658801751429150071, 781250000000000000000000000000⟩]
lemma CA1_4_11I1R1Certificates_valid :
    CA1_4_11I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_4_11I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R1Certificates (CA1_4_11I1R1CertificateIndex a)).input
lemma CA1_4_11I1R1P_check : ∀ a : PairSlot, contains (CA1_4_11I1R1Raw a) (CA1_4_11I1R1P a) = true := by
  decide +kernel
lemma CA1_4_11I1R1P_sound (a : PairSlot) :
    (CA1_4_11I1R1P a).Encloses (CA1_4_11I1R1Value a) :=
  contains_sound (CA1_4_11I1R1Raw_sound a) (CA1_4_11I1R1P_check a)
def CA1_4_11I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R1Certificates (CA1_4_11I1R1CertificateIndex a)).output
lemma CA1_4_11I1R1Terms_sound (a : PairSlot) :
    (CA1_4_11I1R1Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R1Certificates_valid
    (CA1_4_11I1R1CertificateIndex a) (CA1_4_11I1R1P_sound a)
def CA1_4_11I1R1Entropy : Ball := ⟨(3083556523177856507528997814397 / 6250000000000000000000000000000), (2398309139 / 10000000000000000000000000000000)⟩
lemma CA1_4_11I1R1Entropy_sound : CA1_4_11I1R1Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R1Value CA1_4_11I1R1Terms CA1_4_11I1R1Terms_sound) (by decide +kernel)
def CA1_4_11I1R1Mass : Ball := ⟨(1415711825578658801751429150071 / 6250000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I1R1Mass_sound : CA1_4_11I1R1Mass.Encloses (∑ a, CA1_4_11I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R1P CA1_4_11I1R1Value CA1_4_11I1R1P_sound) (by decide +kernel)
def CA1_4_11I1R1MassTermLogWitness : LogWitness := ⟨-3, 1415711825578658801751429150071, 781250000000000000000000000000⟩
def CA1_4_11I1R1MassTermLog : Ball := ⟨(-148494900219778646294756194987429 / 100000000000000000000000000000000), (21175823747 / 25000000000000000000000000000000)⟩
lemma CA1_4_11I1R1MassTermLog_sound : CA1_4_11I1R1MassTermLog.Encloses (Real.log ((∑ a, CA1_4_11I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_4_11I1R1Mass_sound) (w := CA1_4_11I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_4_11I1R1MassTerm : Ball := ⟨(3363615780468217751509662805569 / 10000000000000000000000000000000), (4796618277 / 25000000000000000000000000000000)⟩
lemma CA1_4_11I1R1MassTerm_sound : CA1_4_11I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_4_11I1R1Mass_sound) CA1_4_11I1R1MassTermLog_sound) (by decide +kernel)
def CA1_4_11I1R1H : Ball := ⟨(7850373283081763302683668487331 / 50000000000000000000000000000000), (21584782249 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I1R1H_sound : CA1_4_11I1R1H.Encloses (homogeneousEntropy CA1_4_11I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R1Value CA1_4_11I1R1MassTerm_sound CA1_4_11I1R1Entropy_sound) (by decide +kernel)
def CA1_4_11I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA1_4_11I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA1_4_11I1R2Raw_sound (a : PairSlot) :
    (CA1_4_11I1R2Raw a).Encloses (CA1_4_11I1R2Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA1_4_11I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(223940389815138067251494298067 / 2500000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(10805867789225661561870460519403 / 50000000000000000000000000000000), (948424451 / 10000000000000000000000000000000)⟩ ⟨(-15079163195708386909004244644217 / 6250000000000000000000000000000), (21175823741 / 20000000000000000000000000000000)⟩ ⟨-4, 223940389815138067251494298067, 156250000000000000000000000000⟩,
   .log ⟨(209189197543782672972939077581 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(400253574441421611996235844733 / 10000000000000000000000000000000), (354380291 / 25000000000000000000000000000000)⟩ ⟨(-478339200997281105739975070413043 / 100000000000000000000000000000000), (169406589941 / 100000000000000000000000000000000)⟩ ⟨-7, 209189197543782672972939077581, 195312500000000000000000000000⟩,
   .log ⟨(15224332591794269613006245759661 / 50000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩ ⟨(36207361219350480702515376712927 / 100000000000000000000000000000000), (9671633527 / 50000000000000000000000000000000)⟩ ⟨(-11891280291283773157913279044349 / 10000000000000000000000000000000), (63527471189 / 100000000000000000000000000000000)⟩ ⟨-2, 15224332591794269613006245759661, 12500000000000000000000000000000⟩]
lemma CA1_4_11I1R2Certificates_valid :
    CA1_4_11I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_4_11I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R2Certificates (CA1_4_11I1R2CertificateIndex a)).input
lemma CA1_4_11I1R2P_check : ∀ a : PairSlot, contains (CA1_4_11I1R2Raw a) (CA1_4_11I1R2P a) = true := by
  decide +kernel
lemma CA1_4_11I1R2P_sound (a : PairSlot) :
    (CA1_4_11I1R2P a).Encloses (CA1_4_11I1R2Value a) :=
  contains_sound (CA1_4_11I1R2Raw_sound a) (CA1_4_11I1R2P_check a)
def CA1_4_11I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R2Certificates (CA1_4_11I1R2CertificateIndex a)).output
lemma CA1_4_11I1R2Terms_sound (a : PairSlot) :
    (CA1_4_11I1R2Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R2Certificates_valid
    (CA1_4_11I1R2CertificateIndex a) (CA1_4_11I1R2P_sound a)
def CA1_4_11I1R2Entropy : Ball := ⟨(87435903865081559189921935685199 / 100000000000000000000000000000000), (20573399201 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I1R2Entropy_sound : CA1_4_11I1R2Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R2Value CA1_4_11I1R2Terms CA1_4_11I1R2Terms_sound) (by decide +kernel)
def CA1_4_11I1R2Mass : Ball := ⟨(5003740994914984598991554798533 / 10000000000000000000000000000000), (103 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I1R2Mass_sound : CA1_4_11I1R2Mass.Encloses (∑ a, CA1_4_11I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R2P CA1_4_11I1R2Value CA1_4_11I1R2P_sound) (by decide +kernel)
def CA1_4_11I1R2MassTermLogWitness : LogWitness := ⟨-1, 5003740994914984598991554798533, 5000000000000000000000000000000⟩
def CA1_4_11I1R2MassTermLog : Ball := ⟨(-34619963066913570366131252995201 / 50000000000000000000000000000000), (42351647571 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I1R2MassTermLog_sound : CA1_4_11I1R2MassTermLog.Encloses (Real.log ((∑ a, CA1_4_11I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_4_11I1R2Mass_sound) (w := CA1_4_11I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_4_11I1R2MassTerm : Ball := ⟨(34645865688071626023959378116581 / 100000000000000000000000000000000), (21191667587 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I1R2MassTerm_sound : CA1_4_11I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_4_11I1R2Mass_sound) CA1_4_11I1R2MassTermLog_sound) (by decide +kernel)
def CA1_4_11I1R2H : Ball := ⟨(26395019088504966582981278784309 / 50000000000000000000000000000000), (62338465989 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I1R2H_sound : CA1_4_11I1R2H.Encloses (homogeneousEntropy CA1_4_11I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R2Value CA1_4_11I1R2MassTerm_sound CA1_4_11I1R2Entropy_sound) (by decide +kernel)
def CA1_4_11I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA1_4_11I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA1_4_11I1R3Raw_sound (a : PairSlot) :
    (CA1_4_11I1R3Raw a).Encloses (CA1_4_11I1R3Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA1_4_11I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(137888861593042178984912356271 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2868189307593617450192719616833 / 100000000000000000000000000000000), (1051167699 / 100000000000000000000000000000000)⟩ ⟨(-520018309393734457926281583611911 / 100000000000000000000000000000000), (19058241369 / 10000000000000000000000000000000)⟩ ⟨-8, 137888861593042178984912356271, 97656250000000000000000000000⟩,
   .log ⟨(4904076801820583064126827285721 / 50000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩ ⟨(22774102539518115754746011166397 / 100000000000000000000000000000000), (2076957341 / 20000000000000000000000000000000)⟩ ⟨(-232195614586046936348432266750089 / 100000000000000000000000000000000), (105879118833 / 100000000000000000000000000000000)⟩ ⟨-4, 4904076801820583064126827285721, 3125000000000000000000000000000⟩,
   .log ⟨(482992777307967784909064602021 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(4481957157449281667465669218783 / 100000000000000000000000000000000), (818221603 / 50000000000000000000000000000000)⟩ ⟨(-463977658468325110475718101747593 / 100000000000000000000000000000000), (169406589877 / 100000000000000000000000000000000)⟩ ⟨-7, 482992777307967784909064602021, 390625000000000000000000000000⟩]
lemma CA1_4_11I1R3Certificates_valid :
    CA1_4_11I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_4_11I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R3Certificates (CA1_4_11I1R3CertificateIndex a)).input
lemma CA1_4_11I1R3P_check : ∀ a : PairSlot, contains (CA1_4_11I1R3Raw a) (CA1_4_11I1R3P a) = true := by
  decide +kernel
lemma CA1_4_11I1R3P_sound (a : PairSlot) :
    (CA1_4_11I1R3P a).Encloses (CA1_4_11I1R3Value a) :=
  contains_sound (CA1_4_11I1R3Raw_sound a) (CA1_4_11I1R3P_check a)
def CA1_4_11I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R3Certificates (CA1_4_11I1R3CertificateIndex a)).output
lemma CA1_4_11I1R3Terms_sound (a : PairSlot) :
    (CA1_4_11I1R3Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R3Certificates_valid
    (CA1_4_11I1R3CertificateIndex a) (CA1_4_11I1R3P_sound a)
def CA1_4_11I1R3Entropy : Ball := ⟨(30124249004561014872404400002013 / 50000000000000000000000000000000), (1307239761 / 5000000000000000000000000000000)⟩
lemma CA1_4_11I1R3Entropy_sound : CA1_4_11I1R3Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R3Value CA1_4_11I1R3Terms CA1_4_11I1R3Terms_sound) (by decide +kernel)
def CA1_4_11I1R3Mass : Ball := ⟨(1415711825578658801751429150071 / 6250000000000000000000000000000), (3 / 3125000000000000000000000000000)⟩
lemma CA1_4_11I1R3Mass_sound : CA1_4_11I1R3Mass.Encloses (∑ a, CA1_4_11I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R3P CA1_4_11I1R3Value CA1_4_11I1R3P_sound) (by decide +kernel)
def CA1_4_11I1R3MassTermLogWitness : LogWitness := ⟨-3, 1415711825578658801751429150071, 781250000000000000000000000000⟩
def CA1_4_11I1R3MassTermLog : Ball := ⟨(-148494900219778646294756194987429 / 100000000000000000000000000000000), (21175823789 / 25000000000000000000000000000000)⟩
lemma CA1_4_11I1R3MassTermLog_sound : CA1_4_11I1R3MassTermLog.Encloses (Real.log ((∑ a, CA1_4_11I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_4_11I1R3Mass_sound) (w := CA1_4_11I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_4_11I1R3MassTerm : Ball := ⟨(3363615780468217751509662805569 / 10000000000000000000000000000000), (9593236601 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I1R3MassTerm_sound : CA1_4_11I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_4_11I1R3Mass_sound) CA1_4_11I1R3MassTermLog_sound) (by decide +kernel)
def CA1_4_11I1R3H : Ball := ⟨(1663271262777490764357010746771 / 6250000000000000000000000000000), (22665634211 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I1R3H_sound : CA1_4_11I1R3H.Encloses (homogeneousEntropy CA1_4_11I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R3Value CA1_4_11I1R3MassTerm_sound CA1_4_11I1R3Entropy_sound) (by decide +kernel)
def CA1_4_11I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA1_4_11I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA1_4_11I1R4Raw_sound (a : PairSlot) :
    (CA1_4_11I1R4Raw a).Encloses (CA1_4_11I1R4Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA1_4_11I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(858584694521010948985622169 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(8633891199949041081299899313 / 20000000000000000000000000000000), (7272501 / 50000000000000000000000000000000)⟩ ⟨(-201119150039489921776711304601741 / 20000000000000000000000000000000), (338813202221 / 100000000000000000000000000000000)⟩ ⟨-15, 858584694521010948985622169, 610351562500000000000000000⟩,
   .log ⟨(11664977189338182042318946841 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(34046911231915542261283174941 / 2000000000000000000000000000000), (123507753 / 20000000000000000000000000000000)⟩ ⟨(-583745869010948486140178427050387 / 100000000000000000000000000000000), (42351647503 / 20000000000000000000000000000000)⟩ ⟨-9, 11664977189338182042318946841, 7812500000000000000000000000⟩,
   .log ⟨(1432041275913219638258759429603 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(6080546489257217219713937617783 / 100000000000000000000000000000000), (1212986169 / 50000000000000000000000000000000)⟩ ⟨(-106151732347582358530726446483411 / 25000000000000000000000000000000), (84703295081 / 50000000000000000000000000000000)⟩ ⟨-7, 1432041275913219638258759429603, 781250000000000000000000000000⟩,
   .log ⟨(72646759446330440509803789261 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(18987449595068623982609898379 / 2000000000000000000000000000000), (338438109 / 100000000000000000000000000000000)⟩ ⟨(-130683390007891982652220310067249 / 20000000000000000000000000000000), (232934061889 / 100000000000000000000000000000000)⟩ ⟨-10, 72646759446330440509803789261, 48828125000000000000000000000⟩,
   .log ⟨(15442796055875565115581455813 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(135522624707020123450557332547 / 100000000000000000000000000000000), (1144549 / 2500000000000000000000000000000)⟩ ⟨(-27424321390834174728384894737699 / 3125000000000000000000000000000), (296461538037 / 100000000000000000000000000000000)⟩ ⟨-13, 15442796055875565115581455813, 12207031250000000000000000000⟩]
lemma CA1_4_11I1R4Certificates_valid :
    CA1_4_11I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA1_4_11I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R4Certificates (CA1_4_11I1R4CertificateIndex a)).input
lemma CA1_4_11I1R4P_check : ∀ a : PairSlot, contains (CA1_4_11I1R4Raw a) (CA1_4_11I1R4P a) = true := by
  decide +kernel
lemma CA1_4_11I1R4P_sound (a : PairSlot) :
    (CA1_4_11I1R4P a).Encloses (CA1_4_11I1R4Value a) :=
  contains_sound (CA1_4_11I1R4Raw_sound a) (CA1_4_11I1R4P_check a)
def CA1_4_11I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R4Certificates (CA1_4_11I1R4CertificateIndex a)).output
lemma CA1_4_11I1R4Terms_sound (a : PairSlot) :
    (CA1_4_11I1R4Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R4Certificates_valid
    (CA1_4_11I1R4CertificateIndex a) (CA1_4_11I1R4P_sound a)
def CA1_4_11I1R4Entropy : Ball := ⟨(580292205433107218918340063773 / 5000000000000000000000000000000), (88255961 / 2000000000000000000000000000000)⟩
lemma CA1_4_11I1R4Entropy_sound : CA1_4_11I1R4Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R4Value CA1_4_11I1R4Terms CA1_4_11I1R4Terms_sound) (by decide +kernel)
def CA1_4_11I1R4Mass : Ball := ⟨(11649529080832680885096798031 / 500000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I1R4Mass_sound : CA1_4_11I1R4Mass.Encloses (∑ a, CA1_4_11I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R4P CA1_4_11I1R4Value CA1_4_11I1R4P_sound) (by decide +kernel)
def CA1_4_11I1R4MassTermLogWitness : LogWitness := ⟨-6, 11649529080832680885096798031, 7812500000000000000000000000⟩
def CA1_4_11I1R4MassTermLog : Ball := ⟨(-375934234147360499072534355300923 / 100000000000000000000000000000000), (74115383341 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I1R4MassTermLog_sound : CA1_4_11I1R4MassTermLog.Encloses (Real.log ((∑ a, CA1_4_11I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_4_11I1R4Mass_sound) (w := CA1_4_11I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_4_11I1R4MassTerm : Ball := ⟨(437945679318023839001681305581 / 5000000000000000000000000000000), (1726818667 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I1R4MassTerm_sound : CA1_4_11I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_4_11I1R4Mass_sound) CA1_4_11I1R4MassTermLog_sound) (by decide +kernel)
def CA1_4_11I1R4H : Ball := ⟨(8896657882192711244791172387 / 312500000000000000000000000000), (983304423 / 12500000000000000000000000000000)⟩
lemma CA1_4_11I1R4H_sound : CA1_4_11I1R4H.Encloses (homogeneousEntropy CA1_4_11I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R4Value CA1_4_11I1R4MassTerm_sound CA1_4_11I1R4Entropy_sound) (by decide +kernel)
def CA1_4_11I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA1_4_11I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA1_4_11I1R5Raw_sound (a : PairSlot) :
    (CA1_4_11I1R5Raw a).Encloses (CA1_4_11I1R5Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA1_4_11I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R5Certificates_valid :
    CA1_4_11I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R5Certificates (CA1_4_11I1R5CertificateIndex a)).input
lemma CA1_4_11I1R5P_check : ∀ a : PairSlot, contains (CA1_4_11I1R5Raw a) (CA1_4_11I1R5P a) = true := by
  decide +kernel
lemma CA1_4_11I1R5P_sound (a : PairSlot) :
    (CA1_4_11I1R5P a).Encloses (CA1_4_11I1R5Value a) :=
  contains_sound (CA1_4_11I1R5Raw_sound a) (CA1_4_11I1R5P_check a)
def CA1_4_11I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R5Certificates (CA1_4_11I1R5CertificateIndex a)).output
lemma CA1_4_11I1R5Terms_sound (a : PairSlot) :
    (CA1_4_11I1R5Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R5Certificates_valid
    (CA1_4_11I1R5CertificateIndex a) (CA1_4_11I1R5P_sound a)
def CA1_4_11I1R5Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R5Entropy_sound : CA1_4_11I1R5Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R5Value CA1_4_11I1R5Terms CA1_4_11I1R5Terms_sound) (by decide +kernel)
def CA1_4_11I1R5Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R5Mass_sound : CA1_4_11I1R5Mass.Encloses (∑ a, CA1_4_11I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R5P CA1_4_11I1R5Value CA1_4_11I1R5P_sound) (by decide +kernel)
def CA1_4_11I1R5MassTerm : Ball := .exact 0
lemma CA1_4_11I1R5MassTerm_sound : CA1_4_11I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R5Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R5Mass_sound)
def CA1_4_11I1R5H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R5H_sound : CA1_4_11I1R5H.Encloses (homogeneousEntropy CA1_4_11I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R5Value CA1_4_11I1R5MassTerm_sound CA1_4_11I1R5Entropy_sound) (by decide +kernel)
def CA1_4_11I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA1_4_11I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA1_4_11I1R6Raw_sound (a : PairSlot) :
    (CA1_4_11I1R6Raw a).Encloses (CA1_4_11I1R6Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA1_4_11I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R6Certificates_valid :
    CA1_4_11I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R6Certificates (CA1_4_11I1R6CertificateIndex a)).input
lemma CA1_4_11I1R6P_check : ∀ a : PairSlot, contains (CA1_4_11I1R6Raw a) (CA1_4_11I1R6P a) = true := by
  decide +kernel
lemma CA1_4_11I1R6P_sound (a : PairSlot) :
    (CA1_4_11I1R6P a).Encloses (CA1_4_11I1R6Value a) :=
  contains_sound (CA1_4_11I1R6Raw_sound a) (CA1_4_11I1R6P_check a)
def CA1_4_11I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R6Certificates (CA1_4_11I1R6CertificateIndex a)).output
lemma CA1_4_11I1R6Terms_sound (a : PairSlot) :
    (CA1_4_11I1R6Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R6Certificates_valid
    (CA1_4_11I1R6CertificateIndex a) (CA1_4_11I1R6P_sound a)
def CA1_4_11I1R6Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R6Entropy_sound : CA1_4_11I1R6Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R6Value CA1_4_11I1R6Terms CA1_4_11I1R6Terms_sound) (by decide +kernel)
def CA1_4_11I1R6Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R6Mass_sound : CA1_4_11I1R6Mass.Encloses (∑ a, CA1_4_11I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R6P CA1_4_11I1R6Value CA1_4_11I1R6P_sound) (by decide +kernel)
def CA1_4_11I1R6MassTerm : Ball := .exact 0
lemma CA1_4_11I1R6MassTerm_sound : CA1_4_11I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R6Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R6Mass_sound)
def CA1_4_11I1R6H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R6H_sound : CA1_4_11I1R6H.Encloses (homogeneousEntropy CA1_4_11I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R6Value CA1_4_11I1R6MassTerm_sound CA1_4_11I1R6Entropy_sound) (by decide +kernel)
def CA1_4_11I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA1_4_11I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA1_4_11I1R7Raw_sound (a : PairSlot) :
    (CA1_4_11I1R7Raw a).Encloses (CA1_4_11I1R7Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA1_4_11I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R7Certificates_valid :
    CA1_4_11I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R7Certificates (CA1_4_11I1R7CertificateIndex a)).input
lemma CA1_4_11I1R7P_check : ∀ a : PairSlot, contains (CA1_4_11I1R7Raw a) (CA1_4_11I1R7P a) = true := by
  decide +kernel
lemma CA1_4_11I1R7P_sound (a : PairSlot) :
    (CA1_4_11I1R7P a).Encloses (CA1_4_11I1R7Value a) :=
  contains_sound (CA1_4_11I1R7Raw_sound a) (CA1_4_11I1R7P_check a)
def CA1_4_11I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R7Certificates (CA1_4_11I1R7CertificateIndex a)).output
lemma CA1_4_11I1R7Terms_sound (a : PairSlot) :
    (CA1_4_11I1R7Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R7Certificates_valid
    (CA1_4_11I1R7CertificateIndex a) (CA1_4_11I1R7P_sound a)
def CA1_4_11I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R7Entropy_sound : CA1_4_11I1R7Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R7Value CA1_4_11I1R7Terms CA1_4_11I1R7Terms_sound) (by decide +kernel)
def CA1_4_11I1R7Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R7Mass_sound : CA1_4_11I1R7Mass.Encloses (∑ a, CA1_4_11I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R7P CA1_4_11I1R7Value CA1_4_11I1R7P_sound) (by decide +kernel)
def CA1_4_11I1R7MassTerm : Ball := .exact 0
lemma CA1_4_11I1R7MassTerm_sound : CA1_4_11I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R7Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R7Mass_sound)
def CA1_4_11I1R7H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R7H_sound : CA1_4_11I1R7H.Encloses (homogeneousEntropy CA1_4_11I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R7Value CA1_4_11I1R7MassTerm_sound CA1_4_11I1R7Entropy_sound) (by decide +kernel)
def CA1_4_11I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA1_4_11I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA1_4_11I1R8Raw_sound (a : PairSlot) :
    (CA1_4_11I1R8Raw a).Encloses (CA1_4_11I1R8Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA1_4_11I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R8Certificates_valid :
    CA1_4_11I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R8Certificates (CA1_4_11I1R8CertificateIndex a)).input
lemma CA1_4_11I1R8P_check : ∀ a : PairSlot, contains (CA1_4_11I1R8Raw a) (CA1_4_11I1R8P a) = true := by
  decide +kernel
lemma CA1_4_11I1R8P_sound (a : PairSlot) :
    (CA1_4_11I1R8P a).Encloses (CA1_4_11I1R8Value a) :=
  contains_sound (CA1_4_11I1R8Raw_sound a) (CA1_4_11I1R8P_check a)
def CA1_4_11I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R8Certificates (CA1_4_11I1R8CertificateIndex a)).output
lemma CA1_4_11I1R8Terms_sound (a : PairSlot) :
    (CA1_4_11I1R8Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R8Certificates_valid
    (CA1_4_11I1R8CertificateIndex a) (CA1_4_11I1R8P_sound a)
def CA1_4_11I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R8Entropy_sound : CA1_4_11I1R8Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R8Value CA1_4_11I1R8Terms CA1_4_11I1R8Terms_sound) (by decide +kernel)
def CA1_4_11I1R8Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R8Mass_sound : CA1_4_11I1R8Mass.Encloses (∑ a, CA1_4_11I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R8P CA1_4_11I1R8Value CA1_4_11I1R8P_sound) (by decide +kernel)
def CA1_4_11I1R8MassTerm : Ball := .exact 0
lemma CA1_4_11I1R8MassTerm_sound : CA1_4_11I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R8Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R8Mass_sound)
def CA1_4_11I1R8H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R8H_sound : CA1_4_11I1R8H.Encloses (homogeneousEntropy CA1_4_11I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R8Value CA1_4_11I1R8MassTerm_sound CA1_4_11I1R8Entropy_sound) (by decide +kernel)
def CA1_4_11I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA1_4_11I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA1_4_11I1R9Raw_sound (a : PairSlot) :
    (CA1_4_11I1R9Raw a).Encloses (CA1_4_11I1R9Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA1_4_11I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R9Certificates_valid :
    CA1_4_11I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R9Certificates (CA1_4_11I1R9CertificateIndex a)).input
lemma CA1_4_11I1R9P_check : ∀ a : PairSlot, contains (CA1_4_11I1R9Raw a) (CA1_4_11I1R9P a) = true := by
  decide +kernel
lemma CA1_4_11I1R9P_sound (a : PairSlot) :
    (CA1_4_11I1R9P a).Encloses (CA1_4_11I1R9Value a) :=
  contains_sound (CA1_4_11I1R9Raw_sound a) (CA1_4_11I1R9P_check a)
def CA1_4_11I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R9Certificates (CA1_4_11I1R9CertificateIndex a)).output
lemma CA1_4_11I1R9Terms_sound (a : PairSlot) :
    (CA1_4_11I1R9Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R9Certificates_valid
    (CA1_4_11I1R9CertificateIndex a) (CA1_4_11I1R9P_sound a)
def CA1_4_11I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R9Entropy_sound : CA1_4_11I1R9Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R9Value CA1_4_11I1R9Terms CA1_4_11I1R9Terms_sound) (by decide +kernel)
def CA1_4_11I1R9Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R9Mass_sound : CA1_4_11I1R9Mass.Encloses (∑ a, CA1_4_11I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R9P CA1_4_11I1R9Value CA1_4_11I1R9P_sound) (by decide +kernel)
def CA1_4_11I1R9MassTerm : Ball := .exact 0
lemma CA1_4_11I1R9MassTerm_sound : CA1_4_11I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R9Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R9Mass_sound)
def CA1_4_11I1R9H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R9H_sound : CA1_4_11I1R9H.Encloses (homogeneousEntropy CA1_4_11I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R9Value CA1_4_11I1R9MassTerm_sound CA1_4_11I1R9Entropy_sound) (by decide +kernel)
def CA1_4_11I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA1_4_11I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA1_4_11I1R10Raw_sound (a : PairSlot) :
    (CA1_4_11I1R10Raw a).Encloses (CA1_4_11I1R10Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA1_4_11I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R10Certificates_valid :
    CA1_4_11I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R10Certificates (CA1_4_11I1R10CertificateIndex a)).input
lemma CA1_4_11I1R10P_check : ∀ a : PairSlot, contains (CA1_4_11I1R10Raw a) (CA1_4_11I1R10P a) = true := by
  decide +kernel
lemma CA1_4_11I1R10P_sound (a : PairSlot) :
    (CA1_4_11I1R10P a).Encloses (CA1_4_11I1R10Value a) :=
  contains_sound (CA1_4_11I1R10Raw_sound a) (CA1_4_11I1R10P_check a)
def CA1_4_11I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R10Certificates (CA1_4_11I1R10CertificateIndex a)).output
lemma CA1_4_11I1R10Terms_sound (a : PairSlot) :
    (CA1_4_11I1R10Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R10Certificates_valid
    (CA1_4_11I1R10CertificateIndex a) (CA1_4_11I1R10P_sound a)
def CA1_4_11I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R10Entropy_sound : CA1_4_11I1R10Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R10Value CA1_4_11I1R10Terms CA1_4_11I1R10Terms_sound) (by decide +kernel)
def CA1_4_11I1R10Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R10Mass_sound : CA1_4_11I1R10Mass.Encloses (∑ a, CA1_4_11I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R10P CA1_4_11I1R10Value CA1_4_11I1R10P_sound) (by decide +kernel)
def CA1_4_11I1R10MassTerm : Ball := .exact 0
lemma CA1_4_11I1R10MassTerm_sound : CA1_4_11I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R10Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R10Mass_sound)
def CA1_4_11I1R10H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R10H_sound : CA1_4_11I1R10H.Encloses (homogeneousEntropy CA1_4_11I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R10Value CA1_4_11I1R10MassTerm_sound CA1_4_11I1R10Entropy_sound) (by decide +kernel)
def CA1_4_11I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA1_4_11I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA1_4_11I1R11Raw_sound (a : PairSlot) :
    (CA1_4_11I1R11Raw a).Encloses (CA1_4_11I1R11Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA1_4_11I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R11Certificates_valid :
    CA1_4_11I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R11Certificates (CA1_4_11I1R11CertificateIndex a)).input
lemma CA1_4_11I1R11P_check : ∀ a : PairSlot, contains (CA1_4_11I1R11Raw a) (CA1_4_11I1R11P a) = true := by
  decide +kernel
lemma CA1_4_11I1R11P_sound (a : PairSlot) :
    (CA1_4_11I1R11P a).Encloses (CA1_4_11I1R11Value a) :=
  contains_sound (CA1_4_11I1R11Raw_sound a) (CA1_4_11I1R11P_check a)
def CA1_4_11I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R11Certificates (CA1_4_11I1R11CertificateIndex a)).output
lemma CA1_4_11I1R11Terms_sound (a : PairSlot) :
    (CA1_4_11I1R11Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R11Certificates_valid
    (CA1_4_11I1R11CertificateIndex a) (CA1_4_11I1R11P_sound a)
def CA1_4_11I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R11Entropy_sound : CA1_4_11I1R11Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R11Value CA1_4_11I1R11Terms CA1_4_11I1R11Terms_sound) (by decide +kernel)
def CA1_4_11I1R11Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R11Mass_sound : CA1_4_11I1R11Mass.Encloses (∑ a, CA1_4_11I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R11P CA1_4_11I1R11Value CA1_4_11I1R11P_sound) (by decide +kernel)
def CA1_4_11I1R11MassTerm : Ball := .exact 0
lemma CA1_4_11I1R11MassTerm_sound : CA1_4_11I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R11Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R11Mass_sound)
def CA1_4_11I1R11H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R11H_sound : CA1_4_11I1R11H.Encloses (homogeneousEntropy CA1_4_11I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R11Value CA1_4_11I1R11MassTerm_sound CA1_4_11I1R11Entropy_sound) (by decide +kernel)
def CA1_4_11I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA1_4_11I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA1_4_11I1R12Raw_sound (a : PairSlot) :
    (CA1_4_11I1R12Raw a).Encloses (CA1_4_11I1R12Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA1_4_11I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R12Certificates_valid :
    CA1_4_11I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R12Certificates (CA1_4_11I1R12CertificateIndex a)).input
lemma CA1_4_11I1R12P_check : ∀ a : PairSlot, contains (CA1_4_11I1R12Raw a) (CA1_4_11I1R12P a) = true := by
  decide +kernel
lemma CA1_4_11I1R12P_sound (a : PairSlot) :
    (CA1_4_11I1R12P a).Encloses (CA1_4_11I1R12Value a) :=
  contains_sound (CA1_4_11I1R12Raw_sound a) (CA1_4_11I1R12P_check a)
def CA1_4_11I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R12Certificates (CA1_4_11I1R12CertificateIndex a)).output
lemma CA1_4_11I1R12Terms_sound (a : PairSlot) :
    (CA1_4_11I1R12Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R12Certificates_valid
    (CA1_4_11I1R12CertificateIndex a) (CA1_4_11I1R12P_sound a)
def CA1_4_11I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R12Entropy_sound : CA1_4_11I1R12Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R12Value CA1_4_11I1R12Terms CA1_4_11I1R12Terms_sound) (by decide +kernel)
def CA1_4_11I1R12Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R12Mass_sound : CA1_4_11I1R12Mass.Encloses (∑ a, CA1_4_11I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R12P CA1_4_11I1R12Value CA1_4_11I1R12P_sound) (by decide +kernel)
def CA1_4_11I1R12MassTerm : Ball := .exact 0
lemma CA1_4_11I1R12MassTerm_sound : CA1_4_11I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R12Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R12Mass_sound)
def CA1_4_11I1R12H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R12H_sound : CA1_4_11I1R12H.Encloses (homogeneousEntropy CA1_4_11I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R12Value CA1_4_11I1R12MassTerm_sound CA1_4_11I1R12Entropy_sound) (by decide +kernel)
def CA1_4_11I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA1_4_11I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA1_4_11I1R13Raw_sound (a : PairSlot) :
    (CA1_4_11I1R13Raw a).Encloses (CA1_4_11I1R13Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA1_4_11I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R13Certificates_valid :
    CA1_4_11I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R13Certificates (CA1_4_11I1R13CertificateIndex a)).input
lemma CA1_4_11I1R13P_check : ∀ a : PairSlot, contains (CA1_4_11I1R13Raw a) (CA1_4_11I1R13P a) = true := by
  decide +kernel
lemma CA1_4_11I1R13P_sound (a : PairSlot) :
    (CA1_4_11I1R13P a).Encloses (CA1_4_11I1R13Value a) :=
  contains_sound (CA1_4_11I1R13Raw_sound a) (CA1_4_11I1R13P_check a)
def CA1_4_11I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R13Certificates (CA1_4_11I1R13CertificateIndex a)).output
lemma CA1_4_11I1R13Terms_sound (a : PairSlot) :
    (CA1_4_11I1R13Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R13Certificates_valid
    (CA1_4_11I1R13CertificateIndex a) (CA1_4_11I1R13P_sound a)
def CA1_4_11I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R13Entropy_sound : CA1_4_11I1R13Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R13Value CA1_4_11I1R13Terms CA1_4_11I1R13Terms_sound) (by decide +kernel)
def CA1_4_11I1R13Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R13Mass_sound : CA1_4_11I1R13Mass.Encloses (∑ a, CA1_4_11I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R13P CA1_4_11I1R13Value CA1_4_11I1R13P_sound) (by decide +kernel)
def CA1_4_11I1R13MassTerm : Ball := .exact 0
lemma CA1_4_11I1R13MassTerm_sound : CA1_4_11I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R13Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R13Mass_sound)
def CA1_4_11I1R13H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R13H_sound : CA1_4_11I1R13H.Encloses (homogeneousEntropy CA1_4_11I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R13Value CA1_4_11I1R13MassTerm_sound CA1_4_11I1R13Entropy_sound) (by decide +kernel)
def CA1_4_11I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA1_4_11I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA1_4_11I1R14Raw_sound (a : PairSlot) :
    (CA1_4_11I1R14Raw a).Encloses (CA1_4_11I1R14Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA1_4_11I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R14Certificates_valid :
    CA1_4_11I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R14Certificates (CA1_4_11I1R14CertificateIndex a)).input
lemma CA1_4_11I1R14P_check : ∀ a : PairSlot, contains (CA1_4_11I1R14Raw a) (CA1_4_11I1R14P a) = true := by
  decide +kernel
lemma CA1_4_11I1R14P_sound (a : PairSlot) :
    (CA1_4_11I1R14P a).Encloses (CA1_4_11I1R14Value a) :=
  contains_sound (CA1_4_11I1R14Raw_sound a) (CA1_4_11I1R14P_check a)
def CA1_4_11I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R14Certificates (CA1_4_11I1R14CertificateIndex a)).output
lemma CA1_4_11I1R14Terms_sound (a : PairSlot) :
    (CA1_4_11I1R14Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R14Certificates_valid
    (CA1_4_11I1R14CertificateIndex a) (CA1_4_11I1R14P_sound a)
def CA1_4_11I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R14Entropy_sound : CA1_4_11I1R14Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R14Value CA1_4_11I1R14Terms CA1_4_11I1R14Terms_sound) (by decide +kernel)
def CA1_4_11I1R14Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R14Mass_sound : CA1_4_11I1R14Mass.Encloses (∑ a, CA1_4_11I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R14P CA1_4_11I1R14Value CA1_4_11I1R14P_sound) (by decide +kernel)
def CA1_4_11I1R14MassTerm : Ball := .exact 0
lemma CA1_4_11I1R14MassTerm_sound : CA1_4_11I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R14Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R14Mass_sound)
def CA1_4_11I1R14H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R14H_sound : CA1_4_11I1R14H.Encloses (homogeneousEntropy CA1_4_11I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R14Value CA1_4_11I1R14MassTerm_sound CA1_4_11I1R14Entropy_sound) (by decide +kernel)
def CA1_4_11I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA1_4_11I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA1_4_11I1R15Raw_sound (a : PairSlot) :
    (CA1_4_11I1R15Raw a).Encloses (CA1_4_11I1R15Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA1_4_11I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R15Certificates_valid :
    CA1_4_11I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R15Certificates (CA1_4_11I1R15CertificateIndex a)).input
lemma CA1_4_11I1R15P_check : ∀ a : PairSlot, contains (CA1_4_11I1R15Raw a) (CA1_4_11I1R15P a) = true := by
  decide +kernel
lemma CA1_4_11I1R15P_sound (a : PairSlot) :
    (CA1_4_11I1R15P a).Encloses (CA1_4_11I1R15Value a) :=
  contains_sound (CA1_4_11I1R15Raw_sound a) (CA1_4_11I1R15P_check a)
def CA1_4_11I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R15Certificates (CA1_4_11I1R15CertificateIndex a)).output
lemma CA1_4_11I1R15Terms_sound (a : PairSlot) :
    (CA1_4_11I1R15Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R15Certificates_valid
    (CA1_4_11I1R15CertificateIndex a) (CA1_4_11I1R15P_sound a)
def CA1_4_11I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R15Entropy_sound : CA1_4_11I1R15Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R15Value CA1_4_11I1R15Terms CA1_4_11I1R15Terms_sound) (by decide +kernel)
def CA1_4_11I1R15Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R15Mass_sound : CA1_4_11I1R15Mass.Encloses (∑ a, CA1_4_11I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R15P CA1_4_11I1R15Value CA1_4_11I1R15P_sound) (by decide +kernel)
def CA1_4_11I1R15MassTerm : Ball := .exact 0
lemma CA1_4_11I1R15MassTerm_sound : CA1_4_11I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R15Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R15Mass_sound)
def CA1_4_11I1R15H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R15H_sound : CA1_4_11I1R15H.Encloses (homogeneousEntropy CA1_4_11I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R15Value CA1_4_11I1R15MassTerm_sound CA1_4_11I1R15Entropy_sound) (by decide +kernel)
def CA1_4_11I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA1_4_11I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA1_4_11I1R16Raw_sound (a : PairSlot) :
    (CA1_4_11I1R16Raw a).Encloses (CA1_4_11I1R16Value a) := by
  exact residualBall_sound_on (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 4 11) (show (shape 1 4 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA1_4_11I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_4_11I1R16Certificates_valid :
    CA1_4_11I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_4_11I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R16Certificates (CA1_4_11I1R16CertificateIndex a)).input
lemma CA1_4_11I1R16P_check : ∀ a : PairSlot, contains (CA1_4_11I1R16Raw a) (CA1_4_11I1R16P a) = true := by
  decide +kernel
lemma CA1_4_11I1R16P_sound (a : PairSlot) :
    (CA1_4_11I1R16P a).Encloses (CA1_4_11I1R16Value a) :=
  contains_sound (CA1_4_11I1R16Raw_sound a) (CA1_4_11I1R16P_check a)
def CA1_4_11I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R16Certificates (CA1_4_11I1R16CertificateIndex a)).output
lemma CA1_4_11I1R16Terms_sound (a : PairSlot) :
    (CA1_4_11I1R16Terms a).Encloses (Foundation.entropyTerm (CA1_4_11I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_4_11I1R16Certificates_valid
    (CA1_4_11I1R16CertificateIndex a) (CA1_4_11I1R16P_sound a)
def CA1_4_11I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R16Entropy_sound : CA1_4_11I1R16Entropy.Encloses (Foundation.finiteEntropy CA1_4_11I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA1_4_11I1R16Value CA1_4_11I1R16Terms CA1_4_11I1R16Terms_sound) (by decide +kernel)
def CA1_4_11I1R16Mass : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R16Mass_sound : CA1_4_11I1R16Mass.Encloses (∑ a, CA1_4_11I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA1_4_11I1R16P CA1_4_11I1R16Value CA1_4_11I1R16P_sound) (by decide +kernel)
def CA1_4_11I1R16MassTerm : Ball := .exact 0
lemma CA1_4_11I1R16MassTerm_sound : CA1_4_11I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_4_11I1R16Value a))) :=
  entropyTerm_zero_ball (CA1_4_11I1R16Mass_sound)
def CA1_4_11I1R16H : Ball := ⟨0, 0⟩
lemma CA1_4_11I1R16H_sound : CA1_4_11I1R16H.Encloses (homogeneousEntropy CA1_4_11I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R16Value CA1_4_11I1R16MassTerm_sound CA1_4_11I1R16Entropy_sound) (by decide +kernel)
def CA1_4_11I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_4_11I1R0H
  | 1 => CA1_4_11I1R1H
  | 2 => CA1_4_11I1R2H
  | 3 => CA1_4_11I1R3H
  | 4 => CA1_4_11I1R4H
  | 5 => CA1_4_11I1R5H
  | 6 => CA1_4_11I1R6H
  | 7 => CA1_4_11I1R7H
  | 8 => CA1_4_11I1R8H
  | 9 => CA1_4_11I1R9H
  | 10 => CA1_4_11I1R10H
  | 11 => CA1_4_11I1R11H
  | 12 => CA1_4_11I1R12H
  | 13 => CA1_4_11I1R13H
  | 14 => CA1_4_11I1R14H
  | 15 => CA1_4_11I1R15H
  | 16 => CA1_4_11I1R16H
  | _ => (.exact 0)
lemma CA1_4_11I1ResidualEntropies_sound (k : Fin 17) :
    (CA1_4_11I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_4_11I1R0H_sound
  · exact CA1_4_11I1R1H_sound
  · exact CA1_4_11I1R2H_sound
  · exact CA1_4_11I1R3H_sound
  · exact CA1_4_11I1R4H_sound
  · exact CA1_4_11I1R5H_sound
  · exact CA1_4_11I1R6H_sound
  · exact CA1_4_11I1R7H_sound
  · exact CA1_4_11I1R8H_sound
  · exact CA1_4_11I1R9H_sound
  · exact CA1_4_11I1R10H_sound
  · exact CA1_4_11I1R11H_sound
  · exact CA1_4_11I1R12H_sound
  · exact CA1_4_11I1R13H_sound
  · exact CA1_4_11I1R14H_sound
  · exact CA1_4_11I1R15H_sound
  · exact CA1_4_11I1R16H_sound
def CA1_4_11I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
lemma CA1_4_11I1Singles_sound (u : Shape) (hu : u ∈ below (shape 1 4 11))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA1_4_11I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A1_4_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def CA1_4_11I1Singleton : Ball := ⟨0, 0⟩
lemma CA1_4_11I1Singleton_sound : CA1_4_11I1Singleton.Encloses
    (singletonEntropy (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 4 11)) A1_4_11Law (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA1_4_11I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_4_11Law_sound u) CA1_4_11I1Singles_sound) (by decide +kernel)
def CA1_4_11I1Group : Ball := ⟨(3060939233434843112480476301733 / 3125000000000000000000000000000), (165613008857 / 100000000000000000000000000000000)⟩
lemma CA1_4_11I1Group_sound : CA1_4_11I1Group.Encloses
    (groupedEntropy (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_4_11I1Singleton_sound
    (finSumBall_sound 17 CA1_4_11I1ResidualEntropies _ CA1_4_11I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA1_4_11I1H : Ball := ⟨(29858925884867968039673444479119 / 25000000000000000000000000000000), (241431188193 / 50000000000000000000000000000000)⟩
lemma CA1_4_11I1_sound : CA1_4_11I1H.Encloses (stageACapacity (shape 1 4 11) 1) := by
  have hb := contains_sound (Ball.add_sound CA1_4_11I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_4_11I1Group_sound)))
    (show contains (.add CA1_4_11I1PairH (.neg (.mul (.exact 2) CA1_4_11I1Group))) CA1_4_11I1H = true by decide +kernel)
  unfold CA1_4_11I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
