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
def CA2_3_11I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 2 3 11)) (shape 2 3 11) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA2_3_11I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 3 11) A2_3_11Law 1 a
lemma CA2_3_11I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA2_3_11I1PairRaw a).Encloses (CA2_3_11I1PairValue a) := by
  exact stageAPairBall_sound (shape 2 3 11) (by decide +kernel) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (fun u _ => A2_3_11Law_sound u) 1 a
def CA2_3_11I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2271560897363885769568661563241 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(14045314490315458940368407925559 / 100000000000000000000000000000000), (5772260873 / 100000000000000000000000000000000)⟩ ⟨(-77288894756326186137499818697887 / 25000000000000000000000000000000), (12705494267 / 10000000000000000000000000000000)⟩ ⟨-5, 2271560897363885769568661563241, 1562500000000000000000000000000⟩,
   .log ⟨(445631426468121811824369066183 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1206197991236156335588169110941 / 50000000000000000000000000000000), (424647573 / 50000000000000000000000000000000)⟩ ⟨(-541343325265881605206048859565183 / 100000000000000000000000000000000), (9529120691 / 5000000000000000000000000000000)⟩ ⟨-8, 445631426468121811824369066183, 390625000000000000000000000000⟩,
   .log ⟨(245112486634681690138917478609 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(736711098549424427900092923637 / 50000000000000000000000000000000), (259522951 / 50000000000000000000000000000000)⟩ ⟨(-601120823067187632449041235450239 / 100000000000000000000000000000000), (211758238053 / 100000000000000000000000000000000)⟩ ⟨-9, 245112486634681690138917478609, 195312500000000000000000000000⟩,
   .log ⟨(3478219192845429210452448196343 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩ ⟨(1460265002538934125775794000921 / 12500000000000000000000000000000), (1104812363 / 25000000000000000000000000000000)⟩ ⟨(-41983121867151049577989038803243 / 12500000000000000000000000000000), (127054942557 / 100000000000000000000000000000000)⟩ ⟨-5, 3478219192845429210452448196343, 3125000000000000000000000000000⟩,
   .log ⟨(333792101685443411124955538513 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1903418455862116071835962862411 / 100000000000000000000000000000000), (706832283 / 100000000000000000000000000000000)⟩ ⟨(-14256017789598911799381317146333 / 2500000000000000000000000000000), (211758237429 / 100000000000000000000000000000000)⟩ ⟨-9, 333792101685443411124955538513, 195312500000000000000000000000⟩,
   .log ⟨(12142111703107679715744582859013 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩ ⟨(25601526806740030244864750152551 / 100000000000000000000000000000000), (6427980469 / 50000000000000000000000000000000)⟩ ⟨(-210849046959331770779779818286681 / 100000000000000000000000000000000), (105879118703 / 100000000000000000000000000000000)⟩ ⟨-4, 12142111703107679715744582859013, 6250000000000000000000000000000⟩]
lemma CA2_3_11I1PairCertificates_valid :
    CA2_3_11I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 1, 2 => 1
  | 0, 0, 1, 3 => 2
  | 0, 0, 2, 1 => 1
  | 0, 0, 3, 1 => 2
  | 0, 0, 4, 0 => 3
  | 0, 0, 0, 4 => 3
  | 1, 0, 0, 2 => 4
  | 1, 0, 0, 3 => 5
  | 1, 0, 1, 1 => 6
  | 1, 0, 2, 0 => 4
  | 1, 0, 3, 0 => 5
  | 0, 1, 0, 2 => 4
  | 0, 1, 0, 3 => 5
  | 0, 1, 1, 1 => 6
  | 0, 1, 2, 0 => 4
  | 0, 1, 3, 0 => 5
  | 2, 0, 0, 1 => 4
  | 2, 0, 1, 0 => 4
  | 3, 0, 0, 1 => 5
  | 3, 0, 1, 0 => 5
  | 1, 1, 0, 1 => 6
  | 1, 1, 1, 0 => 6
  | 0, 2, 0, 1 => 4
  | 0, 2, 1, 0 => 4
  | 0, 3, 0, 1 => 5
  | 0, 3, 1, 0 => 5
  | 4, 0, 0, 0 => 3
  | 2, 1, 0, 0 => 1
  | 3, 1, 0, 0 => 2
  | 1, 2, 0, 0 => 1
  | 1, 3, 0, 0 => 2
  | 0, 4, 0, 0 => 3
  | _, _, _, _ => 0
def CA2_3_11I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1PairCertificates (CA2_3_11I1PairCertificateIndex a)).input
lemma CA2_3_11I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,0),(k,l))) (CA2_3_11I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,1),(k,l))) (CA2_3_11I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,2),(k,l))) (CA2_3_11I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,3),(k,l))) (CA2_3_11I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,4),(k,l))) (CA2_3_11I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,5),(k,l))) (CA2_3_11I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,0),(k,l))) (CA2_3_11I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,1),(k,l))) (CA2_3_11I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,2),(k,l))) (CA2_3_11I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,3),(k,l))) (CA2_3_11I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,4),(k,l))) (CA2_3_11I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,5),(k,l))) (CA2_3_11I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,0),(k,l))) (CA2_3_11I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,1),(k,l))) (CA2_3_11I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,2),(k,l))) (CA2_3_11I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,3),(k,l))) (CA2_3_11I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,4),(k,l))) (CA2_3_11I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,5),(k,l))) (CA2_3_11I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,0),(k,l))) (CA2_3_11I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,1),(k,l))) (CA2_3_11I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,2),(k,l))) (CA2_3_11I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,3),(k,l))) (CA2_3_11I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,4),(k,l))) (CA2_3_11I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,5),(k,l))) (CA2_3_11I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,0),(k,l))) (CA2_3_11I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,1),(k,l))) (CA2_3_11I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,2),(k,l))) (CA2_3_11I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,3),(k,l))) (CA2_3_11I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,4),(k,l))) (CA2_3_11I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,5),(k,l))) (CA2_3_11I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,0),(k,l))) (CA2_3_11I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,1),(k,l))) (CA2_3_11I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,2),(k,l))) (CA2_3_11I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,3),(k,l))) (CA2_3_11I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,4),(k,l))) (CA2_3_11I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,5),(k,l))) (CA2_3_11I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check (a : PairSlot × PairSlot) : contains (CA2_3_11I1PairRaw a) (CA2_3_11I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA2_3_11I1PairP_check_0_0 k l) (CA2_3_11I1PairP_check_0_1 k l) (CA2_3_11I1PairP_check_0_2 k l) (CA2_3_11I1PairP_check_0_3 k l) (CA2_3_11I1PairP_check_0_4 k l) (CA2_3_11I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA2_3_11I1PairP_check_1_0 k l) (CA2_3_11I1PairP_check_1_1 k l) (CA2_3_11I1PairP_check_1_2 k l) (CA2_3_11I1PairP_check_1_3 k l) (CA2_3_11I1PairP_check_1_4 k l) (CA2_3_11I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA2_3_11I1PairP_check_2_0 k l) (CA2_3_11I1PairP_check_2_1 k l) (CA2_3_11I1PairP_check_2_2 k l) (CA2_3_11I1PairP_check_2_3 k l) (CA2_3_11I1PairP_check_2_4 k l) (CA2_3_11I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA2_3_11I1PairP_check_3_0 k l) (CA2_3_11I1PairP_check_3_1 k l) (CA2_3_11I1PairP_check_3_2 k l) (CA2_3_11I1PairP_check_3_3 k l) (CA2_3_11I1PairP_check_3_4 k l) (CA2_3_11I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA2_3_11I1PairP_check_4_0 k l) (CA2_3_11I1PairP_check_4_1 k l) (CA2_3_11I1PairP_check_4_2 k l) (CA2_3_11I1PairP_check_4_3 k l) (CA2_3_11I1PairP_check_4_4 k l) (CA2_3_11I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA2_3_11I1PairP_check_5_0 k l) (CA2_3_11I1PairP_check_5_1 k l) (CA2_3_11I1PairP_check_5_2 k l) (CA2_3_11I1PairP_check_5_3 k l) (CA2_3_11I1PairP_check_5_4 k l) (CA2_3_11I1PairP_check_5_5 k l)
lemma CA2_3_11I1PairP_sound (a : PairSlot × PairSlot) :
    (CA2_3_11I1PairP a).Encloses (CA2_3_11I1PairValue a) :=
  contains_sound (CA2_3_11I1PairRaw_sound a) (CA2_3_11I1PairP_check a)
def CA2_3_11I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1PairCertificates (CA2_3_11I1PairCertificateIndex a)).output
lemma CA2_3_11I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA2_3_11I1PairTerms a).Encloses (Foundation.entropyTerm (CA2_3_11I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1PairCertificates_valid
    (CA2_3_11I1PairCertificateIndex a) (CA2_3_11I1PairP_sound a)
def CA2_3_11I1PairEntropy : Ball := ⟨(8837967053621728608536788985853 / 3125000000000000000000000000000), (30248726329 / 25000000000000000000000000000000)⟩
lemma CA2_3_11I1PairEntropy_sound : CA2_3_11I1PairEntropy.Encloses (Foundation.finiteEntropy CA2_3_11I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA2_3_11I1PairValue CA2_3_11I1PairTerms CA2_3_11I1PairTerms_sound) (by decide +kernel)
def CA2_3_11I1PairMass : Ball := ⟨(24999999999999999999999999999999 / 25000000000000000000000000000000), (103 / 25000000000000000000000000000000)⟩
lemma CA2_3_11I1PairMass_sound : CA2_3_11I1PairMass.Encloses (∑ a, CA2_3_11I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA2_3_11I1PairP CA2_3_11I1PairValue CA2_3_11I1PairP_sound) (by decide +kernel)
def CA2_3_11I1PairMassTermLogWitness : LogWitness := ⟨-1, 24999999999999999999999999999999, 12500000000000000000000000000000⟩
def CA2_3_11I1PairMassTermLog : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175823889 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I1PairMassTermLog_sound : CA2_3_11I1PairMassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I1PairMass_sound) (w := CA2_3_11I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_3_11I1PairMassTerm : Ball := ⟨(1 / 25000000000000000000000000000000), (42351647779 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I1PairMassTerm_sound : CA2_3_11I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I1PairMass_sound) CA2_3_11I1PairMassTermLog_sound) (by decide +kernel)
def CA2_3_11I1PairH : Ball := ⟨(70703736428973828868294311886823 / 25000000000000000000000000000000), (32669310619 / 20000000000000000000000000000000)⟩
lemma CA2_3_11I1PairH_sound : CA2_3_11I1PairH.Encloses (homogeneousEntropy CA2_3_11I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1PairValue CA2_3_11I1PairMassTerm_sound CA2_3_11I1PairEntropy_sound) (by decide +kernel)

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
def CA2_3_11I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA2_3_11I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA2_3_11I1R0Raw_sound (a : PairSlot) :
    (CA2_3_11I1R0Raw a).Encloses (CA2_3_11I1R0Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA2_3_11I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2616932853915287520550304835637 / 25000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩ ⟨(23624338930499515612716987850007 / 100000000000000000000000000000000), (5541570939 / 50000000000000000000000000000000)⟩ ⟨(-225687285930495800137701698295113 / 100000000000000000000000000000000), (3308722463 / 3125000000000000000000000000000)⟩ ⟨-4, 2616932853915287520550304835637, 1562500000000000000000000000000⟩]
lemma CA2_3_11I1R0Certificates_valid :
    CA2_3_11I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA2_3_11I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R0Certificates (CA2_3_11I1R0CertificateIndex a)).input
lemma CA2_3_11I1R0P_check : ∀ a : PairSlot, contains (CA2_3_11I1R0Raw a) (CA2_3_11I1R0P a) = true := by
  decide +kernel
lemma CA2_3_11I1R0P_sound (a : PairSlot) :
    (CA2_3_11I1R0P a).Encloses (CA2_3_11I1R0Value a) :=
  contains_sound (CA2_3_11I1R0Raw_sound a) (CA2_3_11I1R0P_check a)
def CA2_3_11I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R0Certificates (CA2_3_11I1R0CertificateIndex a)).output
lemma CA2_3_11I1R0Terms_sound (a : PairSlot) :
    (CA2_3_11I1R0Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R0Certificates_valid
    (CA2_3_11I1R0CertificateIndex a) (CA2_3_11I1R0P_sound a)
def CA2_3_11I1R0Entropy : Ball := ⟨(23624338930499515612716987850007 / 100000000000000000000000000000000), (5541570939 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I1R0Entropy_sound : CA2_3_11I1R0Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R0Value CA2_3_11I1R0Terms CA2_3_11I1R0Terms_sound) (by decide +kernel)
def CA2_3_11I1R0Mass : Ball := ⟨(2616932853915287520550304835637 / 25000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I1R0Mass_sound : CA2_3_11I1R0Mass.Encloses (∑ a, CA2_3_11I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R0P CA2_3_11I1R0Value CA2_3_11I1R0P_sound) (by decide +kernel)
def CA2_3_11I1R0MassTermLogWitness : LogWitness := ⟨-4, 2616932853915287520550304835637, 1562500000000000000000000000000⟩
def CA2_3_11I1R0MassTermLog : Ball := ⟨(-225687285930495800137701698295113 / 100000000000000000000000000000000), (3308722463 / 3125000000000000000000000000000)⟩
lemma CA2_3_11I1R0MassTermLog_sound : CA2_3_11I1R0MassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I1R0Mass_sound) (w := CA2_3_11I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_3_11I1R0MassTerm : Ball := ⟨(23624338930499515612716987850007 / 100000000000000000000000000000000), (5541570939 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I1R0MassTerm_sound : CA2_3_11I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I1R0Mass_sound) CA2_3_11I1R0MassTermLog_sound) (by decide +kernel)
def CA2_3_11I1R0H : Ball := ⟨0, (5541570939 / 25000000000000000000000000000000)⟩
lemma CA2_3_11I1R0H_sound : CA2_3_11I1R0H.Encloses (homogeneousEntropy CA2_3_11I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R0Value CA2_3_11I1R0MassTerm_sound CA2_3_11I1R0Entropy_sound) (by decide +kernel)
def CA2_3_11I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA2_3_11I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA2_3_11I1R1Raw_sound (a : PairSlot) :
    (CA2_3_11I1R1Raw a).Encloses (CA2_3_11I1R1Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA2_3_11I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(9883067146084712479449695164363 / 50000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩ ⟨(32044858929775539194174820947917 / 100000000000000000000000000000000), (4185641777 / 25000000000000000000000000000000)⟩ ⟨(-4053000254894360938496064162113 / 2500000000000000000000000000000), (21175823741 / 25000000000000000000000000000000)⟩ ⟨-3, 9883067146084712479449695164363, 6250000000000000000000000000000⟩]
lemma CA2_3_11I1R1Certificates_valid :
    CA2_3_11I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA2_3_11I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R1Certificates (CA2_3_11I1R1CertificateIndex a)).input
lemma CA2_3_11I1R1P_check : ∀ a : PairSlot, contains (CA2_3_11I1R1Raw a) (CA2_3_11I1R1P a) = true := by
  decide +kernel
lemma CA2_3_11I1R1P_sound (a : PairSlot) :
    (CA2_3_11I1R1P a).Encloses (CA2_3_11I1R1Value a) :=
  contains_sound (CA2_3_11I1R1Raw_sound a) (CA2_3_11I1R1P_check a)
def CA2_3_11I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R1Certificates (CA2_3_11I1R1CertificateIndex a)).output
lemma CA2_3_11I1R1Terms_sound (a : PairSlot) :
    (CA2_3_11I1R1Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R1Certificates_valid
    (CA2_3_11I1R1CertificateIndex a) (CA2_3_11I1R1P_sound a)
def CA2_3_11I1R1Entropy : Ball := ⟨(32044858929775539194174820947917 / 50000000000000000000000000000000), (4185641777 / 12500000000000000000000000000000)⟩
lemma CA2_3_11I1R1Entropy_sound : CA2_3_11I1R1Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R1Value CA2_3_11I1R1Terms CA2_3_11I1R1Terms_sound) (by decide +kernel)
def CA2_3_11I1R1Mass : Ball := ⟨(9883067146084712479449695164363 / 25000000000000000000000000000000), (23 / 25000000000000000000000000000000)⟩
lemma CA2_3_11I1R1Mass_sound : CA2_3_11I1R1Mass.Encloses (∑ a, CA2_3_11I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R1P CA2_3_11I1R1Value CA2_3_11I1R1P_sound) (by decide +kernel)
def CA2_3_11I1R1MassTermLogWitness : LogWitness := ⟨-2, 9883067146084712479449695164363, 6250000000000000000000000000000⟩
def CA2_3_11I1R1MassTermLog : Ball := ⟨(-9280529213977990659811937343419 / 10000000000000000000000000000000), (63527471281 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I1R1MassTermLog_sound : CA2_3_11I1R1MassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I1R1Mass_sound) (w := CA2_3_11I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_3_11I1R1MassTerm : Ball := ⟨(36688037349178104038961450659137 / 100000000000000000000000000000000), (12556925329 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I1R1MassTerm_sound : CA2_3_11I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I1R1Mass_sound) CA2_3_11I1R1MassTermLog_sound) (by decide +kernel)
def CA2_3_11I1R1H : Ball := ⟨(27401680510372974349388191236697 / 100000000000000000000000000000000), (29299492437 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I1R1H_sound : CA2_3_11I1R1H.Encloses (homogeneousEntropy CA2_3_11I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R1Value CA2_3_11I1R1MassTerm_sound CA2_3_11I1R1Entropy_sound) (by decide +kernel)
def CA2_3_11I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA2_3_11I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA2_3_11I1R2Raw_sound (a : PairSlot) :
    (CA2_3_11I1R2Raw a).Encloses (CA2_3_11I1R2Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA2_3_11I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3478219192845429210452448196343 / 50000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩ ⟨(2317800548355293762733205614737 / 12500000000000000000000000000000), (7365415743 / 100000000000000000000000000000000)⟩ ⟨(-133275128440606932841094558687807 / 50000000000000000000000000000000), (105879118831 / 100000000000000000000000000000000)⟩ ⟨-4, 3478219192845429210452448196343, 3125000000000000000000000000000⟩,
   .log ⟨(667584203370886822249911077027 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(33441028033713448054116710973 / 1000000000000000000000000000000), (127229811 / 10000000000000000000000000000000)⟩ ⟨(-12523149838199048525838237320071 / 2500000000000000000000000000000), (95291206873 / 50000000000000000000000000000000)⟩ ⟨-8, 667584203370886822249911077027, 390625000000000000000000000000⟩,
   .log ⟨(12142111703107679715744582859013 / 50000000000000000000000000000000), (3 / 5000000000000000000000000000000)⟩ ⟨(34370512627374052637955936517139 / 100000000000000000000000000000000), (20569537471 / 100000000000000000000000000000000)⟩ ⟨(-141534328903337239838056625236351 / 100000000000000000000000000000000), (84703294979 / 100000000000000000000000000000000)⟩ ⟨-3, 12142111703107679715744582859013, 6250000000000000000000000000000⟩]
lemma CA2_3_11I1R2Certificates_valid :
    CA2_3_11I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA2_3_11I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R2Certificates (CA2_3_11I1R2CertificateIndex a)).input
lemma CA2_3_11I1R2P_check : ∀ a : PairSlot, contains (CA2_3_11I1R2Raw a) (CA2_3_11I1R2P a) = true := by
  decide +kernel
lemma CA2_3_11I1R2P_sound (a : PairSlot) :
    (CA2_3_11I1R2P a).Encloses (CA2_3_11I1R2Value a) :=
  contains_sound (CA2_3_11I1R2Raw_sound a) (CA2_3_11I1R2P_check a)
def CA2_3_11I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R2Certificates (CA2_3_11I1R2CertificateIndex a)).output
lemma CA2_3_11I1R2Terms_sound (a : PairSlot) :
    (CA2_3_11I1R2Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R2Certificates_valid
    (CA2_3_11I1R2CertificateIndex a) (CA2_3_11I1R2P_sound a)
def CA2_3_11I1R2Entropy : Ball := ⟨(78143527007801442452510568547531 / 100000000000000000000000000000000), (37844965177 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I1R2Entropy_sound : CA2_3_11I1R2Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R2Value CA2_3_11I1R2Terms CA2_3_11I1R2Terms_sound) (by decide +kernel)
def CA2_3_11I1R2Mass : Ball := ⟨(9883067146084712479449695164363 / 25000000000000000000000000000000), (63 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I1R2Mass_sound : CA2_3_11I1R2Mass.Encloses (∑ a, CA2_3_11I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R2P CA2_3_11I1R2Value CA2_3_11I1R2P_sound) (by decide +kernel)
def CA2_3_11I1R2MassTermLogWitness : LogWitness := ⟨-2, 9883067146084712479449695164363, 6250000000000000000000000000000⟩
def CA2_3_11I1R2MassTermLog : Ball := ⟨(-9280529213977990659811937343419 / 10000000000000000000000000000000), (63527471367 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I1R2MassTermLog_sound : CA2_3_11I1R2MassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I1R2Mass_sound) (w := CA2_3_11I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_3_11I1R2MassTerm : Ball := ⟨(36688037349178104038961450659137 / 100000000000000000000000000000000), (25113850723 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I1R2MassTerm_sound : CA2_3_11I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I1R2Mass_sound) CA2_3_11I1R2MassTermLog_sound) (by decide +kernel)
def CA2_3_11I1R2H : Ball := ⟨(20727744829311669206774558944197 / 50000000000000000000000000000000), (629588159 / 1000000000000000000000000000000)⟩
lemma CA2_3_11I1R2H_sound : CA2_3_11I1R2H.Encloses (homogeneousEntropy CA2_3_11I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R2Value CA2_3_11I1R2MassTerm_sound CA2_3_11I1R2Entropy_sound) (by decide +kernel)
def CA2_3_11I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA2_3_11I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA2_3_11I1R3Raw_sound (a : PairSlot) :
    (CA2_3_11I1R3Raw a).Encloses (CA2_3_11I1R3Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA2_3_11I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(245112486634681690138917478609 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(736711098549424427900092923637 / 50000000000000000000000000000000), (259522951 / 50000000000000000000000000000000)⟩ ⟨(-601120823067187632449041235450239 / 100000000000000000000000000000000), (211758238053 / 100000000000000000000000000000000)⟩ ⟨-9, 245112486634681690138917478609, 195312500000000000000000000000⟩,
   .log ⟨(2271560897363885769568661563241 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(14045314490315458940368407925559 / 100000000000000000000000000000000), (5772260873 / 100000000000000000000000000000000)⟩ ⟨(-77288894756326186137499818697887 / 25000000000000000000000000000000), (12705494267 / 10000000000000000000000000000000)⟩ ⟨-5, 2271560897363885769568661563241, 1562500000000000000000000000000⟩,
   .log ⟨(445631426468121811824369066183 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1206197991236156335588169110941 / 50000000000000000000000000000000), (424647573 / 50000000000000000000000000000000)⟩ ⟨(-541343325265881605206048859565183 / 100000000000000000000000000000000), (9529120691 / 5000000000000000000000000000000)⟩ ⟨-8, 445631426468121811824369066183, 390625000000000000000000000000⟩]
lemma CA2_3_11I1R3Certificates_valid :
    CA2_3_11I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA2_3_11I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R3Certificates (CA2_3_11I1R3CertificateIndex a)).input
lemma CA2_3_11I1R3P_check : ∀ a : PairSlot, contains (CA2_3_11I1R3Raw a) (CA2_3_11I1R3P a) = true := by
  decide +kernel
lemma CA2_3_11I1R3P_sound (a : PairSlot) :
    (CA2_3_11I1R3P a).Encloses (CA2_3_11I1R3Value a) :=
  contains_sound (CA2_3_11I1R3Raw_sound a) (CA2_3_11I1R3P_check a)
def CA2_3_11I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R3Certificates (CA2_3_11I1R3CertificateIndex a)).output
lemma CA2_3_11I1R3Terms_sound (a : PairSlot) :
    (CA2_3_11I1R3Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R3Certificates_valid
    (CA2_3_11I1R3CertificateIndex a) (CA2_3_11I1R3P_sound a)
def CA2_3_11I1R3Entropy : Ball := ⟨(3586226533977324093468986398943 / 10000000000000000000000000000000), (7140601921 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I1R3Entropy_sound : CA2_3_11I1R3Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R3Value CA2_3_11I1R3Terms CA2_3_11I1R3Terms_sound) (by decide +kernel)
def CA2_3_11I1R3Mass : Ball := ⟨(2616932853915287520550304835637 / 25000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
lemma CA2_3_11I1R3Mass_sound : CA2_3_11I1R3Mass.Encloses (∑ a, CA2_3_11I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R3P CA2_3_11I1R3Value CA2_3_11I1R3P_sound) (by decide +kernel)
def CA2_3_11I1R3MassTermLogWitness : LogWitness := ⟨-4, 2616932853915287520550304835637, 1562500000000000000000000000000⟩
def CA2_3_11I1R3MassTermLog : Ball := ⟨(-225687285930495800137701698295113 / 100000000000000000000000000000000), (52939559513 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I1R3MassTermLog_sound : CA2_3_11I1R3MassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I1R3Mass_sound) (w := CA2_3_11I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_3_11I1R3MassTerm : Ball := ⟨(23624338930499515612716987850007 / 100000000000000000000000000000000), (221662839 / 2000000000000000000000000000000)⟩
lemma CA2_3_11I1R3MassTerm_sound : CA2_3_11I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I1R3Mass_sound) CA2_3_11I1R3MassTermLog_sound) (by decide +kernel)
def CA2_3_11I1R3H : Ball := ⟨(12237926409273725321972876139423 / 100000000000000000000000000000000), (396317903 / 1562500000000000000000000000000)⟩
lemma CA2_3_11I1R3H_sound : CA2_3_11I1R3H.Encloses (homogeneousEntropy CA2_3_11I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R3Value CA2_3_11I1R3MassTerm_sound CA2_3_11I1R3Entropy_sound) (by decide +kernel)
def CA2_3_11I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA2_3_11I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA2_3_11I1R4Raw_sound (a : PairSlot) :
    (CA2_3_11I1R4Raw a).Encloses (CA2_3_11I1R4Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA2_3_11I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R4Certificates_valid :
    CA2_3_11I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R4Certificates (CA2_3_11I1R4CertificateIndex a)).input
lemma CA2_3_11I1R4P_check : ∀ a : PairSlot, contains (CA2_3_11I1R4Raw a) (CA2_3_11I1R4P a) = true := by
  decide +kernel
lemma CA2_3_11I1R4P_sound (a : PairSlot) :
    (CA2_3_11I1R4P a).Encloses (CA2_3_11I1R4Value a) :=
  contains_sound (CA2_3_11I1R4Raw_sound a) (CA2_3_11I1R4P_check a)
def CA2_3_11I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R4Certificates (CA2_3_11I1R4CertificateIndex a)).output
lemma CA2_3_11I1R4Terms_sound (a : PairSlot) :
    (CA2_3_11I1R4Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R4Certificates_valid
    (CA2_3_11I1R4CertificateIndex a) (CA2_3_11I1R4P_sound a)
def CA2_3_11I1R4Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R4Entropy_sound : CA2_3_11I1R4Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R4Value CA2_3_11I1R4Terms CA2_3_11I1R4Terms_sound) (by decide +kernel)
def CA2_3_11I1R4Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R4Mass_sound : CA2_3_11I1R4Mass.Encloses (∑ a, CA2_3_11I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R4P CA2_3_11I1R4Value CA2_3_11I1R4P_sound) (by decide +kernel)
def CA2_3_11I1R4MassTerm : Ball := .exact 0
lemma CA2_3_11I1R4MassTerm_sound : CA2_3_11I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R4Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R4Mass_sound)
def CA2_3_11I1R4H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R4H_sound : CA2_3_11I1R4H.Encloses (homogeneousEntropy CA2_3_11I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R4Value CA2_3_11I1R4MassTerm_sound CA2_3_11I1R4Entropy_sound) (by decide +kernel)
def CA2_3_11I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA2_3_11I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA2_3_11I1R5Raw_sound (a : PairSlot) :
    (CA2_3_11I1R5Raw a).Encloses (CA2_3_11I1R5Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA2_3_11I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R5Certificates_valid :
    CA2_3_11I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R5Certificates (CA2_3_11I1R5CertificateIndex a)).input
lemma CA2_3_11I1R5P_check : ∀ a : PairSlot, contains (CA2_3_11I1R5Raw a) (CA2_3_11I1R5P a) = true := by
  decide +kernel
lemma CA2_3_11I1R5P_sound (a : PairSlot) :
    (CA2_3_11I1R5P a).Encloses (CA2_3_11I1R5Value a) :=
  contains_sound (CA2_3_11I1R5Raw_sound a) (CA2_3_11I1R5P_check a)
def CA2_3_11I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R5Certificates (CA2_3_11I1R5CertificateIndex a)).output
lemma CA2_3_11I1R5Terms_sound (a : PairSlot) :
    (CA2_3_11I1R5Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R5Certificates_valid
    (CA2_3_11I1R5CertificateIndex a) (CA2_3_11I1R5P_sound a)
def CA2_3_11I1R5Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R5Entropy_sound : CA2_3_11I1R5Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R5Value CA2_3_11I1R5Terms CA2_3_11I1R5Terms_sound) (by decide +kernel)
def CA2_3_11I1R5Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R5Mass_sound : CA2_3_11I1R5Mass.Encloses (∑ a, CA2_3_11I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R5P CA2_3_11I1R5Value CA2_3_11I1R5P_sound) (by decide +kernel)
def CA2_3_11I1R5MassTerm : Ball := .exact 0
lemma CA2_3_11I1R5MassTerm_sound : CA2_3_11I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R5Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R5Mass_sound)
def CA2_3_11I1R5H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R5H_sound : CA2_3_11I1R5H.Encloses (homogeneousEntropy CA2_3_11I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R5Value CA2_3_11I1R5MassTerm_sound CA2_3_11I1R5Entropy_sound) (by decide +kernel)
def CA2_3_11I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA2_3_11I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA2_3_11I1R6Raw_sound (a : PairSlot) :
    (CA2_3_11I1R6Raw a).Encloses (CA2_3_11I1R6Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA2_3_11I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R6Certificates_valid :
    CA2_3_11I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R6Certificates (CA2_3_11I1R6CertificateIndex a)).input
lemma CA2_3_11I1R6P_check : ∀ a : PairSlot, contains (CA2_3_11I1R6Raw a) (CA2_3_11I1R6P a) = true := by
  decide +kernel
lemma CA2_3_11I1R6P_sound (a : PairSlot) :
    (CA2_3_11I1R6P a).Encloses (CA2_3_11I1R6Value a) :=
  contains_sound (CA2_3_11I1R6Raw_sound a) (CA2_3_11I1R6P_check a)
def CA2_3_11I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R6Certificates (CA2_3_11I1R6CertificateIndex a)).output
lemma CA2_3_11I1R6Terms_sound (a : PairSlot) :
    (CA2_3_11I1R6Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R6Certificates_valid
    (CA2_3_11I1R6CertificateIndex a) (CA2_3_11I1R6P_sound a)
def CA2_3_11I1R6Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R6Entropy_sound : CA2_3_11I1R6Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R6Value CA2_3_11I1R6Terms CA2_3_11I1R6Terms_sound) (by decide +kernel)
def CA2_3_11I1R6Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R6Mass_sound : CA2_3_11I1R6Mass.Encloses (∑ a, CA2_3_11I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R6P CA2_3_11I1R6Value CA2_3_11I1R6P_sound) (by decide +kernel)
def CA2_3_11I1R6MassTerm : Ball := .exact 0
lemma CA2_3_11I1R6MassTerm_sound : CA2_3_11I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R6Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R6Mass_sound)
def CA2_3_11I1R6H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R6H_sound : CA2_3_11I1R6H.Encloses (homogeneousEntropy CA2_3_11I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R6Value CA2_3_11I1R6MassTerm_sound CA2_3_11I1R6Entropy_sound) (by decide +kernel)
def CA2_3_11I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA2_3_11I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA2_3_11I1R7Raw_sound (a : PairSlot) :
    (CA2_3_11I1R7Raw a).Encloses (CA2_3_11I1R7Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA2_3_11I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R7Certificates_valid :
    CA2_3_11I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R7Certificates (CA2_3_11I1R7CertificateIndex a)).input
lemma CA2_3_11I1R7P_check : ∀ a : PairSlot, contains (CA2_3_11I1R7Raw a) (CA2_3_11I1R7P a) = true := by
  decide +kernel
lemma CA2_3_11I1R7P_sound (a : PairSlot) :
    (CA2_3_11I1R7P a).Encloses (CA2_3_11I1R7Value a) :=
  contains_sound (CA2_3_11I1R7Raw_sound a) (CA2_3_11I1R7P_check a)
def CA2_3_11I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R7Certificates (CA2_3_11I1R7CertificateIndex a)).output
lemma CA2_3_11I1R7Terms_sound (a : PairSlot) :
    (CA2_3_11I1R7Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R7Certificates_valid
    (CA2_3_11I1R7CertificateIndex a) (CA2_3_11I1R7P_sound a)
def CA2_3_11I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R7Entropy_sound : CA2_3_11I1R7Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R7Value CA2_3_11I1R7Terms CA2_3_11I1R7Terms_sound) (by decide +kernel)
def CA2_3_11I1R7Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R7Mass_sound : CA2_3_11I1R7Mass.Encloses (∑ a, CA2_3_11I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R7P CA2_3_11I1R7Value CA2_3_11I1R7P_sound) (by decide +kernel)
def CA2_3_11I1R7MassTerm : Ball := .exact 0
lemma CA2_3_11I1R7MassTerm_sound : CA2_3_11I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R7Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R7Mass_sound)
def CA2_3_11I1R7H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R7H_sound : CA2_3_11I1R7H.Encloses (homogeneousEntropy CA2_3_11I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R7Value CA2_3_11I1R7MassTerm_sound CA2_3_11I1R7Entropy_sound) (by decide +kernel)
def CA2_3_11I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA2_3_11I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA2_3_11I1R8Raw_sound (a : PairSlot) :
    (CA2_3_11I1R8Raw a).Encloses (CA2_3_11I1R8Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA2_3_11I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R8Certificates_valid :
    CA2_3_11I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R8Certificates (CA2_3_11I1R8CertificateIndex a)).input
lemma CA2_3_11I1R8P_check : ∀ a : PairSlot, contains (CA2_3_11I1R8Raw a) (CA2_3_11I1R8P a) = true := by
  decide +kernel
lemma CA2_3_11I1R8P_sound (a : PairSlot) :
    (CA2_3_11I1R8P a).Encloses (CA2_3_11I1R8Value a) :=
  contains_sound (CA2_3_11I1R8Raw_sound a) (CA2_3_11I1R8P_check a)
def CA2_3_11I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R8Certificates (CA2_3_11I1R8CertificateIndex a)).output
lemma CA2_3_11I1R8Terms_sound (a : PairSlot) :
    (CA2_3_11I1R8Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R8Certificates_valid
    (CA2_3_11I1R8CertificateIndex a) (CA2_3_11I1R8P_sound a)
def CA2_3_11I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R8Entropy_sound : CA2_3_11I1R8Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R8Value CA2_3_11I1R8Terms CA2_3_11I1R8Terms_sound) (by decide +kernel)
def CA2_3_11I1R8Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R8Mass_sound : CA2_3_11I1R8Mass.Encloses (∑ a, CA2_3_11I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R8P CA2_3_11I1R8Value CA2_3_11I1R8P_sound) (by decide +kernel)
def CA2_3_11I1R8MassTerm : Ball := .exact 0
lemma CA2_3_11I1R8MassTerm_sound : CA2_3_11I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R8Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R8Mass_sound)
def CA2_3_11I1R8H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R8H_sound : CA2_3_11I1R8H.Encloses (homogeneousEntropy CA2_3_11I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R8Value CA2_3_11I1R8MassTerm_sound CA2_3_11I1R8Entropy_sound) (by decide +kernel)
def CA2_3_11I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA2_3_11I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA2_3_11I1R9Raw_sound (a : PairSlot) :
    (CA2_3_11I1R9Raw a).Encloses (CA2_3_11I1R9Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA2_3_11I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R9Certificates_valid :
    CA2_3_11I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R9Certificates (CA2_3_11I1R9CertificateIndex a)).input
lemma CA2_3_11I1R9P_check : ∀ a : PairSlot, contains (CA2_3_11I1R9Raw a) (CA2_3_11I1R9P a) = true := by
  decide +kernel
lemma CA2_3_11I1R9P_sound (a : PairSlot) :
    (CA2_3_11I1R9P a).Encloses (CA2_3_11I1R9Value a) :=
  contains_sound (CA2_3_11I1R9Raw_sound a) (CA2_3_11I1R9P_check a)
def CA2_3_11I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R9Certificates (CA2_3_11I1R9CertificateIndex a)).output
lemma CA2_3_11I1R9Terms_sound (a : PairSlot) :
    (CA2_3_11I1R9Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R9Certificates_valid
    (CA2_3_11I1R9CertificateIndex a) (CA2_3_11I1R9P_sound a)
def CA2_3_11I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R9Entropy_sound : CA2_3_11I1R9Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R9Value CA2_3_11I1R9Terms CA2_3_11I1R9Terms_sound) (by decide +kernel)
def CA2_3_11I1R9Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R9Mass_sound : CA2_3_11I1R9Mass.Encloses (∑ a, CA2_3_11I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R9P CA2_3_11I1R9Value CA2_3_11I1R9P_sound) (by decide +kernel)
def CA2_3_11I1R9MassTerm : Ball := .exact 0
lemma CA2_3_11I1R9MassTerm_sound : CA2_3_11I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R9Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R9Mass_sound)
def CA2_3_11I1R9H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R9H_sound : CA2_3_11I1R9H.Encloses (homogeneousEntropy CA2_3_11I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R9Value CA2_3_11I1R9MassTerm_sound CA2_3_11I1R9Entropy_sound) (by decide +kernel)
def CA2_3_11I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA2_3_11I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA2_3_11I1R10Raw_sound (a : PairSlot) :
    (CA2_3_11I1R10Raw a).Encloses (CA2_3_11I1R10Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA2_3_11I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R10Certificates_valid :
    CA2_3_11I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R10Certificates (CA2_3_11I1R10CertificateIndex a)).input
lemma CA2_3_11I1R10P_check : ∀ a : PairSlot, contains (CA2_3_11I1R10Raw a) (CA2_3_11I1R10P a) = true := by
  decide +kernel
lemma CA2_3_11I1R10P_sound (a : PairSlot) :
    (CA2_3_11I1R10P a).Encloses (CA2_3_11I1R10Value a) :=
  contains_sound (CA2_3_11I1R10Raw_sound a) (CA2_3_11I1R10P_check a)
def CA2_3_11I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R10Certificates (CA2_3_11I1R10CertificateIndex a)).output
lemma CA2_3_11I1R10Terms_sound (a : PairSlot) :
    (CA2_3_11I1R10Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R10Certificates_valid
    (CA2_3_11I1R10CertificateIndex a) (CA2_3_11I1R10P_sound a)
def CA2_3_11I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R10Entropy_sound : CA2_3_11I1R10Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R10Value CA2_3_11I1R10Terms CA2_3_11I1R10Terms_sound) (by decide +kernel)
def CA2_3_11I1R10Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R10Mass_sound : CA2_3_11I1R10Mass.Encloses (∑ a, CA2_3_11I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R10P CA2_3_11I1R10Value CA2_3_11I1R10P_sound) (by decide +kernel)
def CA2_3_11I1R10MassTerm : Ball := .exact 0
lemma CA2_3_11I1R10MassTerm_sound : CA2_3_11I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R10Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R10Mass_sound)
def CA2_3_11I1R10H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R10H_sound : CA2_3_11I1R10H.Encloses (homogeneousEntropy CA2_3_11I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R10Value CA2_3_11I1R10MassTerm_sound CA2_3_11I1R10Entropy_sound) (by decide +kernel)
def CA2_3_11I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA2_3_11I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA2_3_11I1R11Raw_sound (a : PairSlot) :
    (CA2_3_11I1R11Raw a).Encloses (CA2_3_11I1R11Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA2_3_11I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R11Certificates_valid :
    CA2_3_11I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R11Certificates (CA2_3_11I1R11CertificateIndex a)).input
lemma CA2_3_11I1R11P_check : ∀ a : PairSlot, contains (CA2_3_11I1R11Raw a) (CA2_3_11I1R11P a) = true := by
  decide +kernel
lemma CA2_3_11I1R11P_sound (a : PairSlot) :
    (CA2_3_11I1R11P a).Encloses (CA2_3_11I1R11Value a) :=
  contains_sound (CA2_3_11I1R11Raw_sound a) (CA2_3_11I1R11P_check a)
def CA2_3_11I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R11Certificates (CA2_3_11I1R11CertificateIndex a)).output
lemma CA2_3_11I1R11Terms_sound (a : PairSlot) :
    (CA2_3_11I1R11Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R11Certificates_valid
    (CA2_3_11I1R11CertificateIndex a) (CA2_3_11I1R11P_sound a)
def CA2_3_11I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R11Entropy_sound : CA2_3_11I1R11Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R11Value CA2_3_11I1R11Terms CA2_3_11I1R11Terms_sound) (by decide +kernel)
def CA2_3_11I1R11Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R11Mass_sound : CA2_3_11I1R11Mass.Encloses (∑ a, CA2_3_11I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R11P CA2_3_11I1R11Value CA2_3_11I1R11P_sound) (by decide +kernel)
def CA2_3_11I1R11MassTerm : Ball := .exact 0
lemma CA2_3_11I1R11MassTerm_sound : CA2_3_11I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R11Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R11Mass_sound)
def CA2_3_11I1R11H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R11H_sound : CA2_3_11I1R11H.Encloses (homogeneousEntropy CA2_3_11I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R11Value CA2_3_11I1R11MassTerm_sound CA2_3_11I1R11Entropy_sound) (by decide +kernel)
def CA2_3_11I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA2_3_11I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA2_3_11I1R12Raw_sound (a : PairSlot) :
    (CA2_3_11I1R12Raw a).Encloses (CA2_3_11I1R12Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA2_3_11I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R12Certificates_valid :
    CA2_3_11I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R12Certificates (CA2_3_11I1R12CertificateIndex a)).input
lemma CA2_3_11I1R12P_check : ∀ a : PairSlot, contains (CA2_3_11I1R12Raw a) (CA2_3_11I1R12P a) = true := by
  decide +kernel
lemma CA2_3_11I1R12P_sound (a : PairSlot) :
    (CA2_3_11I1R12P a).Encloses (CA2_3_11I1R12Value a) :=
  contains_sound (CA2_3_11I1R12Raw_sound a) (CA2_3_11I1R12P_check a)
def CA2_3_11I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R12Certificates (CA2_3_11I1R12CertificateIndex a)).output
lemma CA2_3_11I1R12Terms_sound (a : PairSlot) :
    (CA2_3_11I1R12Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R12Certificates_valid
    (CA2_3_11I1R12CertificateIndex a) (CA2_3_11I1R12P_sound a)
def CA2_3_11I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R12Entropy_sound : CA2_3_11I1R12Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R12Value CA2_3_11I1R12Terms CA2_3_11I1R12Terms_sound) (by decide +kernel)
def CA2_3_11I1R12Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R12Mass_sound : CA2_3_11I1R12Mass.Encloses (∑ a, CA2_3_11I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R12P CA2_3_11I1R12Value CA2_3_11I1R12P_sound) (by decide +kernel)
def CA2_3_11I1R12MassTerm : Ball := .exact 0
lemma CA2_3_11I1R12MassTerm_sound : CA2_3_11I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R12Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R12Mass_sound)
def CA2_3_11I1R12H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R12H_sound : CA2_3_11I1R12H.Encloses (homogeneousEntropy CA2_3_11I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R12Value CA2_3_11I1R12MassTerm_sound CA2_3_11I1R12Entropy_sound) (by decide +kernel)
def CA2_3_11I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA2_3_11I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA2_3_11I1R13Raw_sound (a : PairSlot) :
    (CA2_3_11I1R13Raw a).Encloses (CA2_3_11I1R13Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA2_3_11I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R13Certificates_valid :
    CA2_3_11I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R13Certificates (CA2_3_11I1R13CertificateIndex a)).input
lemma CA2_3_11I1R13P_check : ∀ a : PairSlot, contains (CA2_3_11I1R13Raw a) (CA2_3_11I1R13P a) = true := by
  decide +kernel
lemma CA2_3_11I1R13P_sound (a : PairSlot) :
    (CA2_3_11I1R13P a).Encloses (CA2_3_11I1R13Value a) :=
  contains_sound (CA2_3_11I1R13Raw_sound a) (CA2_3_11I1R13P_check a)
def CA2_3_11I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R13Certificates (CA2_3_11I1R13CertificateIndex a)).output
lemma CA2_3_11I1R13Terms_sound (a : PairSlot) :
    (CA2_3_11I1R13Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R13Certificates_valid
    (CA2_3_11I1R13CertificateIndex a) (CA2_3_11I1R13P_sound a)
def CA2_3_11I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R13Entropy_sound : CA2_3_11I1R13Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R13Value CA2_3_11I1R13Terms CA2_3_11I1R13Terms_sound) (by decide +kernel)
def CA2_3_11I1R13Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R13Mass_sound : CA2_3_11I1R13Mass.Encloses (∑ a, CA2_3_11I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R13P CA2_3_11I1R13Value CA2_3_11I1R13P_sound) (by decide +kernel)
def CA2_3_11I1R13MassTerm : Ball := .exact 0
lemma CA2_3_11I1R13MassTerm_sound : CA2_3_11I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R13Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R13Mass_sound)
def CA2_3_11I1R13H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R13H_sound : CA2_3_11I1R13H.Encloses (homogeneousEntropy CA2_3_11I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R13Value CA2_3_11I1R13MassTerm_sound CA2_3_11I1R13Entropy_sound) (by decide +kernel)
def CA2_3_11I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA2_3_11I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA2_3_11I1R14Raw_sound (a : PairSlot) :
    (CA2_3_11I1R14Raw a).Encloses (CA2_3_11I1R14Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA2_3_11I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R14Certificates_valid :
    CA2_3_11I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R14Certificates (CA2_3_11I1R14CertificateIndex a)).input
lemma CA2_3_11I1R14P_check : ∀ a : PairSlot, contains (CA2_3_11I1R14Raw a) (CA2_3_11I1R14P a) = true := by
  decide +kernel
lemma CA2_3_11I1R14P_sound (a : PairSlot) :
    (CA2_3_11I1R14P a).Encloses (CA2_3_11I1R14Value a) :=
  contains_sound (CA2_3_11I1R14Raw_sound a) (CA2_3_11I1R14P_check a)
def CA2_3_11I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R14Certificates (CA2_3_11I1R14CertificateIndex a)).output
lemma CA2_3_11I1R14Terms_sound (a : PairSlot) :
    (CA2_3_11I1R14Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R14Certificates_valid
    (CA2_3_11I1R14CertificateIndex a) (CA2_3_11I1R14P_sound a)
def CA2_3_11I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R14Entropy_sound : CA2_3_11I1R14Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R14Value CA2_3_11I1R14Terms CA2_3_11I1R14Terms_sound) (by decide +kernel)
def CA2_3_11I1R14Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R14Mass_sound : CA2_3_11I1R14Mass.Encloses (∑ a, CA2_3_11I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R14P CA2_3_11I1R14Value CA2_3_11I1R14P_sound) (by decide +kernel)
def CA2_3_11I1R14MassTerm : Ball := .exact 0
lemma CA2_3_11I1R14MassTerm_sound : CA2_3_11I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R14Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R14Mass_sound)
def CA2_3_11I1R14H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R14H_sound : CA2_3_11I1R14H.Encloses (homogeneousEntropy CA2_3_11I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R14Value CA2_3_11I1R14MassTerm_sound CA2_3_11I1R14Entropy_sound) (by decide +kernel)
def CA2_3_11I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA2_3_11I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA2_3_11I1R15Raw_sound (a : PairSlot) :
    (CA2_3_11I1R15Raw a).Encloses (CA2_3_11I1R15Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA2_3_11I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R15Certificates_valid :
    CA2_3_11I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R15Certificates (CA2_3_11I1R15CertificateIndex a)).input
lemma CA2_3_11I1R15P_check : ∀ a : PairSlot, contains (CA2_3_11I1R15Raw a) (CA2_3_11I1R15P a) = true := by
  decide +kernel
lemma CA2_3_11I1R15P_sound (a : PairSlot) :
    (CA2_3_11I1R15P a).Encloses (CA2_3_11I1R15Value a) :=
  contains_sound (CA2_3_11I1R15Raw_sound a) (CA2_3_11I1R15P_check a)
def CA2_3_11I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R15Certificates (CA2_3_11I1R15CertificateIndex a)).output
lemma CA2_3_11I1R15Terms_sound (a : PairSlot) :
    (CA2_3_11I1R15Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R15Certificates_valid
    (CA2_3_11I1R15CertificateIndex a) (CA2_3_11I1R15P_sound a)
def CA2_3_11I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R15Entropy_sound : CA2_3_11I1R15Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R15Value CA2_3_11I1R15Terms CA2_3_11I1R15Terms_sound) (by decide +kernel)
def CA2_3_11I1R15Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R15Mass_sound : CA2_3_11I1R15Mass.Encloses (∑ a, CA2_3_11I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R15P CA2_3_11I1R15Value CA2_3_11I1R15P_sound) (by decide +kernel)
def CA2_3_11I1R15MassTerm : Ball := .exact 0
lemma CA2_3_11I1R15MassTerm_sound : CA2_3_11I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R15Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R15Mass_sound)
def CA2_3_11I1R15H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R15H_sound : CA2_3_11I1R15H.Encloses (homogeneousEntropy CA2_3_11I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R15Value CA2_3_11I1R15MassTerm_sound CA2_3_11I1R15Entropy_sound) (by decide +kernel)
def CA2_3_11I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA2_3_11I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA2_3_11I1R16Raw_sound (a : PairSlot) :
    (CA2_3_11I1R16Raw a).Encloses (CA2_3_11I1R16Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA2_3_11I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I1R16Certificates_valid :
    CA2_3_11I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R16Certificates (CA2_3_11I1R16CertificateIndex a)).input
lemma CA2_3_11I1R16P_check : ∀ a : PairSlot, contains (CA2_3_11I1R16Raw a) (CA2_3_11I1R16P a) = true := by
  decide +kernel
lemma CA2_3_11I1R16P_sound (a : PairSlot) :
    (CA2_3_11I1R16P a).Encloses (CA2_3_11I1R16Value a) :=
  contains_sound (CA2_3_11I1R16Raw_sound a) (CA2_3_11I1R16P_check a)
def CA2_3_11I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I1R16Certificates (CA2_3_11I1R16CertificateIndex a)).output
lemma CA2_3_11I1R16Terms_sound (a : PairSlot) :
    (CA2_3_11I1R16Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1R16Certificates_valid
    (CA2_3_11I1R16CertificateIndex a) (CA2_3_11I1R16P_sound a)
def CA2_3_11I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R16Entropy_sound : CA2_3_11I1R16Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I1R16Value CA2_3_11I1R16Terms CA2_3_11I1R16Terms_sound) (by decide +kernel)
def CA2_3_11I1R16Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R16Mass_sound : CA2_3_11I1R16Mass.Encloses (∑ a, CA2_3_11I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I1R16P CA2_3_11I1R16Value CA2_3_11I1R16P_sound) (by decide +kernel)
def CA2_3_11I1R16MassTerm : Ball := .exact 0
lemma CA2_3_11I1R16MassTerm_sound : CA2_3_11I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1R16Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I1R16Mass_sound)
def CA2_3_11I1R16H : Ball := ⟨0, 0⟩
lemma CA2_3_11I1R16H_sound : CA2_3_11I1R16H.Encloses (homogeneousEntropy CA2_3_11I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1R16Value CA2_3_11I1R16MassTerm_sound CA2_3_11I1R16Entropy_sound) (by decide +kernel)
def CA2_3_11I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_3_11I1R0H
  | 1 => CA2_3_11I1R1H
  | 2 => CA2_3_11I1R2H
  | 3 => CA2_3_11I1R3H
  | 4 => CA2_3_11I1R4H
  | 5 => CA2_3_11I1R5H
  | 6 => CA2_3_11I1R6H
  | 7 => CA2_3_11I1R7H
  | 8 => CA2_3_11I1R8H
  | 9 => CA2_3_11I1R9H
  | 10 => CA2_3_11I1R10H
  | 11 => CA2_3_11I1R11H
  | 12 => CA2_3_11I1R12H
  | 13 => CA2_3_11I1R13H
  | 14 => CA2_3_11I1R14H
  | 15 => CA2_3_11I1R15H
  | 16 => CA2_3_11I1R16H
  | _ => (.exact 0)
lemma CA2_3_11I1ResidualEntropies_sound (k : Fin 17) :
    (CA2_3_11I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_3_11I1R0H_sound
  · exact CA2_3_11I1R1H_sound
  · exact CA2_3_11I1R2H_sound
  · exact CA2_3_11I1R3H_sound
  · exact CA2_3_11I1R4H_sound
  · exact CA2_3_11I1R5H_sound
  · exact CA2_3_11I1R6H_sound
  · exact CA2_3_11I1R7H_sound
  · exact CA2_3_11I1R8H_sound
  · exact CA2_3_11I1R9H_sound
  · exact CA2_3_11I1R10H_sound
  · exact CA2_3_11I1R11H_sound
  · exact CA2_3_11I1R12H_sound
  · exact CA2_3_11I1R13H_sound
  · exact CA2_3_11I1R14H_sound
  · exact CA2_3_11I1R15H_sound
  · exact CA2_3_11I1R16H_sound
def CA2_3_11I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
lemma CA2_3_11I1Singles_sound (u : Shape) (hu : u ∈ below (shape 2 3 11))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA2_3_11I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A2_3_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 0 8) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 1 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 0 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 0 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 3 3) by decide +kernel) hd |>.elim
def CA2_3_11I1Singleton : Ball := ⟨0, 0⟩
lemma CA2_3_11I1Singleton_sound : CA2_3_11I1Singleton.Encloses
    (singletonEntropy (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA2_3_11I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_3_11Law_sound u) CA2_3_11I1Singles_sound) (by decide +kernel)
def CA2_3_11I1Group : Ball := ⟨(40547548289135019042455092632257 / 50000000000000000000000000000000), (84544215161 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I1Group_sound : CA2_3_11I1Group.Encloses
    (groupedEntropy (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_3_11I1Singleton_sound
    (finSumBall_sound 17 CA2_3_11I1ResidualEntropies _ CA2_3_11I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA2_3_11I1H : Ball := ⟨(15078094069919404912919609627283 / 12500000000000000000000000000000), (501523413739 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I1_sound : CA2_3_11I1H.Encloses (stageACapacity (shape 2 3 11) 1) := by
  have hb := contains_sound (Ball.add_sound CA2_3_11I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA2_3_11I1Group_sound)))
    (show contains (.add CA2_3_11I1PairH (.neg (.mul (.exact 2) CA2_3_11I1Group))) CA2_3_11I1H = true by decide +kernel)
  unfold CA2_3_11I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
