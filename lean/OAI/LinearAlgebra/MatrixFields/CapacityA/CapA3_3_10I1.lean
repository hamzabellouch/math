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
def CA3_3_10I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 3 3 10)) (shape 3 3 10) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA3_3_10I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 3 3 10) A3_3_10Law 1 a
lemma CA3_3_10I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA3_3_10I1PairRaw a).Encloses (CA3_3_10I1PairValue a) := by
  exact stageAPairBall_sound (shape 3 3 10) (by decide +kernel) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (fun u _ => A3_3_10Law_sound u) 1 a
def CA3_3_10I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(4619054651167277020629531838693 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩ ⟨(14203501238427614750271209133991 / 100000000000000000000000000000000), (5868737311 / 100000000000000000000000000000000)⟩ ⟨(-307498012279163250732354083952271 / 100000000000000000000000000000000), (127054942617 / 100000000000000000000000000000000)⟩ ⟨-5, 4619054651167277020629531838693, 3125000000000000000000000000000⟩,
   .log ⟨(8871250693737520079598966291 / 2000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1201630128356614022253786080439 / 50000000000000000000000000000000), (422676101 / 50000000000000000000000000000000)⟩ ⟨(-541808667048437937517112002272391 / 100000000000000000000000000000000), (95291206911 / 50000000000000000000000000000000)⟩ ⟨-8, 8871250693737520079598966291, 7812500000000000000000000000⟩,
   .log ⟨(205890417481175314177510224919 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1273551935099509918164620566777 / 100000000000000000000000000000000), (435989933 / 100000000000000000000000000000000)⟩ ⟨(-618558139169323674081473370489413 / 100000000000000000000000000000000), (211758237801 / 100000000000000000000000000000000)⟩ ⟨-9, 205890417481175314177510224919, 195312500000000000000000000000⟩,
   .log ⟨(12369411578640493863887606112473 / 100000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩ ⟨(25851372182769150597570746307719 / 100000000000000000000000000000000), (13096624063 / 100000000000000000000000000000000)⟩ ⟨(-104497178456771998300419614782573 / 50000000000000000000000000000000), (52939559377 / 50000000000000000000000000000000)⟩ ⟨-4, 12369411578640493863887606112473, 6250000000000000000000000000000⟩,
   .log ⟨(522296892672814704126252563 / 15625000000000000000000000000), (9 / 50000000000000000000000000000000)⟩ ⟨(11359802944430633853842515363723 / 100000000000000000000000000000000), (4247065773 / 100000000000000000000000000000000)⟩ ⟨(-67967825769899427637754912757131 / 20000000000000000000000000000000), (31763735659 / 25000000000000000000000000000000)⟩ ⟨-5, 522296892672814704126252563, 488281250000000000000000000⟩,
   .log ⟨(338340295906074792254685351483 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(15037305234827450456760484733 / 781250000000000000000000000000), (716463459 / 100000000000000000000000000000000)⟩ ⟨(-17777729010442070054965821551063 / 3125000000000000000000000000000), (211758237421 / 100000000000000000000000000000000)⟩ ⟨-9, 338340295906074792254685351483, 195312500000000000000000000000⟩]
lemma CA3_3_10I1PairCertificates_valid :
    CA3_3_10I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 2, 1 => 1
  | 0, 0, 3, 1 => 2
  | 0, 0, 4, 0 => 3
  | 0, 0, 1, 2 => 1
  | 0, 0, 1, 3 => 2
  | 0, 0, 0, 4 => 3
  | 1, 0, 1, 1 => 4
  | 1, 0, 2, 0 => 5
  | 1, 0, 3, 0 => 6
  | 1, 0, 0, 2 => 5
  | 1, 0, 0, 3 => 6
  | 0, 1, 1, 1 => 4
  | 0, 1, 2, 0 => 5
  | 0, 1, 3, 0 => 6
  | 0, 1, 0, 2 => 5
  | 0, 1, 0, 3 => 6
  | 2, 0, 0, 1 => 5
  | 2, 0, 1, 0 => 5
  | 3, 0, 0, 1 => 6
  | 3, 0, 1, 0 => 6
  | 1, 1, 0, 1 => 4
  | 1, 1, 1, 0 => 4
  | 0, 2, 0, 1 => 5
  | 0, 2, 1, 0 => 5
  | 0, 3, 0, 1 => 6
  | 0, 3, 1, 0 => 6
  | 4, 0, 0, 0 => 3
  | 2, 1, 0, 0 => 1
  | 3, 1, 0, 0 => 2
  | 1, 2, 0, 0 => 1
  | 1, 3, 0, 0 => 2
  | 0, 4, 0, 0 => 3
  | _, _, _, _ => 0
def CA3_3_10I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1PairCertificates (CA3_3_10I1PairCertificateIndex a)).input
lemma CA3_3_10I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((0,0),(k,l))) (CA3_3_10I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((0,1),(k,l))) (CA3_3_10I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((0,2),(k,l))) (CA3_3_10I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((0,3),(k,l))) (CA3_3_10I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((0,4),(k,l))) (CA3_3_10I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((0,5),(k,l))) (CA3_3_10I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((1,0),(k,l))) (CA3_3_10I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((1,1),(k,l))) (CA3_3_10I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((1,2),(k,l))) (CA3_3_10I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((1,3),(k,l))) (CA3_3_10I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((1,4),(k,l))) (CA3_3_10I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((1,5),(k,l))) (CA3_3_10I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((2,0),(k,l))) (CA3_3_10I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((2,1),(k,l))) (CA3_3_10I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((2,2),(k,l))) (CA3_3_10I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((2,3),(k,l))) (CA3_3_10I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((2,4),(k,l))) (CA3_3_10I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((2,5),(k,l))) (CA3_3_10I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((3,0),(k,l))) (CA3_3_10I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((3,1),(k,l))) (CA3_3_10I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((3,2),(k,l))) (CA3_3_10I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((3,3),(k,l))) (CA3_3_10I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((3,4),(k,l))) (CA3_3_10I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((3,5),(k,l))) (CA3_3_10I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((4,0),(k,l))) (CA3_3_10I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((4,1),(k,l))) (CA3_3_10I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((4,2),(k,l))) (CA3_3_10I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((4,3),(k,l))) (CA3_3_10I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((4,4),(k,l))) (CA3_3_10I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((4,5),(k,l))) (CA3_3_10I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((5,0),(k,l))) (CA3_3_10I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((5,1),(k,l))) (CA3_3_10I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((5,2),(k,l))) (CA3_3_10I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((5,3),(k,l))) (CA3_3_10I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((5,4),(k,l))) (CA3_3_10I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA3_3_10I1PairRaw ((5,5),(k,l))) (CA3_3_10I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA3_3_10I1PairP_check (a : PairSlot × PairSlot) : contains (CA3_3_10I1PairRaw a) (CA3_3_10I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA3_3_10I1PairP_check_0_0 k l) (CA3_3_10I1PairP_check_0_1 k l) (CA3_3_10I1PairP_check_0_2 k l) (CA3_3_10I1PairP_check_0_3 k l) (CA3_3_10I1PairP_check_0_4 k l) (CA3_3_10I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA3_3_10I1PairP_check_1_0 k l) (CA3_3_10I1PairP_check_1_1 k l) (CA3_3_10I1PairP_check_1_2 k l) (CA3_3_10I1PairP_check_1_3 k l) (CA3_3_10I1PairP_check_1_4 k l) (CA3_3_10I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA3_3_10I1PairP_check_2_0 k l) (CA3_3_10I1PairP_check_2_1 k l) (CA3_3_10I1PairP_check_2_2 k l) (CA3_3_10I1PairP_check_2_3 k l) (CA3_3_10I1PairP_check_2_4 k l) (CA3_3_10I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA3_3_10I1PairP_check_3_0 k l) (CA3_3_10I1PairP_check_3_1 k l) (CA3_3_10I1PairP_check_3_2 k l) (CA3_3_10I1PairP_check_3_3 k l) (CA3_3_10I1PairP_check_3_4 k l) (CA3_3_10I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA3_3_10I1PairP_check_4_0 k l) (CA3_3_10I1PairP_check_4_1 k l) (CA3_3_10I1PairP_check_4_2 k l) (CA3_3_10I1PairP_check_4_3 k l) (CA3_3_10I1PairP_check_4_4 k l) (CA3_3_10I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA3_3_10I1PairP_check_5_0 k l) (CA3_3_10I1PairP_check_5_1 k l) (CA3_3_10I1PairP_check_5_2 k l) (CA3_3_10I1PairP_check_5_3 k l) (CA3_3_10I1PairP_check_5_4 k l) (CA3_3_10I1PairP_check_5_5 k l)
lemma CA3_3_10I1PairP_sound (a : PairSlot × PairSlot) :
    (CA3_3_10I1PairP a).Encloses (CA3_3_10I1PairValue a) :=
  contains_sound (CA3_3_10I1PairRaw_sound a) (CA3_3_10I1PairP_check a)
def CA3_3_10I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1PairCertificates (CA3_3_10I1PairCertificateIndex a)).output
lemma CA3_3_10I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA3_3_10I1PairTerms a).Encloses (Foundation.entropyTerm (CA3_3_10I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1PairCertificates_valid
    (CA3_3_10I1PairCertificateIndex a) (CA3_3_10I1PairP_sound a)
def CA3_3_10I1PairEntropy : Ball := ⟨(70300841641986598335129862988459 / 25000000000000000000000000000000), (30173761973 / 25000000000000000000000000000000)⟩
lemma CA3_3_10I1PairEntropy_sound : CA3_3_10I1PairEntropy.Encloses (Foundation.finiteEntropy CA3_3_10I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA3_3_10I1PairValue CA3_3_10I1PairTerms CA3_3_10I1PairTerms_sound) (by decide +kernel)
def CA3_3_10I1PairMass : Ball := ⟨(25000000000000000000000000000001 / 25000000000000000000000000000000), (111 / 25000000000000000000000000000000)⟩
lemma CA3_3_10I1PairMass_sound : CA3_3_10I1PairMass.Encloses (∑ a, CA3_3_10I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA3_3_10I1PairP CA3_3_10I1PairValue CA3_3_10I1PairP_sound) (by decide +kernel)
def CA3_3_10I1PairMassTermLogWitness : LogWitness := ⟨0, 25000000000000000000000000000001, 25000000000000000000000000000000⟩
def CA3_3_10I1PairMassTermLog : Ball := ⟨(1 / 25000000000000000000000000000000), (10587912063 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I1PairMassTermLog_sound : CA3_3_10I1PairMassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I1PairMass_sound) (w := CA3_3_10I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_3_10I1PairMassTerm : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175824127 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I1PairMassTerm_sound : CA3_3_10I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I1PairMass_sound) CA3_3_10I1PairMassTermLog_sound) (by decide +kernel)
def CA3_3_10I1PairH : Ball := ⟨(3515042082099329916756493149423 / 1250000000000000000000000000000), (141870872019 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I1PairH_sound : CA3_3_10I1PairH.Encloses (homogeneousEntropy CA3_3_10I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1PairValue CA3_3_10I1PairMassTerm_sound CA3_3_10I1PairEntropy_sound) (by decide +kernel)

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
def CA3_3_10I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA3_3_10I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA3_3_10I1R0Raw_sound (a : PairSlot) :
    (CA3_3_10I1R0Raw a).Encloses (CA3_3_10I1R0Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA3_3_10I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2634253801667664169393495189081 / 25000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩ ⟨(23711191063531435570046086221241 / 100000000000000000000000000000000), (5578249471 / 50000000000000000000000000000000)⟩ ⟨(-14064224188767788938283650303749 / 6250000000000000000000000000000), (26469779701 / 25000000000000000000000000000000)⟩ ⟨-4, 2634253801667664169393495189081, 1562500000000000000000000000000⟩]
lemma CA3_3_10I1R0Certificates_valid :
    CA3_3_10I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA3_3_10I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R0Certificates (CA3_3_10I1R0CertificateIndex a)).input
lemma CA3_3_10I1R0P_check : ∀ a : PairSlot, contains (CA3_3_10I1R0Raw a) (CA3_3_10I1R0P a) = true := by
  decide +kernel
lemma CA3_3_10I1R0P_sound (a : PairSlot) :
    (CA3_3_10I1R0P a).Encloses (CA3_3_10I1R0Value a) :=
  contains_sound (CA3_3_10I1R0Raw_sound a) (CA3_3_10I1R0P_check a)
def CA3_3_10I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R0Certificates (CA3_3_10I1R0CertificateIndex a)).output
lemma CA3_3_10I1R0Terms_sound (a : PairSlot) :
    (CA3_3_10I1R0Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R0Certificates_valid
    (CA3_3_10I1R0CertificateIndex a) (CA3_3_10I1R0P_sound a)
def CA3_3_10I1R0Entropy : Ball := ⟨(23711191063531435570046086221241 / 100000000000000000000000000000000), (5578249471 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I1R0Entropy_sound : CA3_3_10I1R0Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R0Value CA3_3_10I1R0Terms CA3_3_10I1R0Terms_sound) (by decide +kernel)
def CA3_3_10I1R0Mass : Ball := ⟨(2634253801667664169393495189081 / 25000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I1R0Mass_sound : CA3_3_10I1R0Mass.Encloses (∑ a, CA3_3_10I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R0P CA3_3_10I1R0Value CA3_3_10I1R0P_sound) (by decide +kernel)
def CA3_3_10I1R0MassTermLogWitness : LogWitness := ⟨-4, 2634253801667664169393495189081, 1562500000000000000000000000000⟩
def CA3_3_10I1R0MassTermLog : Ball := ⟨(-14064224188767788938283650303749 / 6250000000000000000000000000000), (26469779701 / 25000000000000000000000000000000)⟩
lemma CA3_3_10I1R0MassTermLog_sound : CA3_3_10I1R0MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I1R0Mass_sound) (w := CA3_3_10I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_3_10I1R0MassTerm : Ball := ⟨(23711191063531435570046086221241 / 100000000000000000000000000000000), (5578249471 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I1R0MassTerm_sound : CA3_3_10I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I1R0Mass_sound) CA3_3_10I1R0MassTermLog_sound) (by decide +kernel)
def CA3_3_10I1R0H : Ball := ⟨0, (5578249471 / 25000000000000000000000000000000)⟩
lemma CA3_3_10I1R0H_sound : CA3_3_10I1R0H.Encloses (homogeneousEntropy CA3_3_10I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R0Value CA3_3_10I1R0MassTerm_sound CA3_3_10I1R0Entropy_sound) (by decide +kernel)
def CA3_3_10I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA3_3_10I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA3_3_10I1R1Raw_sound (a : PairSlot) :
    (CA3_3_10I1R1Raw a).Encloses (CA3_3_10I1R1Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA3_3_10I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(9865746198332335830606504810919 / 50000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩ ⟨(32023309006516069604011097727319 / 100000000000000000000000000000000), (8356612147 / 50000000000000000000000000000000)⟩ ⟨(-8114771139138252622148038346787 / 5000000000000000000000000000000), (8470329499 / 10000000000000000000000000000000)⟩ ⟨-3, 9865746198332335830606504810919, 6250000000000000000000000000000⟩]
lemma CA3_3_10I1R1Certificates_valid :
    CA3_3_10I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA3_3_10I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R1Certificates (CA3_3_10I1R1CertificateIndex a)).input
lemma CA3_3_10I1R1P_check : ∀ a : PairSlot, contains (CA3_3_10I1R1Raw a) (CA3_3_10I1R1P a) = true := by
  decide +kernel
lemma CA3_3_10I1R1P_sound (a : PairSlot) :
    (CA3_3_10I1R1P a).Encloses (CA3_3_10I1R1Value a) :=
  contains_sound (CA3_3_10I1R1Raw_sound a) (CA3_3_10I1R1P_check a)
def CA3_3_10I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R1Certificates (CA3_3_10I1R1CertificateIndex a)).output
lemma CA3_3_10I1R1Terms_sound (a : PairSlot) :
    (CA3_3_10I1R1Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R1Certificates_valid
    (CA3_3_10I1R1CertificateIndex a) (CA3_3_10I1R1P_sound a)
def CA3_3_10I1R1Entropy : Ball := ⟨(32023309006516069604011097727319 / 50000000000000000000000000000000), (8356612147 / 25000000000000000000000000000000)⟩
lemma CA3_3_10I1R1Entropy_sound : CA3_3_10I1R1Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R1Value CA3_3_10I1R1Terms CA3_3_10I1R1Terms_sound) (by decide +kernel)
def CA3_3_10I1R1Mass : Ball := ⟨(9865746198332335830606504810919 / 25000000000000000000000000000000), (51 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I1R1Mass_sound : CA3_3_10I1R1Mass.Encloses (∑ a, CA3_3_10I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R1P CA3_3_10I1R1Value CA3_3_10I1R1P_sound) (by decide +kernel)
def CA3_3_10I1R1MassTermLogWitness : LogWitness := ⟨-2, 9865746198332335830606504810919, 6250000000000000000000000000000⟩
def CA3_3_10I1R1MassTermLog : Ball := ⟨(-9298070472677052150123757388541 / 10000000000000000000000000000000), (63527471307 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I1R1MassTermLog_sound : CA3_3_10I1R1MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I1R1Mass_sound) (w := CA3_3_10I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_3_10I1R1MassTerm : Ball := ⟨(17916485042507767989356665939 / 48828125000000000000000000000), (25069836437 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I1R1MassTerm_sound : CA3_3_10I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I1R1Mass_sound) CA3_3_10I1R1MassTermLog_sound) (by decide +kernel)
def CA3_3_10I1R1H : Ball := ⟨(13676828322988115182909871805783 / 50000000000000000000000000000000), (2339851401 / 4000000000000000000000000000000)⟩
lemma CA3_3_10I1R1H_sound : CA3_3_10I1R1H.Encloses (homogeneousEntropy CA3_3_10I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R1Value CA3_3_10I1R1MassTerm_sound CA3_3_10I1R1Entropy_sound) (by decide +kernel)
def CA3_3_10I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA3_3_10I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA3_3_10I1R2Raw_sound (a : PairSlot) :
    (CA3_3_10I1R2Raw a).Encloses (CA3_3_10I1R2Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA3_3_10I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(522296892672814704126252563 / 7812500000000000000000000000), (3 / 10000000000000000000000000000000)⟩ ⟨(1808563957114757977164683124919 / 10000000000000000000000000000000), (3539221467 / 50000000000000000000000000000000)⟩ ⟨(-10820976431740104289882054829413 / 4000000000000000000000000000000), (105879118863 / 100000000000000000000000000000000)⟩ ⟨-4, 522296892672814704126252563, 488281250000000000000000000⟩,
   .log ⟨(338340295906074792254685351483 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(676102179152320123866190477321 / 20000000000000000000000000000000), (644817113 / 50000000000000000000000000000000)⟩ ⟨(-249786305139075855408591548291843 / 50000000000000000000000000000000), (95291206869 / 50000000000000000000000000000000)⟩ ⟨-8, 338340295906074792254685351483, 195312500000000000000000000000⟩,
   .log ⟨(4947764631456197545555042444989 / 20000000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩ ⟨(8638774710924475024149402842617 / 25000000000000000000000000000000), (1309662403 / 6250000000000000000000000000000)⟩ ⟨(-6983981942877473282955801825741 / 5000000000000000000000000000000), (42351647497 / 50000000000000000000000000000000)⟩ ⟨-3, 4947764631456197545555042444989, 2500000000000000000000000000000⟩]
lemma CA3_3_10I1R2Certificates_valid :
    CA3_3_10I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA3_3_10I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R2Certificates (CA3_3_10I1R2CertificateIndex a)).input
lemma CA3_3_10I1R2P_check : ∀ a : PairSlot, contains (CA3_3_10I1R2Raw a) (CA3_3_10I1R2P a) = true := by
  decide +kernel
lemma CA3_3_10I1R2P_sound (a : PairSlot) :
    (CA3_3_10I1R2P a).Encloses (CA3_3_10I1R2Value a) :=
  contains_sound (CA3_3_10I1R2Raw_sound a) (CA3_3_10I1R2P_check a)
def CA3_3_10I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R2Certificates (CA3_3_10I1R2CertificateIndex a)).output
lemma CA3_3_10I1R2Terms_sound (a : PairSlot) :
    (CA3_3_10I1R2Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R2Certificates_valid
    (CA3_3_10I1R2CertificateIndex a) (CA3_3_10I1R2P_sound a)
def CA3_3_10I1R2Entropy : Ball := ⟨(38743699888758130439276589321029 / 50000000000000000000000000000000), (147229503 / 390625000000000000000000000000)⟩
lemma CA3_3_10I1R2Entropy_sound : CA3_3_10I1R2Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R2Value CA3_3_10I1R2Terms CA3_3_10I1R2Terms_sound) (by decide +kernel)
def CA3_3_10I1R2Mass : Ball := ⟨(39462984793329343322426019243677 / 100000000000000000000000000000000), (133 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I1R2Mass_sound : CA3_3_10I1R2Mass.Encloses (∑ a, CA3_3_10I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R2P CA3_3_10I1R2Value CA3_3_10I1R2P_sound) (by decide +kernel)
def CA3_3_10I1R2MassTermLogWitness : LogWitness := ⟨-2, 39462984793329343322426019243677, 25000000000000000000000000000000⟩
def CA3_3_10I1R2MassTermLog : Ball := ⟨(-92980704726770521501237573885407 / 100000000000000000000000000000000), (31763735693 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I1R2MassTermLog_sound : CA3_3_10I1R2MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I1R2Mass_sound) (w := CA3_3_10I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_3_10I1R2MassTerm : Ball := ⟨(17916485042507767989356665939 / 48828125000000000000000000000), (25069836497 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I1R2MassTerm_sound : CA3_3_10I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I1R2Mass_sound) CA3_3_10I1R2MassTermLog_sound) (by decide +kernel)
def CA3_3_10I1R2H : Ball := ⟨(20397219205230176018175363399493 / 50000000000000000000000000000000), (12552117853 / 20000000000000000000000000000000)⟩
lemma CA3_3_10I1R2H_sound : CA3_3_10I1R2H.Encloses (homogeneousEntropy CA3_3_10I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R2Value CA3_3_10I1R2MassTerm_sound CA3_3_10I1R2Entropy_sound) (by decide +kernel)
def CA3_3_10I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA3_3_10I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA3_3_10I1R3Raw_sound (a : PairSlot) :
    (CA3_3_10I1R3Raw a).Encloses (CA3_3_10I1R3Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA3_3_10I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(205890417481175314177510224919 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1273551935099509918164620566777 / 100000000000000000000000000000000), (435989933 / 100000000000000000000000000000000)⟩ ⟨(-618558139169323674081473370489413 / 100000000000000000000000000000000), (211758237801 / 100000000000000000000000000000000)⟩ ⟨-9, 205890417481175314177510224919, 195312500000000000000000000000⟩,
   .log ⟨(4619054651167277020629531838693 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩ ⟨(14203501238427614750271209133991 / 100000000000000000000000000000000), (5868737311 / 100000000000000000000000000000000)⟩ ⟨(-307498012279163250732354083952271 / 100000000000000000000000000000000), (127054942617 / 100000000000000000000000000000000)⟩ ⟨-5, 4619054651167277020629531838693, 3125000000000000000000000000000⟩,
   .log ⟨(8871250693737520079598966291 / 2000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1201630128356614022253786080439 / 50000000000000000000000000000000), (422676101 / 50000000000000000000000000000000)⟩ ⟨(-541808667048437937517112002272391 / 100000000000000000000000000000000), (95291206911 / 50000000000000000000000000000000)⟩ ⟨-8, 8871250693737520079598966291, 7812500000000000000000000000⟩]
lemma CA3_3_10I1R3Certificates_valid :
    CA3_3_10I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA3_3_10I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R3Certificates (CA3_3_10I1R3CertificateIndex a)).input
lemma CA3_3_10I1R3P_check : ∀ a : PairSlot, contains (CA3_3_10I1R3Raw a) (CA3_3_10I1R3P a) = true := by
  decide +kernel
lemma CA3_3_10I1R3P_sound (a : PairSlot) :
    (CA3_3_10I1R3P a).Encloses (CA3_3_10I1R3Value a) :=
  contains_sound (CA3_3_10I1R3Raw_sound a) (CA3_3_10I1R3P_check a)
def CA3_3_10I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R3Certificates (CA3_3_10I1R3CertificateIndex a)).output
lemma CA3_3_10I1R3Terms_sound (a : PairSlot) :
    (CA3_3_10I1R3Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R3Certificates_valid
    (CA3_3_10I1R3CertificateIndex a) (CA3_3_10I1R3P_sound a)
def CA3_3_10I1R3Entropy : Ball := ⟨(8940156715120176356471700930823 / 25000000000000000000000000000000), (3575039723 / 25000000000000000000000000000000)⟩
lemma CA3_3_10I1R3Entropy_sound : CA3_3_10I1R3Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R3Value CA3_3_10I1R3Terms CA3_3_10I1R3Terms_sound) (by decide +kernel)
def CA3_3_10I1R3Mass : Ball := ⟨(2634253801667664169393495189081 / 25000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I1R3Mass_sound : CA3_3_10I1R3Mass.Encloses (∑ a, CA3_3_10I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R3P CA3_3_10I1R3Value CA3_3_10I1R3P_sound) (by decide +kernel)
def CA3_3_10I1R3MassTermLogWitness : LogWitness := ⟨-4, 2634253801667664169393495189081, 1562500000000000000000000000000⟩
def CA3_3_10I1R3MassTermLog : Ball := ⟨(-14064224188767788938283650303749 / 6250000000000000000000000000000), (21175823793 / 20000000000000000000000000000000)⟩
lemma CA3_3_10I1R3MassTermLog_sound : CA3_3_10I1R3MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I1R3Mass_sound) (w := CA3_3_10I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_3_10I1R3MassTerm : Ball := ⟨(23711191063531435570046086221241 / 100000000000000000000000000000000), (11156498997 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I1R3MassTerm_sound : CA3_3_10I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I1R3Mass_sound) CA3_3_10I1R3MassTermLog_sound) (by decide +kernel)
def CA3_3_10I1R3H : Ball := ⟨(12049435796949269855840717502051 / 100000000000000000000000000000000), (25456657889 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I1R3H_sound : CA3_3_10I1R3H.Encloses (homogeneousEntropy CA3_3_10I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R3Value CA3_3_10I1R3MassTerm_sound CA3_3_10I1R3Entropy_sound) (by decide +kernel)
def CA3_3_10I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA3_3_10I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA3_3_10I1R4Raw_sound (a : PairSlot) :
    (CA3_3_10I1R4Raw a).Encloses (CA3_3_10I1R4Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA3_3_10I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R4Certificates_valid :
    CA3_3_10I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R4Certificates (CA3_3_10I1R4CertificateIndex a)).input
lemma CA3_3_10I1R4P_check : ∀ a : PairSlot, contains (CA3_3_10I1R4Raw a) (CA3_3_10I1R4P a) = true := by
  decide +kernel
lemma CA3_3_10I1R4P_sound (a : PairSlot) :
    (CA3_3_10I1R4P a).Encloses (CA3_3_10I1R4Value a) :=
  contains_sound (CA3_3_10I1R4Raw_sound a) (CA3_3_10I1R4P_check a)
def CA3_3_10I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R4Certificates (CA3_3_10I1R4CertificateIndex a)).output
lemma CA3_3_10I1R4Terms_sound (a : PairSlot) :
    (CA3_3_10I1R4Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R4Certificates_valid
    (CA3_3_10I1R4CertificateIndex a) (CA3_3_10I1R4P_sound a)
def CA3_3_10I1R4Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R4Entropy_sound : CA3_3_10I1R4Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R4Value CA3_3_10I1R4Terms CA3_3_10I1R4Terms_sound) (by decide +kernel)
def CA3_3_10I1R4Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R4Mass_sound : CA3_3_10I1R4Mass.Encloses (∑ a, CA3_3_10I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R4P CA3_3_10I1R4Value CA3_3_10I1R4P_sound) (by decide +kernel)
def CA3_3_10I1R4MassTerm : Ball := .exact 0
lemma CA3_3_10I1R4MassTerm_sound : CA3_3_10I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R4Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R4Mass_sound)
def CA3_3_10I1R4H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R4H_sound : CA3_3_10I1R4H.Encloses (homogeneousEntropy CA3_3_10I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R4Value CA3_3_10I1R4MassTerm_sound CA3_3_10I1R4Entropy_sound) (by decide +kernel)
def CA3_3_10I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA3_3_10I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA3_3_10I1R5Raw_sound (a : PairSlot) :
    (CA3_3_10I1R5Raw a).Encloses (CA3_3_10I1R5Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA3_3_10I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R5Certificates_valid :
    CA3_3_10I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R5Certificates (CA3_3_10I1R5CertificateIndex a)).input
lemma CA3_3_10I1R5P_check : ∀ a : PairSlot, contains (CA3_3_10I1R5Raw a) (CA3_3_10I1R5P a) = true := by
  decide +kernel
lemma CA3_3_10I1R5P_sound (a : PairSlot) :
    (CA3_3_10I1R5P a).Encloses (CA3_3_10I1R5Value a) :=
  contains_sound (CA3_3_10I1R5Raw_sound a) (CA3_3_10I1R5P_check a)
def CA3_3_10I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R5Certificates (CA3_3_10I1R5CertificateIndex a)).output
lemma CA3_3_10I1R5Terms_sound (a : PairSlot) :
    (CA3_3_10I1R5Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R5Certificates_valid
    (CA3_3_10I1R5CertificateIndex a) (CA3_3_10I1R5P_sound a)
def CA3_3_10I1R5Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R5Entropy_sound : CA3_3_10I1R5Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R5Value CA3_3_10I1R5Terms CA3_3_10I1R5Terms_sound) (by decide +kernel)
def CA3_3_10I1R5Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R5Mass_sound : CA3_3_10I1R5Mass.Encloses (∑ a, CA3_3_10I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R5P CA3_3_10I1R5Value CA3_3_10I1R5P_sound) (by decide +kernel)
def CA3_3_10I1R5MassTerm : Ball := .exact 0
lemma CA3_3_10I1R5MassTerm_sound : CA3_3_10I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R5Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R5Mass_sound)
def CA3_3_10I1R5H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R5H_sound : CA3_3_10I1R5H.Encloses (homogeneousEntropy CA3_3_10I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R5Value CA3_3_10I1R5MassTerm_sound CA3_3_10I1R5Entropy_sound) (by decide +kernel)
def CA3_3_10I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA3_3_10I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA3_3_10I1R6Raw_sound (a : PairSlot) :
    (CA3_3_10I1R6Raw a).Encloses (CA3_3_10I1R6Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA3_3_10I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R6Certificates_valid :
    CA3_3_10I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R6Certificates (CA3_3_10I1R6CertificateIndex a)).input
lemma CA3_3_10I1R6P_check : ∀ a : PairSlot, contains (CA3_3_10I1R6Raw a) (CA3_3_10I1R6P a) = true := by
  decide +kernel
lemma CA3_3_10I1R6P_sound (a : PairSlot) :
    (CA3_3_10I1R6P a).Encloses (CA3_3_10I1R6Value a) :=
  contains_sound (CA3_3_10I1R6Raw_sound a) (CA3_3_10I1R6P_check a)
def CA3_3_10I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R6Certificates (CA3_3_10I1R6CertificateIndex a)).output
lemma CA3_3_10I1R6Terms_sound (a : PairSlot) :
    (CA3_3_10I1R6Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R6Certificates_valid
    (CA3_3_10I1R6CertificateIndex a) (CA3_3_10I1R6P_sound a)
def CA3_3_10I1R6Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R6Entropy_sound : CA3_3_10I1R6Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R6Value CA3_3_10I1R6Terms CA3_3_10I1R6Terms_sound) (by decide +kernel)
def CA3_3_10I1R6Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R6Mass_sound : CA3_3_10I1R6Mass.Encloses (∑ a, CA3_3_10I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R6P CA3_3_10I1R6Value CA3_3_10I1R6P_sound) (by decide +kernel)
def CA3_3_10I1R6MassTerm : Ball := .exact 0
lemma CA3_3_10I1R6MassTerm_sound : CA3_3_10I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R6Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R6Mass_sound)
def CA3_3_10I1R6H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R6H_sound : CA3_3_10I1R6H.Encloses (homogeneousEntropy CA3_3_10I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R6Value CA3_3_10I1R6MassTerm_sound CA3_3_10I1R6Entropy_sound) (by decide +kernel)
def CA3_3_10I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA3_3_10I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA3_3_10I1R7Raw_sound (a : PairSlot) :
    (CA3_3_10I1R7Raw a).Encloses (CA3_3_10I1R7Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA3_3_10I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R7Certificates_valid :
    CA3_3_10I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R7Certificates (CA3_3_10I1R7CertificateIndex a)).input
lemma CA3_3_10I1R7P_check : ∀ a : PairSlot, contains (CA3_3_10I1R7Raw a) (CA3_3_10I1R7P a) = true := by
  decide +kernel
lemma CA3_3_10I1R7P_sound (a : PairSlot) :
    (CA3_3_10I1R7P a).Encloses (CA3_3_10I1R7Value a) :=
  contains_sound (CA3_3_10I1R7Raw_sound a) (CA3_3_10I1R7P_check a)
def CA3_3_10I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R7Certificates (CA3_3_10I1R7CertificateIndex a)).output
lemma CA3_3_10I1R7Terms_sound (a : PairSlot) :
    (CA3_3_10I1R7Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R7Certificates_valid
    (CA3_3_10I1R7CertificateIndex a) (CA3_3_10I1R7P_sound a)
def CA3_3_10I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R7Entropy_sound : CA3_3_10I1R7Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R7Value CA3_3_10I1R7Terms CA3_3_10I1R7Terms_sound) (by decide +kernel)
def CA3_3_10I1R7Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R7Mass_sound : CA3_3_10I1R7Mass.Encloses (∑ a, CA3_3_10I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R7P CA3_3_10I1R7Value CA3_3_10I1R7P_sound) (by decide +kernel)
def CA3_3_10I1R7MassTerm : Ball := .exact 0
lemma CA3_3_10I1R7MassTerm_sound : CA3_3_10I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R7Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R7Mass_sound)
def CA3_3_10I1R7H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R7H_sound : CA3_3_10I1R7H.Encloses (homogeneousEntropy CA3_3_10I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R7Value CA3_3_10I1R7MassTerm_sound CA3_3_10I1R7Entropy_sound) (by decide +kernel)
def CA3_3_10I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA3_3_10I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA3_3_10I1R8Raw_sound (a : PairSlot) :
    (CA3_3_10I1R8Raw a).Encloses (CA3_3_10I1R8Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA3_3_10I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R8Certificates_valid :
    CA3_3_10I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R8Certificates (CA3_3_10I1R8CertificateIndex a)).input
lemma CA3_3_10I1R8P_check : ∀ a : PairSlot, contains (CA3_3_10I1R8Raw a) (CA3_3_10I1R8P a) = true := by
  decide +kernel
lemma CA3_3_10I1R8P_sound (a : PairSlot) :
    (CA3_3_10I1R8P a).Encloses (CA3_3_10I1R8Value a) :=
  contains_sound (CA3_3_10I1R8Raw_sound a) (CA3_3_10I1R8P_check a)
def CA3_3_10I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R8Certificates (CA3_3_10I1R8CertificateIndex a)).output
lemma CA3_3_10I1R8Terms_sound (a : PairSlot) :
    (CA3_3_10I1R8Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R8Certificates_valid
    (CA3_3_10I1R8CertificateIndex a) (CA3_3_10I1R8P_sound a)
def CA3_3_10I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R8Entropy_sound : CA3_3_10I1R8Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R8Value CA3_3_10I1R8Terms CA3_3_10I1R8Terms_sound) (by decide +kernel)
def CA3_3_10I1R8Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R8Mass_sound : CA3_3_10I1R8Mass.Encloses (∑ a, CA3_3_10I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R8P CA3_3_10I1R8Value CA3_3_10I1R8P_sound) (by decide +kernel)
def CA3_3_10I1R8MassTerm : Ball := .exact 0
lemma CA3_3_10I1R8MassTerm_sound : CA3_3_10I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R8Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R8Mass_sound)
def CA3_3_10I1R8H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R8H_sound : CA3_3_10I1R8H.Encloses (homogeneousEntropy CA3_3_10I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R8Value CA3_3_10I1R8MassTerm_sound CA3_3_10I1R8Entropy_sound) (by decide +kernel)
def CA3_3_10I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA3_3_10I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA3_3_10I1R9Raw_sound (a : PairSlot) :
    (CA3_3_10I1R9Raw a).Encloses (CA3_3_10I1R9Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA3_3_10I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R9Certificates_valid :
    CA3_3_10I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R9Certificates (CA3_3_10I1R9CertificateIndex a)).input
lemma CA3_3_10I1R9P_check : ∀ a : PairSlot, contains (CA3_3_10I1R9Raw a) (CA3_3_10I1R9P a) = true := by
  decide +kernel
lemma CA3_3_10I1R9P_sound (a : PairSlot) :
    (CA3_3_10I1R9P a).Encloses (CA3_3_10I1R9Value a) :=
  contains_sound (CA3_3_10I1R9Raw_sound a) (CA3_3_10I1R9P_check a)
def CA3_3_10I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R9Certificates (CA3_3_10I1R9CertificateIndex a)).output
lemma CA3_3_10I1R9Terms_sound (a : PairSlot) :
    (CA3_3_10I1R9Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R9Certificates_valid
    (CA3_3_10I1R9CertificateIndex a) (CA3_3_10I1R9P_sound a)
def CA3_3_10I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R9Entropy_sound : CA3_3_10I1R9Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R9Value CA3_3_10I1R9Terms CA3_3_10I1R9Terms_sound) (by decide +kernel)
def CA3_3_10I1R9Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R9Mass_sound : CA3_3_10I1R9Mass.Encloses (∑ a, CA3_3_10I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R9P CA3_3_10I1R9Value CA3_3_10I1R9P_sound) (by decide +kernel)
def CA3_3_10I1R9MassTerm : Ball := .exact 0
lemma CA3_3_10I1R9MassTerm_sound : CA3_3_10I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R9Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R9Mass_sound)
def CA3_3_10I1R9H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R9H_sound : CA3_3_10I1R9H.Encloses (homogeneousEntropy CA3_3_10I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R9Value CA3_3_10I1R9MassTerm_sound CA3_3_10I1R9Entropy_sound) (by decide +kernel)
def CA3_3_10I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA3_3_10I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA3_3_10I1R10Raw_sound (a : PairSlot) :
    (CA3_3_10I1R10Raw a).Encloses (CA3_3_10I1R10Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA3_3_10I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R10Certificates_valid :
    CA3_3_10I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R10Certificates (CA3_3_10I1R10CertificateIndex a)).input
lemma CA3_3_10I1R10P_check : ∀ a : PairSlot, contains (CA3_3_10I1R10Raw a) (CA3_3_10I1R10P a) = true := by
  decide +kernel
lemma CA3_3_10I1R10P_sound (a : PairSlot) :
    (CA3_3_10I1R10P a).Encloses (CA3_3_10I1R10Value a) :=
  contains_sound (CA3_3_10I1R10Raw_sound a) (CA3_3_10I1R10P_check a)
def CA3_3_10I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R10Certificates (CA3_3_10I1R10CertificateIndex a)).output
lemma CA3_3_10I1R10Terms_sound (a : PairSlot) :
    (CA3_3_10I1R10Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R10Certificates_valid
    (CA3_3_10I1R10CertificateIndex a) (CA3_3_10I1R10P_sound a)
def CA3_3_10I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R10Entropy_sound : CA3_3_10I1R10Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R10Value CA3_3_10I1R10Terms CA3_3_10I1R10Terms_sound) (by decide +kernel)
def CA3_3_10I1R10Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R10Mass_sound : CA3_3_10I1R10Mass.Encloses (∑ a, CA3_3_10I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R10P CA3_3_10I1R10Value CA3_3_10I1R10P_sound) (by decide +kernel)
def CA3_3_10I1R10MassTerm : Ball := .exact 0
lemma CA3_3_10I1R10MassTerm_sound : CA3_3_10I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R10Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R10Mass_sound)
def CA3_3_10I1R10H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R10H_sound : CA3_3_10I1R10H.Encloses (homogeneousEntropy CA3_3_10I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R10Value CA3_3_10I1R10MassTerm_sound CA3_3_10I1R10Entropy_sound) (by decide +kernel)
def CA3_3_10I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA3_3_10I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA3_3_10I1R11Raw_sound (a : PairSlot) :
    (CA3_3_10I1R11Raw a).Encloses (CA3_3_10I1R11Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA3_3_10I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R11Certificates_valid :
    CA3_3_10I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R11Certificates (CA3_3_10I1R11CertificateIndex a)).input
lemma CA3_3_10I1R11P_check : ∀ a : PairSlot, contains (CA3_3_10I1R11Raw a) (CA3_3_10I1R11P a) = true := by
  decide +kernel
lemma CA3_3_10I1R11P_sound (a : PairSlot) :
    (CA3_3_10I1R11P a).Encloses (CA3_3_10I1R11Value a) :=
  contains_sound (CA3_3_10I1R11Raw_sound a) (CA3_3_10I1R11P_check a)
def CA3_3_10I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R11Certificates (CA3_3_10I1R11CertificateIndex a)).output
lemma CA3_3_10I1R11Terms_sound (a : PairSlot) :
    (CA3_3_10I1R11Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R11Certificates_valid
    (CA3_3_10I1R11CertificateIndex a) (CA3_3_10I1R11P_sound a)
def CA3_3_10I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R11Entropy_sound : CA3_3_10I1R11Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R11Value CA3_3_10I1R11Terms CA3_3_10I1R11Terms_sound) (by decide +kernel)
def CA3_3_10I1R11Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R11Mass_sound : CA3_3_10I1R11Mass.Encloses (∑ a, CA3_3_10I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R11P CA3_3_10I1R11Value CA3_3_10I1R11P_sound) (by decide +kernel)
def CA3_3_10I1R11MassTerm : Ball := .exact 0
lemma CA3_3_10I1R11MassTerm_sound : CA3_3_10I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R11Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R11Mass_sound)
def CA3_3_10I1R11H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R11H_sound : CA3_3_10I1R11H.Encloses (homogeneousEntropy CA3_3_10I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R11Value CA3_3_10I1R11MassTerm_sound CA3_3_10I1R11Entropy_sound) (by decide +kernel)
def CA3_3_10I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA3_3_10I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA3_3_10I1R12Raw_sound (a : PairSlot) :
    (CA3_3_10I1R12Raw a).Encloses (CA3_3_10I1R12Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA3_3_10I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R12Certificates_valid :
    CA3_3_10I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R12Certificates (CA3_3_10I1R12CertificateIndex a)).input
lemma CA3_3_10I1R12P_check : ∀ a : PairSlot, contains (CA3_3_10I1R12Raw a) (CA3_3_10I1R12P a) = true := by
  decide +kernel
lemma CA3_3_10I1R12P_sound (a : PairSlot) :
    (CA3_3_10I1R12P a).Encloses (CA3_3_10I1R12Value a) :=
  contains_sound (CA3_3_10I1R12Raw_sound a) (CA3_3_10I1R12P_check a)
def CA3_3_10I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R12Certificates (CA3_3_10I1R12CertificateIndex a)).output
lemma CA3_3_10I1R12Terms_sound (a : PairSlot) :
    (CA3_3_10I1R12Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R12Certificates_valid
    (CA3_3_10I1R12CertificateIndex a) (CA3_3_10I1R12P_sound a)
def CA3_3_10I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R12Entropy_sound : CA3_3_10I1R12Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R12Value CA3_3_10I1R12Terms CA3_3_10I1R12Terms_sound) (by decide +kernel)
def CA3_3_10I1R12Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R12Mass_sound : CA3_3_10I1R12Mass.Encloses (∑ a, CA3_3_10I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R12P CA3_3_10I1R12Value CA3_3_10I1R12P_sound) (by decide +kernel)
def CA3_3_10I1R12MassTerm : Ball := .exact 0
lemma CA3_3_10I1R12MassTerm_sound : CA3_3_10I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R12Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R12Mass_sound)
def CA3_3_10I1R12H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R12H_sound : CA3_3_10I1R12H.Encloses (homogeneousEntropy CA3_3_10I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R12Value CA3_3_10I1R12MassTerm_sound CA3_3_10I1R12Entropy_sound) (by decide +kernel)
def CA3_3_10I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA3_3_10I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA3_3_10I1R13Raw_sound (a : PairSlot) :
    (CA3_3_10I1R13Raw a).Encloses (CA3_3_10I1R13Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA3_3_10I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R13Certificates_valid :
    CA3_3_10I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R13Certificates (CA3_3_10I1R13CertificateIndex a)).input
lemma CA3_3_10I1R13P_check : ∀ a : PairSlot, contains (CA3_3_10I1R13Raw a) (CA3_3_10I1R13P a) = true := by
  decide +kernel
lemma CA3_3_10I1R13P_sound (a : PairSlot) :
    (CA3_3_10I1R13P a).Encloses (CA3_3_10I1R13Value a) :=
  contains_sound (CA3_3_10I1R13Raw_sound a) (CA3_3_10I1R13P_check a)
def CA3_3_10I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R13Certificates (CA3_3_10I1R13CertificateIndex a)).output
lemma CA3_3_10I1R13Terms_sound (a : PairSlot) :
    (CA3_3_10I1R13Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R13Certificates_valid
    (CA3_3_10I1R13CertificateIndex a) (CA3_3_10I1R13P_sound a)
def CA3_3_10I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R13Entropy_sound : CA3_3_10I1R13Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R13Value CA3_3_10I1R13Terms CA3_3_10I1R13Terms_sound) (by decide +kernel)
def CA3_3_10I1R13Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R13Mass_sound : CA3_3_10I1R13Mass.Encloses (∑ a, CA3_3_10I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R13P CA3_3_10I1R13Value CA3_3_10I1R13P_sound) (by decide +kernel)
def CA3_3_10I1R13MassTerm : Ball := .exact 0
lemma CA3_3_10I1R13MassTerm_sound : CA3_3_10I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R13Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R13Mass_sound)
def CA3_3_10I1R13H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R13H_sound : CA3_3_10I1R13H.Encloses (homogeneousEntropy CA3_3_10I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R13Value CA3_3_10I1R13MassTerm_sound CA3_3_10I1R13Entropy_sound) (by decide +kernel)
def CA3_3_10I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA3_3_10I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA3_3_10I1R14Raw_sound (a : PairSlot) :
    (CA3_3_10I1R14Raw a).Encloses (CA3_3_10I1R14Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA3_3_10I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R14Certificates_valid :
    CA3_3_10I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R14Certificates (CA3_3_10I1R14CertificateIndex a)).input
lemma CA3_3_10I1R14P_check : ∀ a : PairSlot, contains (CA3_3_10I1R14Raw a) (CA3_3_10I1R14P a) = true := by
  decide +kernel
lemma CA3_3_10I1R14P_sound (a : PairSlot) :
    (CA3_3_10I1R14P a).Encloses (CA3_3_10I1R14Value a) :=
  contains_sound (CA3_3_10I1R14Raw_sound a) (CA3_3_10I1R14P_check a)
def CA3_3_10I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R14Certificates (CA3_3_10I1R14CertificateIndex a)).output
lemma CA3_3_10I1R14Terms_sound (a : PairSlot) :
    (CA3_3_10I1R14Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R14Certificates_valid
    (CA3_3_10I1R14CertificateIndex a) (CA3_3_10I1R14P_sound a)
def CA3_3_10I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R14Entropy_sound : CA3_3_10I1R14Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R14Value CA3_3_10I1R14Terms CA3_3_10I1R14Terms_sound) (by decide +kernel)
def CA3_3_10I1R14Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R14Mass_sound : CA3_3_10I1R14Mass.Encloses (∑ a, CA3_3_10I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R14P CA3_3_10I1R14Value CA3_3_10I1R14P_sound) (by decide +kernel)
def CA3_3_10I1R14MassTerm : Ball := .exact 0
lemma CA3_3_10I1R14MassTerm_sound : CA3_3_10I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R14Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R14Mass_sound)
def CA3_3_10I1R14H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R14H_sound : CA3_3_10I1R14H.Encloses (homogeneousEntropy CA3_3_10I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R14Value CA3_3_10I1R14MassTerm_sound CA3_3_10I1R14Entropy_sound) (by decide +kernel)
def CA3_3_10I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA3_3_10I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA3_3_10I1R15Raw_sound (a : PairSlot) :
    (CA3_3_10I1R15Raw a).Encloses (CA3_3_10I1R15Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA3_3_10I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R15Certificates_valid :
    CA3_3_10I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R15Certificates (CA3_3_10I1R15CertificateIndex a)).input
lemma CA3_3_10I1R15P_check : ∀ a : PairSlot, contains (CA3_3_10I1R15Raw a) (CA3_3_10I1R15P a) = true := by
  decide +kernel
lemma CA3_3_10I1R15P_sound (a : PairSlot) :
    (CA3_3_10I1R15P a).Encloses (CA3_3_10I1R15Value a) :=
  contains_sound (CA3_3_10I1R15Raw_sound a) (CA3_3_10I1R15P_check a)
def CA3_3_10I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R15Certificates (CA3_3_10I1R15CertificateIndex a)).output
lemma CA3_3_10I1R15Terms_sound (a : PairSlot) :
    (CA3_3_10I1R15Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R15Certificates_valid
    (CA3_3_10I1R15CertificateIndex a) (CA3_3_10I1R15P_sound a)
def CA3_3_10I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R15Entropy_sound : CA3_3_10I1R15Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R15Value CA3_3_10I1R15Terms CA3_3_10I1R15Terms_sound) (by decide +kernel)
def CA3_3_10I1R15Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R15Mass_sound : CA3_3_10I1R15Mass.Encloses (∑ a, CA3_3_10I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R15P CA3_3_10I1R15Value CA3_3_10I1R15P_sound) (by decide +kernel)
def CA3_3_10I1R15MassTerm : Ball := .exact 0
lemma CA3_3_10I1R15MassTerm_sound : CA3_3_10I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R15Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R15Mass_sound)
def CA3_3_10I1R15H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R15H_sound : CA3_3_10I1R15H.Encloses (homogeneousEntropy CA3_3_10I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R15Value CA3_3_10I1R15MassTerm_sound CA3_3_10I1R15Entropy_sound) (by decide +kernel)
def CA3_3_10I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA3_3_10I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA3_3_10I1R16Raw_sound (a : PairSlot) :
    (CA3_3_10I1R16Raw a).Encloses (CA3_3_10I1R16Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA3_3_10I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I1R16Certificates_valid :
    CA3_3_10I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R16Certificates (CA3_3_10I1R16CertificateIndex a)).input
lemma CA3_3_10I1R16P_check : ∀ a : PairSlot, contains (CA3_3_10I1R16Raw a) (CA3_3_10I1R16P a) = true := by
  decide +kernel
lemma CA3_3_10I1R16P_sound (a : PairSlot) :
    (CA3_3_10I1R16P a).Encloses (CA3_3_10I1R16Value a) :=
  contains_sound (CA3_3_10I1R16Raw_sound a) (CA3_3_10I1R16P_check a)
def CA3_3_10I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I1R16Certificates (CA3_3_10I1R16CertificateIndex a)).output
lemma CA3_3_10I1R16Terms_sound (a : PairSlot) :
    (CA3_3_10I1R16Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R16Certificates_valid
    (CA3_3_10I1R16CertificateIndex a) (CA3_3_10I1R16P_sound a)
def CA3_3_10I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R16Entropy_sound : CA3_3_10I1R16Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R16Value CA3_3_10I1R16Terms CA3_3_10I1R16Terms_sound) (by decide +kernel)
def CA3_3_10I1R16Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R16Mass_sound : CA3_3_10I1R16Mass.Encloses (∑ a, CA3_3_10I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R16P CA3_3_10I1R16Value CA3_3_10I1R16P_sound) (by decide +kernel)
def CA3_3_10I1R16MassTerm : Ball := .exact 0
lemma CA3_3_10I1R16MassTerm_sound : CA3_3_10I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R16Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R16Mass_sound)
def CA3_3_10I1R16H : Ball := ⟨0, 0⟩
lemma CA3_3_10I1R16H_sound : CA3_3_10I1R16H.Encloses (homogeneousEntropy CA3_3_10I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R16Value CA3_3_10I1R16MassTerm_sound CA3_3_10I1R16Entropy_sound) (by decide +kernel)
def CA3_3_10I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_3_10I1R0H
  | 1 => CA3_3_10I1R1H
  | 2 => CA3_3_10I1R2H
  | 3 => CA3_3_10I1R3H
  | 4 => CA3_3_10I1R4H
  | 5 => CA3_3_10I1R5H
  | 6 => CA3_3_10I1R6H
  | 7 => CA3_3_10I1R7H
  | 8 => CA3_3_10I1R8H
  | 9 => CA3_3_10I1R9H
  | 10 => CA3_3_10I1R10H
  | 11 => CA3_3_10I1R11H
  | 12 => CA3_3_10I1R12H
  | 13 => CA3_3_10I1R13H
  | 14 => CA3_3_10I1R14H
  | 15 => CA3_3_10I1R15H
  | 16 => CA3_3_10I1R16H
  | _ => (.exact 0)
lemma CA3_3_10I1ResidualEntropies_sound (k : Fin 17) :
    (CA3_3_10I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA3_3_10I1R0H_sound
  · exact CA3_3_10I1R1H_sound
  · exact CA3_3_10I1R2H_sound
  · exact CA3_3_10I1R3H_sound
  · exact CA3_3_10I1R4H_sound
  · exact CA3_3_10I1R5H_sound
  · exact CA3_3_10I1R6H_sound
  · exact CA3_3_10I1R7H_sound
  · exact CA3_3_10I1R8H_sound
  · exact CA3_3_10I1R9H_sound
  · exact CA3_3_10I1R10H_sound
  · exact CA3_3_10I1R11H_sound
  · exact CA3_3_10I1R12H_sound
  · exact CA3_3_10I1R13H_sound
  · exact CA3_3_10I1R14H_sound
  · exact CA3_3_10I1R15H_sound
  · exact CA3_3_10I1R16H_sound
def CA3_3_10I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
lemma CA3_3_10I1Singles_sound (u : Shape) (hu : u ∈ below (shape 3 3 10))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA3_3_10I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A3_3_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 0 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 3 2) by decide +kernel) hd |>.elim
def CA3_3_10I1Singleton : Ball := ⟨0, 0⟩
lemma CA3_3_10I1Singleton_sound : CA3_3_10I1Singleton.Encloses
    (singletonEntropy (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA3_3_10I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) CA3_3_10I1Singles_sound) (by decide +kernel)
def CA3_3_10I1Group : Ball := ⟨(80197530853385852258011187912603 / 100000000000000000000000000000000), (169026530063 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I1Group_sound : CA3_3_10I1Group.Encloses
    (groupedEntropy (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA3_3_10I1Singleton_sound
    (finSumBall_sound 17 CA3_3_10I1ResidualEntropies _ CA3_3_10I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA3_3_10I1H : Ball := ⟨(60404152430587344412248538064317 / 50000000000000000000000000000000), (95984786429 / 20000000000000000000000000000000)⟩
lemma CA3_3_10I1_sound : CA3_3_10I1H.Encloses (stageACapacity (shape 3 3 10) 1) := by
  have hb := contains_sound (Ball.add_sound CA3_3_10I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA3_3_10I1Group_sound)))
    (show contains (.add CA3_3_10I1PairH (.neg (.mul (.exact 2) CA3_3_10I1Group))) CA3_3_10I1H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg]
  exact hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
