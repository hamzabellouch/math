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
def CA1_2_13I2PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 2 13)) (shape 1 2 13) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) a
def CA1_2_13I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 2 13) A1_2_13Law 2 a
lemma CA1_2_13I2PairRaw_sound (a : PairSlot × PairSlot) :
    (CA1_2_13I2PairRaw a).Encloses (CA1_2_13I2PairValue a) := by
  exact stageAPairBall_sound (shape 1 2 13) (by decide +kernel) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (fun u _ => A1_2_13Law_sound u) 2 a
def CA1_2_13I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(442586390428493077743201299 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(23719548252484822547177113277 / 100000000000000000000000000000000), (1991581 / 25000000000000000000000000000000)⟩ ⟨(-1071860715351892212750556015805041 / 100000000000000000000000000000000), (1799945239 / 500000000000000000000000000000)⟩ ⟨-16, 442586390428493077743201299, 305175781250000000000000000⟩,
   .log ⟨(73487247372078367653150166241 / 5000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(1240488635278793899698860727877 / 20000000000000000000000000000000), (2489844827 / 100000000000000000000000000000000)⟩ ⟨(-422008130539299575952973473557267 / 100000000000000000000000000000000), (8470329497 / 5000000000000000000000000000000)⟩ ⟨-7, 73487247372078367653150166241, 39062500000000000000000000000⟩,
   .log ⟨(13559799966062424844924713757 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(407852833492994091090370054029 / 100000000000000000000000000000000), (137827177 / 100000000000000000000000000000000)⟩ ⟨(-751952157321220455269927703992753 / 100000000000000000000000000000000), (254109886039 / 100000000000000000000000000000000)⟩ ⟨-11, 13559799966062424844924713757, 12207031250000000000000000000⟩,
   .log ⟨(602160777172434722019253310913 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(4487430519244414723671769540491 / 50000000000000000000000000000000), (3570350173 / 100000000000000000000000000000000)⟩ ⟨(-186305331124190541737476037081479 / 50000000000000000000000000000000), (29646153239 / 20000000000000000000000000000000)⟩ ⟨-6, 602160777172434722019253310913, 390625000000000000000000000000⟩,
   .log ⟨(93171277412476765128264423973 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(146403261066533712208140456213 / 12500000000000000000000000000000), (86811059 / 20000000000000000000000000000000)⟩ ⟨(-25141355169944859121021011035561 / 4000000000000000000000000000000), (116467030793 / 50000000000000000000000000000000)⟩ ⟨-10, 93171277412476765128264423973, 48828125000000000000000000000⟩,
   .log ⟨(914191579685632782275074881523 / 5000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩ ⟨(3883378495598803084596402029963 / 12500000000000000000000000000000), (7743503921 / 50000000000000000000000000000000)⟩ ⟨(-169915303614334234657882374566849 / 100000000000000000000000000000000), (8470329489 / 10000000000000000000000000000000)⟩ ⟨-3, 914191579685632782275074881523, 625000000000000000000000000000⟩]
lemma CA1_2_13I2PairCertificates_valid :
    CA1_2_13I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 5, 5, 5, 1 => 1
  | 5, 5, 4, 2 => 2
  | 5, 5, 4, 3 => 3
  | 5, 5, 2, 4 => 2
  | 5, 5, 3, 4 => 3
  | 5, 5, 1, 5 => 1
  | 4, 5, 5, 2 => 4
  | 4, 5, 5, 3 => 5
  | 4, 5, 4, 4 => 6
  | 4, 5, 2, 5 => 4
  | 4, 5, 3, 5 => 5
  | 5, 4, 5, 2 => 4
  | 5, 4, 5, 3 => 5
  | 5, 4, 4, 4 => 6
  | 5, 4, 2, 5 => 4
  | 5, 4, 3, 5 => 5
  | 2, 5, 4, 5 => 4
  | 2, 5, 5, 4 => 4
  | 3, 5, 4, 5 => 5
  | 3, 5, 5, 4 => 5
  | 4, 4, 4, 5 => 6
  | 4, 4, 5, 4 => 6
  | 5, 2, 4, 5 => 4
  | 5, 2, 5, 4 => 4
  | 5, 3, 4, 5 => 5
  | 5, 3, 5, 4 => 5
  | 5, 1, 5, 5 => 1
  | 4, 2, 5, 5 => 2
  | 4, 3, 5, 5 => 3
  | 2, 4, 5, 5 => 2
  | 3, 4, 5, 5 => 3
  | 1, 5, 5, 5 => 1
  | _, _, _, _ => 0
def CA1_2_13I2PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2PairCertificates (CA1_2_13I2PairCertificateIndex a)).input
lemma CA1_2_13I2PairP_check_0_0 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((0,0),(k,l))) (CA1_2_13I2PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_0_1 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((0,1),(k,l))) (CA1_2_13I2PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_0_2 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((0,2),(k,l))) (CA1_2_13I2PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_0_3 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((0,3),(k,l))) (CA1_2_13I2PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_0_4 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((0,4),(k,l))) (CA1_2_13I2PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_0_5 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((0,5),(k,l))) (CA1_2_13I2PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_1_0 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((1,0),(k,l))) (CA1_2_13I2PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_1_1 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((1,1),(k,l))) (CA1_2_13I2PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_1_2 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((1,2),(k,l))) (CA1_2_13I2PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_1_3 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((1,3),(k,l))) (CA1_2_13I2PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_1_4 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((1,4),(k,l))) (CA1_2_13I2PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_1_5 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((1,5),(k,l))) (CA1_2_13I2PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_2_0 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((2,0),(k,l))) (CA1_2_13I2PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_2_1 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((2,1),(k,l))) (CA1_2_13I2PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_2_2 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((2,2),(k,l))) (CA1_2_13I2PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_2_3 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((2,3),(k,l))) (CA1_2_13I2PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_2_4 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((2,4),(k,l))) (CA1_2_13I2PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_2_5 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((2,5),(k,l))) (CA1_2_13I2PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_3_0 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((3,0),(k,l))) (CA1_2_13I2PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_3_1 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((3,1),(k,l))) (CA1_2_13I2PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_3_2 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((3,2),(k,l))) (CA1_2_13I2PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_3_3 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((3,3),(k,l))) (CA1_2_13I2PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_3_4 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((3,4),(k,l))) (CA1_2_13I2PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_3_5 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((3,5),(k,l))) (CA1_2_13I2PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_4_0 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((4,0),(k,l))) (CA1_2_13I2PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_4_1 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((4,1),(k,l))) (CA1_2_13I2PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_4_2 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((4,2),(k,l))) (CA1_2_13I2PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_4_3 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((4,3),(k,l))) (CA1_2_13I2PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_4_4 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((4,4),(k,l))) (CA1_2_13I2PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_4_5 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((4,5),(k,l))) (CA1_2_13I2PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_5_0 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((5,0),(k,l))) (CA1_2_13I2PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_5_1 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((5,1),(k,l))) (CA1_2_13I2PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_5_2 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((5,2),(k,l))) (CA1_2_13I2PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_5_3 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((5,3),(k,l))) (CA1_2_13I2PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_5_4 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((5,4),(k,l))) (CA1_2_13I2PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check_5_5 : ∀ k l : Fin 6, contains (CA1_2_13I2PairRaw ((5,5),(k,l))) (CA1_2_13I2PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA1_2_13I2PairP_check (a : PairSlot × PairSlot) : contains (CA1_2_13I2PairRaw a) (CA1_2_13I2PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA1_2_13I2PairP_check_0_0 k l) (CA1_2_13I2PairP_check_0_1 k l) (CA1_2_13I2PairP_check_0_2 k l) (CA1_2_13I2PairP_check_0_3 k l) (CA1_2_13I2PairP_check_0_4 k l) (CA1_2_13I2PairP_check_0_5 k l)
  · exact forall_fin6 (CA1_2_13I2PairP_check_1_0 k l) (CA1_2_13I2PairP_check_1_1 k l) (CA1_2_13I2PairP_check_1_2 k l) (CA1_2_13I2PairP_check_1_3 k l) (CA1_2_13I2PairP_check_1_4 k l) (CA1_2_13I2PairP_check_1_5 k l)
  · exact forall_fin6 (CA1_2_13I2PairP_check_2_0 k l) (CA1_2_13I2PairP_check_2_1 k l) (CA1_2_13I2PairP_check_2_2 k l) (CA1_2_13I2PairP_check_2_3 k l) (CA1_2_13I2PairP_check_2_4 k l) (CA1_2_13I2PairP_check_2_5 k l)
  · exact forall_fin6 (CA1_2_13I2PairP_check_3_0 k l) (CA1_2_13I2PairP_check_3_1 k l) (CA1_2_13I2PairP_check_3_2 k l) (CA1_2_13I2PairP_check_3_3 k l) (CA1_2_13I2PairP_check_3_4 k l) (CA1_2_13I2PairP_check_3_5 k l)
  · exact forall_fin6 (CA1_2_13I2PairP_check_4_0 k l) (CA1_2_13I2PairP_check_4_1 k l) (CA1_2_13I2PairP_check_4_2 k l) (CA1_2_13I2PairP_check_4_3 k l) (CA1_2_13I2PairP_check_4_4 k l) (CA1_2_13I2PairP_check_4_5 k l)
  · exact forall_fin6 (CA1_2_13I2PairP_check_5_0 k l) (CA1_2_13I2PairP_check_5_1 k l) (CA1_2_13I2PairP_check_5_2 k l) (CA1_2_13I2PairP_check_5_3 k l) (CA1_2_13I2PairP_check_5_4 k l) (CA1_2_13I2PairP_check_5_5 k l)
lemma CA1_2_13I2PairP_sound (a : PairSlot × PairSlot) :
    (CA1_2_13I2PairP a).Encloses (CA1_2_13I2PairValue a) :=
  contains_sound (CA1_2_13I2PairRaw_sound a) (CA1_2_13I2PairP_check a)
def CA1_2_13I2PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2PairCertificates (CA1_2_13I2PairCertificateIndex a)).output
lemma CA1_2_13I2PairTerms_sound (a : PairSlot × PairSlot) :
    (CA1_2_13I2PairTerms a).Encloses (Foundation.entropyTerm (CA1_2_13I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2PairCertificates_valid
    (CA1_2_13I2PairCertificateIndex a) (CA1_2_13I2PairP_sound a)
def CA1_2_13I2PairEntropy : Ball := ⟨(57993217776972071378920392507767 / 25000000000000000000000000000000), (13065728553 / 12500000000000000000000000000000)⟩
lemma CA1_2_13I2PairEntropy_sound : CA1_2_13I2PairEntropy.Encloses (Foundation.finiteEntropy CA1_2_13I2PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA1_2_13I2PairValue CA1_2_13I2PairTerms CA1_2_13I2PairTerms_sound) (by decide +kernel)
def CA1_2_13I2PairMass : Ball := ⟨(24999999999999999999999999999999 / 25000000000000000000000000000000), (31 / 12500000000000000000000000000000)⟩
lemma CA1_2_13I2PairMass_sound : CA1_2_13I2PairMass.Encloses (∑ a, CA1_2_13I2PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA1_2_13I2PairP CA1_2_13I2PairValue CA1_2_13I2PairP_sound) (by decide +kernel)
def CA1_2_13I2PairMassTermLogWitness : LogWitness := ⟨-1, 24999999999999999999999999999999, 12500000000000000000000000000000⟩
def CA1_2_13I2PairMassTermLog : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175823807 / 50000000000000000000000000000000)⟩
lemma CA1_2_13I2PairMassTermLog_sound : CA1_2_13I2PairMassTermLog.Encloses (Real.log ((∑ a, CA1_2_13I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_2_13I2PairMass_sound) (w := CA1_2_13I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_2_13I2PairMassTerm : Ball := ⟨(1 / 25000000000000000000000000000000), (8470329523 / 20000000000000000000000000000000)⟩
lemma CA1_2_13I2PairMassTerm_sound : CA1_2_13I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA1_2_13I2PairMass_sound) CA1_2_13I2PairMassTermLog_sound) (by decide +kernel)
def CA1_2_13I2PairH : Ball := ⟨(28996608888486035689460196253883 / 12500000000000000000000000000000), (146877476039 / 100000000000000000000000000000000)⟩
lemma CA1_2_13I2PairH_sound : CA1_2_13I2PairH.Encloses (homogeneousEntropy CA1_2_13I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2PairValue CA1_2_13I2PairMassTerm_sound CA1_2_13I2PairEntropy_sound) (by decide +kernel)

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
def CA1_2_13I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA1_2_13I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA1_2_13I2R0Raw_sound (a : PairSlot) :
    (CA1_2_13I2R0Raw a).Encloses (CA1_2_13I2R0Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA1_2_13I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R0Certificates_valid :
    CA1_2_13I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R0Certificates (CA1_2_13I2R0CertificateIndex a)).input
lemma CA1_2_13I2R0P_check : ∀ a : PairSlot, contains (CA1_2_13I2R0Raw a) (CA1_2_13I2R0P a) = true := by
  decide +kernel
lemma CA1_2_13I2R0P_sound (a : PairSlot) :
    (CA1_2_13I2R0P a).Encloses (CA1_2_13I2R0Value a) :=
  contains_sound (CA1_2_13I2R0Raw_sound a) (CA1_2_13I2R0P_check a)
def CA1_2_13I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R0Certificates (CA1_2_13I2R0CertificateIndex a)).output
lemma CA1_2_13I2R0Terms_sound (a : PairSlot) :
    (CA1_2_13I2R0Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R0Certificates_valid
    (CA1_2_13I2R0CertificateIndex a) (CA1_2_13I2R0P_sound a)
def CA1_2_13I2R0Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R0Entropy_sound : CA1_2_13I2R0Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R0Value CA1_2_13I2R0Terms CA1_2_13I2R0Terms_sound) (by decide +kernel)
def CA1_2_13I2R0Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R0Mass_sound : CA1_2_13I2R0Mass.Encloses (∑ a, CA1_2_13I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R0P CA1_2_13I2R0Value CA1_2_13I2R0P_sound) (by decide +kernel)
def CA1_2_13I2R0MassTerm : Ball := .exact 0
lemma CA1_2_13I2R0MassTerm_sound : CA1_2_13I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R0Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R0Mass_sound)
def CA1_2_13I2R0H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R0H_sound : CA1_2_13I2R0H.Encloses (homogeneousEntropy CA1_2_13I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R0Value CA1_2_13I2R0MassTerm_sound CA1_2_13I2R0Entropy_sound) (by decide +kernel)
def CA1_2_13I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA1_2_13I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA1_2_13I2R1Raw_sound (a : PairSlot) :
    (CA1_2_13I2R1Raw a).Encloses (CA1_2_13I2R1Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA1_2_13I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R1Certificates_valid :
    CA1_2_13I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R1Certificates (CA1_2_13I2R1CertificateIndex a)).input
lemma CA1_2_13I2R1P_check : ∀ a : PairSlot, contains (CA1_2_13I2R1Raw a) (CA1_2_13I2R1P a) = true := by
  decide +kernel
lemma CA1_2_13I2R1P_sound (a : PairSlot) :
    (CA1_2_13I2R1P a).Encloses (CA1_2_13I2R1Value a) :=
  contains_sound (CA1_2_13I2R1Raw_sound a) (CA1_2_13I2R1P_check a)
def CA1_2_13I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R1Certificates (CA1_2_13I2R1CertificateIndex a)).output
lemma CA1_2_13I2R1Terms_sound (a : PairSlot) :
    (CA1_2_13I2R1Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R1Certificates_valid
    (CA1_2_13I2R1CertificateIndex a) (CA1_2_13I2R1P_sound a)
def CA1_2_13I2R1Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R1Entropy_sound : CA1_2_13I2R1Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R1Value CA1_2_13I2R1Terms CA1_2_13I2R1Terms_sound) (by decide +kernel)
def CA1_2_13I2R1Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R1Mass_sound : CA1_2_13I2R1Mass.Encloses (∑ a, CA1_2_13I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R1P CA1_2_13I2R1Value CA1_2_13I2R1P_sound) (by decide +kernel)
def CA1_2_13I2R1MassTerm : Ball := .exact 0
lemma CA1_2_13I2R1MassTerm_sound : CA1_2_13I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R1Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R1Mass_sound)
def CA1_2_13I2R1H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R1H_sound : CA1_2_13I2R1H.Encloses (homogeneousEntropy CA1_2_13I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R1Value CA1_2_13I2R1MassTerm_sound CA1_2_13I2R1Entropy_sound) (by decide +kernel)
def CA1_2_13I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA1_2_13I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA1_2_13I2R2Raw_sound (a : PairSlot) :
    (CA1_2_13I2R2Raw a).Encloses (CA1_2_13I2R2Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA1_2_13I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R2Certificates_valid :
    CA1_2_13I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R2Certificates (CA1_2_13I2R2CertificateIndex a)).input
lemma CA1_2_13I2R2P_check : ∀ a : PairSlot, contains (CA1_2_13I2R2Raw a) (CA1_2_13I2R2P a) = true := by
  decide +kernel
lemma CA1_2_13I2R2P_sound (a : PairSlot) :
    (CA1_2_13I2R2P a).Encloses (CA1_2_13I2R2Value a) :=
  contains_sound (CA1_2_13I2R2Raw_sound a) (CA1_2_13I2R2P_check a)
def CA1_2_13I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R2Certificates (CA1_2_13I2R2CertificateIndex a)).output
lemma CA1_2_13I2R2Terms_sound (a : PairSlot) :
    (CA1_2_13I2R2Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R2Certificates_valid
    (CA1_2_13I2R2CertificateIndex a) (CA1_2_13I2R2P_sound a)
def CA1_2_13I2R2Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R2Entropy_sound : CA1_2_13I2R2Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R2Value CA1_2_13I2R2Terms CA1_2_13I2R2Terms_sound) (by decide +kernel)
def CA1_2_13I2R2Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R2Mass_sound : CA1_2_13I2R2Mass.Encloses (∑ a, CA1_2_13I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R2P CA1_2_13I2R2Value CA1_2_13I2R2P_sound) (by decide +kernel)
def CA1_2_13I2R2MassTerm : Ball := .exact 0
lemma CA1_2_13I2R2MassTerm_sound : CA1_2_13I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R2Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R2Mass_sound)
def CA1_2_13I2R2H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R2H_sound : CA1_2_13I2R2H.Encloses (homogeneousEntropy CA1_2_13I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R2Value CA1_2_13I2R2MassTerm_sound CA1_2_13I2R2Entropy_sound) (by decide +kernel)
def CA1_2_13I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA1_2_13I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA1_2_13I2R3Raw_sound (a : PairSlot) :
    (CA1_2_13I2R3Raw a).Encloses (CA1_2_13I2R3Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA1_2_13I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R3Certificates_valid :
    CA1_2_13I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R3Certificates (CA1_2_13I2R3CertificateIndex a)).input
lemma CA1_2_13I2R3P_check : ∀ a : PairSlot, contains (CA1_2_13I2R3Raw a) (CA1_2_13I2R3P a) = true := by
  decide +kernel
lemma CA1_2_13I2R3P_sound (a : PairSlot) :
    (CA1_2_13I2R3P a).Encloses (CA1_2_13I2R3Value a) :=
  contains_sound (CA1_2_13I2R3Raw_sound a) (CA1_2_13I2R3P_check a)
def CA1_2_13I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R3Certificates (CA1_2_13I2R3CertificateIndex a)).output
lemma CA1_2_13I2R3Terms_sound (a : PairSlot) :
    (CA1_2_13I2R3Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R3Certificates_valid
    (CA1_2_13I2R3CertificateIndex a) (CA1_2_13I2R3P_sound a)
def CA1_2_13I2R3Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R3Entropy_sound : CA1_2_13I2R3Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R3Value CA1_2_13I2R3Terms CA1_2_13I2R3Terms_sound) (by decide +kernel)
def CA1_2_13I2R3Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R3Mass_sound : CA1_2_13I2R3Mass.Encloses (∑ a, CA1_2_13I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R3P CA1_2_13I2R3Value CA1_2_13I2R3P_sound) (by decide +kernel)
def CA1_2_13I2R3MassTerm : Ball := .exact 0
lemma CA1_2_13I2R3MassTerm_sound : CA1_2_13I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R3Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R3Mass_sound)
def CA1_2_13I2R3H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R3H_sound : CA1_2_13I2R3H.Encloses (homogeneousEntropy CA1_2_13I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R3Value CA1_2_13I2R3MassTerm_sound CA1_2_13I2R3Entropy_sound) (by decide +kernel)
def CA1_2_13I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA1_2_13I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA1_2_13I2R4Raw_sound (a : PairSlot) :
    (CA1_2_13I2R4Raw a).Encloses (CA1_2_13I2R4Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA1_2_13I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R4Certificates_valid :
    CA1_2_13I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R4Certificates (CA1_2_13I2R4CertificateIndex a)).input
lemma CA1_2_13I2R4P_check : ∀ a : PairSlot, contains (CA1_2_13I2R4Raw a) (CA1_2_13I2R4P a) = true := by
  decide +kernel
lemma CA1_2_13I2R4P_sound (a : PairSlot) :
    (CA1_2_13I2R4P a).Encloses (CA1_2_13I2R4Value a) :=
  contains_sound (CA1_2_13I2R4Raw_sound a) (CA1_2_13I2R4P_check a)
def CA1_2_13I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R4Certificates (CA1_2_13I2R4CertificateIndex a)).output
lemma CA1_2_13I2R4Terms_sound (a : PairSlot) :
    (CA1_2_13I2R4Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R4Certificates_valid
    (CA1_2_13I2R4CertificateIndex a) (CA1_2_13I2R4P_sound a)
def CA1_2_13I2R4Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R4Entropy_sound : CA1_2_13I2R4Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R4Value CA1_2_13I2R4Terms CA1_2_13I2R4Terms_sound) (by decide +kernel)
def CA1_2_13I2R4Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R4Mass_sound : CA1_2_13I2R4Mass.Encloses (∑ a, CA1_2_13I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R4P CA1_2_13I2R4Value CA1_2_13I2R4P_sound) (by decide +kernel)
def CA1_2_13I2R4MassTerm : Ball := .exact 0
lemma CA1_2_13I2R4MassTerm_sound : CA1_2_13I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R4Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R4Mass_sound)
def CA1_2_13I2R4H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R4H_sound : CA1_2_13I2R4H.Encloses (homogeneousEntropy CA1_2_13I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R4Value CA1_2_13I2R4MassTerm_sound CA1_2_13I2R4Entropy_sound) (by decide +kernel)
def CA1_2_13I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA1_2_13I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA1_2_13I2R5Raw_sound (a : PairSlot) :
    (CA1_2_13I2R5Raw a).Encloses (CA1_2_13I2R5Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA1_2_13I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(442586390428493077743201299 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(23719548252484822547177113277 / 100000000000000000000000000000000), (1991581 / 25000000000000000000000000000000)⟩ ⟨(-1071860715351892212750556015805041 / 100000000000000000000000000000000), (1799945239 / 500000000000000000000000000000)⟩ ⟨-16, 442586390428493077743201299, 305175781250000000000000000⟩,
   .log ⟨(73487247372078367653150166241 / 5000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(1240488635278793899698860727877 / 20000000000000000000000000000000), (2489844827 / 100000000000000000000000000000000)⟩ ⟨(-422008130539299575952973473557267 / 100000000000000000000000000000000), (8470329497 / 5000000000000000000000000000000)⟩ ⟨-7, 73487247372078367653150166241, 39062500000000000000000000000⟩,
   .log ⟨(13559799966062424844924713757 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(407852833492994091090370054029 / 100000000000000000000000000000000), (137827177 / 100000000000000000000000000000000)⟩ ⟨(-751952157321220455269927703992753 / 100000000000000000000000000000000), (254109886039 / 100000000000000000000000000000000)⟩ ⟨-11, 13559799966062424844924713757, 12207031250000000000000000000⟩]
lemma CA1_2_13I2R5Certificates_valid :
    CA1_2_13I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA1_2_13I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R5Certificates (CA1_2_13I2R5CertificateIndex a)).input
lemma CA1_2_13I2R5P_check : ∀ a : PairSlot, contains (CA1_2_13I2R5Raw a) (CA1_2_13I2R5P a) = true := by
  decide +kernel
lemma CA1_2_13I2R5P_sound (a : PairSlot) :
    (CA1_2_13I2R5P a).Encloses (CA1_2_13I2R5Value a) :=
  contains_sound (CA1_2_13I2R5Raw_sound a) (CA1_2_13I2R5P_check a)
def CA1_2_13I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R5Certificates (CA1_2_13I2R5CertificateIndex a)).output
lemma CA1_2_13I2R5Terms_sound (a : PairSlot) :
    (CA1_2_13I2R5Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R5Certificates_valid
    (CA1_2_13I2R5CertificateIndex a) (CA1_2_13I2R5P_sound a)
def CA1_2_13I2R5Entropy : Ball := ⟨(6634015558139448412131850806691 / 50000000000000000000000000000000), (329454791 / 6250000000000000000000000000000)⟩
lemma CA1_2_13I2R5Entropy_sound : CA1_2_13I2R5Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R5Value CA1_2_13I2R5Terms CA1_2_13I2R5Terms_sound) (by decide +kernel)
def CA1_2_13I2R5Mass : Ball := ⟨(1526197079257959517831418186343 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
lemma CA1_2_13I2R5Mass_sound : CA1_2_13I2R5Mass.Encloses (∑ a, CA1_2_13I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R5P CA1_2_13I2R5Value CA1_2_13I2R5P_sound) (by decide +kernel)
def CA1_2_13I2R5MassTermLogWitness : LogWitness := ⟨-6, 1526197079257959517831418186343, 781250000000000000000000000000⟩
def CA1_2_13I2R5MassTermLog : Ball := ⟨(-43615549166142176302494797824791 / 12500000000000000000000000000000), (148230766371 / 100000000000000000000000000000000)⟩
lemma CA1_2_13I2R5MassTermLog_sound : CA1_2_13I2R5MassTermLog.Encloses (Real.log ((∑ a, CA1_2_13I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_2_13I2R5Mass_sound) (w := CA1_2_13I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_2_13I2R5MassTerm : Ball := ⟨(2130109559923139878541476166057 / 20000000000000000000000000000000), (4524587317 / 100000000000000000000000000000000)⟩
lemma CA1_2_13I2R5MassTerm_sound : CA1_2_13I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_2_13I2R5Mass_sound) CA1_2_13I2R5MassTermLog_sound) (by decide +kernel)
def CA1_2_13I2R5H : Ball := ⟨(2617483316663197431556320783097 / 100000000000000000000000000000000), (9795863973 / 100000000000000000000000000000000)⟩
lemma CA1_2_13I2R5H_sound : CA1_2_13I2R5H.Encloses (homogeneousEntropy CA1_2_13I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R5Value CA1_2_13I2R5MassTerm_sound CA1_2_13I2R5Entropy_sound) (by decide +kernel)
def CA1_2_13I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA1_2_13I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA1_2_13I2R6Raw_sound (a : PairSlot) :
    (CA1_2_13I2R6Raw a).Encloses (CA1_2_13I2R6Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA1_2_13I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(216432004712731669553203427467 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(663975410196592757437400918067 / 50000000000000000000000000000000), (114578153 / 25000000000000000000000000000000)⟩ ⟨(-76695612910609221632260488966757 / 12500000000000000000000000000000), (211758237753 / 100000000000000000000000000000000)⟩ ⟨-9, 216432004712731669553203427467, 195312500000000000000000000000⟩,
   .log ⟨(13636075369650383155990643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(53889639849187088294317631 / 25000000000000000000000000000000), (69319 / 100000000000000000000000000000000)⟩ ⟨(-1580796186243689579385450323206413 / 100000000000000000000000000000000), (12705677547 / 2500000000000000000000000000000)⟩ ⟨-23, 13636075369650383155990643, 11920928955078125000000000⟩,
   .log ⟨(5673674538352808081287275234243 / 25000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩ ⟨(33657119057436050543472652170287 / 100000000000000000000000000000000), (4805789279 / 25000000000000000000000000000000)⟩ ⟨(-148303885030420906822516939407071 / 100000000000000000000000000000000), (4235164741 / 5000000000000000000000000000000)⟩ ⟨-3, 5673674538352808081287275234243, 3125000000000000000000000000000⟩]
lemma CA1_2_13I2R6Certificates_valid :
    CA1_2_13I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA1_2_13I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R6Certificates (CA1_2_13I2R6CertificateIndex a)).input
lemma CA1_2_13I2R6P_check : ∀ a : PairSlot, contains (CA1_2_13I2R6Raw a) (CA1_2_13I2R6P a) = true := by
  decide +kernel
lemma CA1_2_13I2R6P_sound (a : PairSlot) :
    (CA1_2_13I2R6P a).Encloses (CA1_2_13I2R6Value a) :=
  contains_sound (CA1_2_13I2R6Raw_sound a) (CA1_2_13I2R6P_check a)
def CA1_2_13I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R6Certificates (CA1_2_13I2R6CertificateIndex a)).output
lemma CA1_2_13I2R6Terms_sound (a : PairSlot) :
    (CA1_2_13I2R6Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R6Certificates_valid
    (CA1_2_13I2R6CertificateIndex a) (CA1_2_13I2R6P_sound a)
def CA1_2_13I2R6Entropy : Ball := ⟨(36313451815341215069928610383603 / 100000000000000000000000000000000), (10069960489 / 50000000000000000000000000000000)⟩
lemma CA1_2_13I2R6Entropy_sound : CA1_2_13I2R6Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R6Value CA1_2_13I2R6Terms CA1_2_13I2R6Terms_sound) (by decide +kernel)
def CA1_2_13I2R6Mass : Ball := ⟨(2890948679373429370627727471649 / 12500000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
lemma CA1_2_13I2R6Mass_sound : CA1_2_13I2R6Mass.Encloses (∑ a, CA1_2_13I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R6P CA1_2_13I2R6Value CA1_2_13I2R6P_sound) (by decide +kernel)
def CA1_2_13I2R6MassTermLogWitness : LogWitness := ⟨-3, 2890948679373429370627727471649, 1562500000000000000000000000000⟩
def CA1_2_13I2R6MassTermLog : Ball := ⟨(-146414393329137410419958436008693 / 100000000000000000000000000000000), (21175823711 / 25000000000000000000000000000000)⟩
lemma CA1_2_13I2R6MassTermLog_sound : CA1_2_13I2R6MassTermLog.Encloses (Real.log ((∑ a, CA1_2_13I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_2_13I2R6Mass_sound) (w := CA1_2_13I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_2_13I2R6MassTerm : Ball := ⟨(6772423952578106297836799977093 / 20000000000000000000000000000000), (4897457577 / 25000000000000000000000000000000)⟩
lemma CA1_2_13I2R6MassTerm_sound : CA1_2_13I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_2_13I2R6Mass_sound) CA1_2_13I2R6MassTermLog_sound) (by decide +kernel)
def CA1_2_13I2R6H : Ball := ⟨(1225666026225341790372305249069 / 50000000000000000000000000000000), (19864875643 / 50000000000000000000000000000000)⟩
lemma CA1_2_13I2R6H_sound : CA1_2_13I2R6H.Encloses (homogeneousEntropy CA1_2_13I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R6Value CA1_2_13I2R6MassTerm_sound CA1_2_13I2R6Entropy_sound) (by decide +kernel)
def CA1_2_13I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA1_2_13I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA1_2_13I2R7Raw_sound (a : PairSlot) :
    (CA1_2_13I2R7Raw a).Encloses (CA1_2_13I2R7Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA1_2_13I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R7Certificates_valid :
    CA1_2_13I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R7Certificates (CA1_2_13I2R7CertificateIndex a)).input
lemma CA1_2_13I2R7P_check : ∀ a : PairSlot, contains (CA1_2_13I2R7Raw a) (CA1_2_13I2R7P a) = true := by
  decide +kernel
lemma CA1_2_13I2R7P_sound (a : PairSlot) :
    (CA1_2_13I2R7P a).Encloses (CA1_2_13I2R7Value a) :=
  contains_sound (CA1_2_13I2R7Raw_sound a) (CA1_2_13I2R7P_check a)
def CA1_2_13I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R7Certificates (CA1_2_13I2R7CertificateIndex a)).output
lemma CA1_2_13I2R7Terms_sound (a : PairSlot) :
    (CA1_2_13I2R7Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R7Certificates_valid
    (CA1_2_13I2R7CertificateIndex a) (CA1_2_13I2R7P_sound a)
def CA1_2_13I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R7Entropy_sound : CA1_2_13I2R7Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R7Value CA1_2_13I2R7Terms CA1_2_13I2R7Terms_sound) (by decide +kernel)
def CA1_2_13I2R7Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R7Mass_sound : CA1_2_13I2R7Mass.Encloses (∑ a, CA1_2_13I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R7P CA1_2_13I2R7Value CA1_2_13I2R7P_sound) (by decide +kernel)
def CA1_2_13I2R7MassTerm : Ball := .exact 0
lemma CA1_2_13I2R7MassTerm_sound : CA1_2_13I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R7Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R7Mass_sound)
def CA1_2_13I2R7H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R7H_sound : CA1_2_13I2R7H.Encloses (homogeneousEntropy CA1_2_13I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R7Value CA1_2_13I2R7MassTerm_sound CA1_2_13I2R7Entropy_sound) (by decide +kernel)
def CA1_2_13I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA1_2_13I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA1_2_13I2R8Raw_sound (a : PairSlot) :
    (CA1_2_13I2R8Raw a).Encloses (CA1_2_13I2R8Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA1_2_13I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R8Certificates_valid :
    CA1_2_13I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R8Certificates (CA1_2_13I2R8CertificateIndex a)).input
lemma CA1_2_13I2R8P_check : ∀ a : PairSlot, contains (CA1_2_13I2R8Raw a) (CA1_2_13I2R8P a) = true := by
  decide +kernel
lemma CA1_2_13I2R8P_sound (a : PairSlot) :
    (CA1_2_13I2R8P a).Encloses (CA1_2_13I2R8Value a) :=
  contains_sound (CA1_2_13I2R8Raw_sound a) (CA1_2_13I2R8P_check a)
def CA1_2_13I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R8Certificates (CA1_2_13I2R8CertificateIndex a)).output
lemma CA1_2_13I2R8Terms_sound (a : PairSlot) :
    (CA1_2_13I2R8Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R8Certificates_valid
    (CA1_2_13I2R8CertificateIndex a) (CA1_2_13I2R8P_sound a)
def CA1_2_13I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R8Entropy_sound : CA1_2_13I2R8Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R8Value CA1_2_13I2R8Terms CA1_2_13I2R8Terms_sound) (by decide +kernel)
def CA1_2_13I2R8Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R8Mass_sound : CA1_2_13I2R8Mass.Encloses (∑ a, CA1_2_13I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R8P CA1_2_13I2R8Value CA1_2_13I2R8P_sound) (by decide +kernel)
def CA1_2_13I2R8MassTerm : Ball := .exact 0
lemma CA1_2_13I2R8MassTerm_sound : CA1_2_13I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R8Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R8Mass_sound)
def CA1_2_13I2R8H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R8H_sound : CA1_2_13I2R8H.Encloses (homogeneousEntropy CA1_2_13I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R8Value CA1_2_13I2R8MassTerm_sound CA1_2_13I2R8Entropy_sound) (by decide +kernel)
def CA1_2_13I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA1_2_13I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA1_2_13I2R9Raw_sound (a : PairSlot) :
    (CA1_2_13I2R9Raw a).Encloses (CA1_2_13I2R9Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA1_2_13I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R9Certificates_valid :
    CA1_2_13I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R9Certificates (CA1_2_13I2R9CertificateIndex a)).input
lemma CA1_2_13I2R9P_check : ∀ a : PairSlot, contains (CA1_2_13I2R9Raw a) (CA1_2_13I2R9P a) = true := by
  decide +kernel
lemma CA1_2_13I2R9P_sound (a : PairSlot) :
    (CA1_2_13I2R9P a).Encloses (CA1_2_13I2R9Value a) :=
  contains_sound (CA1_2_13I2R9Raw_sound a) (CA1_2_13I2R9P_check a)
def CA1_2_13I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R9Certificates (CA1_2_13I2R9CertificateIndex a)).output
lemma CA1_2_13I2R9Terms_sound (a : PairSlot) :
    (CA1_2_13I2R9Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R9Certificates_valid
    (CA1_2_13I2R9CertificateIndex a) (CA1_2_13I2R9P_sound a)
def CA1_2_13I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R9Entropy_sound : CA1_2_13I2R9Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R9Value CA1_2_13I2R9Terms CA1_2_13I2R9Terms_sound) (by decide +kernel)
def CA1_2_13I2R9Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R9Mass_sound : CA1_2_13I2R9Mass.Encloses (∑ a, CA1_2_13I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R9P CA1_2_13I2R9Value CA1_2_13I2R9P_sound) (by decide +kernel)
def CA1_2_13I2R9MassTerm : Ball := .exact 0
lemma CA1_2_13I2R9MassTerm_sound : CA1_2_13I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R9Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R9Mass_sound)
def CA1_2_13I2R9H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R9H_sound : CA1_2_13I2R9H.Encloses (homogeneousEntropy CA1_2_13I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R9Value CA1_2_13I2R9MassTerm_sound CA1_2_13I2R9Entropy_sound) (by decide +kernel)
def CA1_2_13I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA1_2_13I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA1_2_13I2R10Raw_sound (a : PairSlot) :
    (CA1_2_13I2R10Raw a).Encloses (CA1_2_13I2R10Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA1_2_13I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R10Certificates_valid :
    CA1_2_13I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R10Certificates (CA1_2_13I2R10CertificateIndex a)).input
lemma CA1_2_13I2R10P_check : ∀ a : PairSlot, contains (CA1_2_13I2R10Raw a) (CA1_2_13I2R10P a) = true := by
  decide +kernel
lemma CA1_2_13I2R10P_sound (a : PairSlot) :
    (CA1_2_13I2R10P a).Encloses (CA1_2_13I2R10Value a) :=
  contains_sound (CA1_2_13I2R10Raw_sound a) (CA1_2_13I2R10P_check a)
def CA1_2_13I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R10Certificates (CA1_2_13I2R10CertificateIndex a)).output
lemma CA1_2_13I2R10Terms_sound (a : PairSlot) :
    (CA1_2_13I2R10Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R10Certificates_valid
    (CA1_2_13I2R10CertificateIndex a) (CA1_2_13I2R10P_sound a)
def CA1_2_13I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R10Entropy_sound : CA1_2_13I2R10Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R10Value CA1_2_13I2R10Terms CA1_2_13I2R10Terms_sound) (by decide +kernel)
def CA1_2_13I2R10Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R10Mass_sound : CA1_2_13I2R10Mass.Encloses (∑ a, CA1_2_13I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R10P CA1_2_13I2R10Value CA1_2_13I2R10P_sound) (by decide +kernel)
def CA1_2_13I2R10MassTerm : Ball := .exact 0
lemma CA1_2_13I2R10MassTerm_sound : CA1_2_13I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R10Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R10Mass_sound)
def CA1_2_13I2R10H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R10H_sound : CA1_2_13I2R10H.Encloses (homogeneousEntropy CA1_2_13I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R10Value CA1_2_13I2R10MassTerm_sound CA1_2_13I2R10Entropy_sound) (by decide +kernel)
def CA1_2_13I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA1_2_13I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA1_2_13I2R11Raw_sound (a : PairSlot) :
    (CA1_2_13I2R11Raw a).Encloses (CA1_2_13I2R11Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA1_2_13I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R11Certificates_valid :
    CA1_2_13I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R11Certificates (CA1_2_13I2R11CertificateIndex a)).input
lemma CA1_2_13I2R11P_check : ∀ a : PairSlot, contains (CA1_2_13I2R11Raw a) (CA1_2_13I2R11P a) = true := by
  decide +kernel
lemma CA1_2_13I2R11P_sound (a : PairSlot) :
    (CA1_2_13I2R11P a).Encloses (CA1_2_13I2R11Value a) :=
  contains_sound (CA1_2_13I2R11Raw_sound a) (CA1_2_13I2R11P_check a)
def CA1_2_13I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R11Certificates (CA1_2_13I2R11CertificateIndex a)).output
lemma CA1_2_13I2R11Terms_sound (a : PairSlot) :
    (CA1_2_13I2R11Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R11Certificates_valid
    (CA1_2_13I2R11CertificateIndex a) (CA1_2_13I2R11P_sound a)
def CA1_2_13I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R11Entropy_sound : CA1_2_13I2R11Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R11Value CA1_2_13I2R11Terms CA1_2_13I2R11Terms_sound) (by decide +kernel)
def CA1_2_13I2R11Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R11Mass_sound : CA1_2_13I2R11Mass.Encloses (∑ a, CA1_2_13I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R11P CA1_2_13I2R11Value CA1_2_13I2R11P_sound) (by decide +kernel)
def CA1_2_13I2R11MassTerm : Ball := .exact 0
lemma CA1_2_13I2R11MassTerm_sound : CA1_2_13I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R11Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R11Mass_sound)
def CA1_2_13I2R11H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R11H_sound : CA1_2_13I2R11H.Encloses (homogeneousEntropy CA1_2_13I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R11Value CA1_2_13I2R11MassTerm_sound CA1_2_13I2R11Entropy_sound) (by decide +kernel)
def CA1_2_13I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA1_2_13I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA1_2_13I2R12Raw_sound (a : PairSlot) :
    (CA1_2_13I2R12Raw a).Encloses (CA1_2_13I2R12Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA1_2_13I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R12Certificates_valid :
    CA1_2_13I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R12Certificates (CA1_2_13I2R12CertificateIndex a)).input
lemma CA1_2_13I2R12P_check : ∀ a : PairSlot, contains (CA1_2_13I2R12Raw a) (CA1_2_13I2R12P a) = true := by
  decide +kernel
lemma CA1_2_13I2R12P_sound (a : PairSlot) :
    (CA1_2_13I2R12P a).Encloses (CA1_2_13I2R12Value a) :=
  contains_sound (CA1_2_13I2R12Raw_sound a) (CA1_2_13I2R12P_check a)
def CA1_2_13I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R12Certificates (CA1_2_13I2R12CertificateIndex a)).output
lemma CA1_2_13I2R12Terms_sound (a : PairSlot) :
    (CA1_2_13I2R12Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R12Certificates_valid
    (CA1_2_13I2R12CertificateIndex a) (CA1_2_13I2R12P_sound a)
def CA1_2_13I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R12Entropy_sound : CA1_2_13I2R12Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R12Value CA1_2_13I2R12Terms CA1_2_13I2R12Terms_sound) (by decide +kernel)
def CA1_2_13I2R12Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R12Mass_sound : CA1_2_13I2R12Mass.Encloses (∑ a, CA1_2_13I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R12P CA1_2_13I2R12Value CA1_2_13I2R12P_sound) (by decide +kernel)
def CA1_2_13I2R12MassTerm : Ball := .exact 0
lemma CA1_2_13I2R12MassTerm_sound : CA1_2_13I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R12Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R12Mass_sound)
def CA1_2_13I2R12H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R12H_sound : CA1_2_13I2R12H.Encloses (homogeneousEntropy CA1_2_13I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R12Value CA1_2_13I2R12MassTerm_sound CA1_2_13I2R12Entropy_sound) (by decide +kernel)
def CA1_2_13I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA1_2_13I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA1_2_13I2R13Raw_sound (a : PairSlot) :
    (CA1_2_13I2R13Raw a).Encloses (CA1_2_13I2R13Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA1_2_13I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R13Certificates_valid :
    CA1_2_13I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R13Certificates (CA1_2_13I2R13CertificateIndex a)).input
lemma CA1_2_13I2R13P_check : ∀ a : PairSlot, contains (CA1_2_13I2R13Raw a) (CA1_2_13I2R13P a) = true := by
  decide +kernel
lemma CA1_2_13I2R13P_sound (a : PairSlot) :
    (CA1_2_13I2R13P a).Encloses (CA1_2_13I2R13Value a) :=
  contains_sound (CA1_2_13I2R13Raw_sound a) (CA1_2_13I2R13P_check a)
def CA1_2_13I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R13Certificates (CA1_2_13I2R13CertificateIndex a)).output
lemma CA1_2_13I2R13Terms_sound (a : PairSlot) :
    (CA1_2_13I2R13Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R13Certificates_valid
    (CA1_2_13I2R13CertificateIndex a) (CA1_2_13I2R13P_sound a)
def CA1_2_13I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R13Entropy_sound : CA1_2_13I2R13Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R13Value CA1_2_13I2R13Terms CA1_2_13I2R13Terms_sound) (by decide +kernel)
def CA1_2_13I2R13Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R13Mass_sound : CA1_2_13I2R13Mass.Encloses (∑ a, CA1_2_13I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R13P CA1_2_13I2R13Value CA1_2_13I2R13P_sound) (by decide +kernel)
def CA1_2_13I2R13MassTerm : Ball := .exact 0
lemma CA1_2_13I2R13MassTerm_sound : CA1_2_13I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R13Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R13Mass_sound)
def CA1_2_13I2R13H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R13H_sound : CA1_2_13I2R13H.Encloses (homogeneousEntropy CA1_2_13I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R13Value CA1_2_13I2R13MassTerm_sound CA1_2_13I2R13Entropy_sound) (by decide +kernel)
def CA1_2_13I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA1_2_13I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA1_2_13I2R14Raw_sound (a : PairSlot) :
    (CA1_2_13I2R14Raw a).Encloses (CA1_2_13I2R14Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA1_2_13I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R14Certificates_valid :
    CA1_2_13I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R14Certificates (CA1_2_13I2R14CertificateIndex a)).input
lemma CA1_2_13I2R14P_check : ∀ a : PairSlot, contains (CA1_2_13I2R14Raw a) (CA1_2_13I2R14P a) = true := by
  decide +kernel
lemma CA1_2_13I2R14P_sound (a : PairSlot) :
    (CA1_2_13I2R14P a).Encloses (CA1_2_13I2R14Value a) :=
  contains_sound (CA1_2_13I2R14Raw_sound a) (CA1_2_13I2R14P_check a)
def CA1_2_13I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R14Certificates (CA1_2_13I2R14CertificateIndex a)).output
lemma CA1_2_13I2R14Terms_sound (a : PairSlot) :
    (CA1_2_13I2R14Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R14Certificates_valid
    (CA1_2_13I2R14CertificateIndex a) (CA1_2_13I2R14P_sound a)
def CA1_2_13I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R14Entropy_sound : CA1_2_13I2R14Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R14Value CA1_2_13I2R14Terms CA1_2_13I2R14Terms_sound) (by decide +kernel)
def CA1_2_13I2R14Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R14Mass_sound : CA1_2_13I2R14Mass.Encloses (∑ a, CA1_2_13I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R14P CA1_2_13I2R14Value CA1_2_13I2R14P_sound) (by decide +kernel)
def CA1_2_13I2R14MassTerm : Ball := .exact 0
lemma CA1_2_13I2R14MassTerm_sound : CA1_2_13I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R14Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R14Mass_sound)
def CA1_2_13I2R14H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R14H_sound : CA1_2_13I2R14H.Encloses (homogeneousEntropy CA1_2_13I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R14Value CA1_2_13I2R14MassTerm_sound CA1_2_13I2R14Entropy_sound) (by decide +kernel)
def CA1_2_13I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA1_2_13I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA1_2_13I2R15Raw_sound (a : PairSlot) :
    (CA1_2_13I2R15Raw a).Encloses (CA1_2_13I2R15Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA1_2_13I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R15Certificates_valid :
    CA1_2_13I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R15Certificates (CA1_2_13I2R15CertificateIndex a)).input
lemma CA1_2_13I2R15P_check : ∀ a : PairSlot, contains (CA1_2_13I2R15Raw a) (CA1_2_13I2R15P a) = true := by
  decide +kernel
lemma CA1_2_13I2R15P_sound (a : PairSlot) :
    (CA1_2_13I2R15P a).Encloses (CA1_2_13I2R15Value a) :=
  contains_sound (CA1_2_13I2R15Raw_sound a) (CA1_2_13I2R15P_check a)
def CA1_2_13I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R15Certificates (CA1_2_13I2R15CertificateIndex a)).output
lemma CA1_2_13I2R15Terms_sound (a : PairSlot) :
    (CA1_2_13I2R15Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R15Certificates_valid
    (CA1_2_13I2R15CertificateIndex a) (CA1_2_13I2R15P_sound a)
def CA1_2_13I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R15Entropy_sound : CA1_2_13I2R15Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R15Value CA1_2_13I2R15Terms CA1_2_13I2R15Terms_sound) (by decide +kernel)
def CA1_2_13I2R15Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R15Mass_sound : CA1_2_13I2R15Mass.Encloses (∑ a, CA1_2_13I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R15P CA1_2_13I2R15Value CA1_2_13I2R15P_sound) (by decide +kernel)
def CA1_2_13I2R15MassTerm : Ball := .exact 0
lemma CA1_2_13I2R15MassTerm_sound : CA1_2_13I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R15Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R15Mass_sound)
def CA1_2_13I2R15H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R15H_sound : CA1_2_13I2R15H.Encloses (homogeneousEntropy CA1_2_13I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R15Value CA1_2_13I2R15MassTerm_sound CA1_2_13I2R15Entropy_sound) (by decide +kernel)
def CA1_2_13I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA1_2_13I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA1_2_13I2R16Raw_sound (a : PairSlot) :
    (CA1_2_13I2R16Raw a).Encloses (CA1_2_13I2R16Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA1_2_13I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_2_13I2R16Certificates_valid :
    CA1_2_13I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R16Certificates (CA1_2_13I2R16CertificateIndex a)).input
lemma CA1_2_13I2R16P_check : ∀ a : PairSlot, contains (CA1_2_13I2R16Raw a) (CA1_2_13I2R16P a) = true := by
  decide +kernel
lemma CA1_2_13I2R16P_sound (a : PairSlot) :
    (CA1_2_13I2R16P a).Encloses (CA1_2_13I2R16Value a) :=
  contains_sound (CA1_2_13I2R16Raw_sound a) (CA1_2_13I2R16P_check a)
def CA1_2_13I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R16Certificates (CA1_2_13I2R16CertificateIndex a)).output
lemma CA1_2_13I2R16Terms_sound (a : PairSlot) :
    (CA1_2_13I2R16Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R16Certificates_valid
    (CA1_2_13I2R16CertificateIndex a) (CA1_2_13I2R16P_sound a)
def CA1_2_13I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R16Entropy_sound : CA1_2_13I2R16Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R16Value CA1_2_13I2R16Terms CA1_2_13I2R16Terms_sound) (by decide +kernel)
def CA1_2_13I2R16Mass : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R16Mass_sound : CA1_2_13I2R16Mass.Encloses (∑ a, CA1_2_13I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R16P CA1_2_13I2R16Value CA1_2_13I2R16P_sound) (by decide +kernel)
def CA1_2_13I2R16MassTerm : Ball := .exact 0
lemma CA1_2_13I2R16MassTerm_sound : CA1_2_13I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R16Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R16Mass_sound)
def CA1_2_13I2R16H : Ball := ⟨0, 0⟩
lemma CA1_2_13I2R16H_sound : CA1_2_13I2R16H.Encloses (homogeneousEntropy CA1_2_13I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R16Value CA1_2_13I2R16MassTerm_sound CA1_2_13I2R16Entropy_sound) (by decide +kernel)
def CA1_2_13I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_2_13I2R0H
  | 1 => CA1_2_13I2R1H
  | 2 => CA1_2_13I2R2H
  | 3 => CA1_2_13I2R3H
  | 4 => CA1_2_13I2R4H
  | 5 => CA1_2_13I2R5H
  | 6 => CA1_2_13I2R6H
  | 7 => CA1_2_13I2R7H
  | 8 => CA1_2_13I2R8H
  | 9 => CA1_2_13I2R9H
  | 10 => CA1_2_13I2R10H
  | 11 => CA1_2_13I2R11H
  | 12 => CA1_2_13I2R12H
  | 13 => CA1_2_13I2R13H
  | 14 => CA1_2_13I2R14H
  | 15 => CA1_2_13I2R15H
  | 16 => CA1_2_13I2R16H
  | _ => (.exact 0)
lemma CA1_2_13I2ResidualEntropies_sound (k : Fin 17) :
    (CA1_2_13I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_2_13I2R0H_sound
  · exact CA1_2_13I2R1H_sound
  · exact CA1_2_13I2R2H_sound
  · exact CA1_2_13I2R3H_sound
  · exact CA1_2_13I2R4H_sound
  · exact CA1_2_13I2R5H_sound
  · exact CA1_2_13I2R6H_sound
  · exact CA1_2_13I2R7H_sound
  · exact CA1_2_13I2R8H_sound
  · exact CA1_2_13I2R9H_sound
  · exact CA1_2_13I2R10H_sound
  · exact CA1_2_13I2R11H_sound
  · exact CA1_2_13I2R12H_sound
  · exact CA1_2_13I2R13H_sound
  · exact CA1_2_13I2R14H_sound
  · exact CA1_2_13I2R15H_sound
  · exact CA1_2_13I2R16H_sound
def CA1_2_13I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 1, 0, 7 => Z1_0_7H2H
  | _, _, _ => (.exact 0)
lemma CA1_2_13I2Singles_sound (u : Shape) (hu : u ∈ below (shape 1 2 13))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA1_2_13I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A1_2_13_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
def CA1_2_13I2Singleton : Ball := ⟨(58270157785646687706346512918121 / 100000000000000000000000000000000), (44745661021 / 100000000000000000000000000000000)⟩
lemma CA1_2_13I2Singleton_sound : CA1_2_13I2Singleton.Encloses
    (singletonEntropy (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA1_2_13I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) CA1_2_13I2Singles_sound) (by decide +kernel)
def CA1_2_13I2Group : Ball := ⟨(15834743288690142179661861049839 / 25000000000000000000000000000000), (2356781907 / 2500000000000000000000000000000)⟩
lemma CA1_2_13I2Group_sound : CA1_2_13I2Group.Encloses
    (groupedEntropy (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_2_13I2Singleton_sound
    (finSumBall_sound 17 CA1_2_13I2ResidualEntropies _ CA1_2_13I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA1_2_13I2H : Ball := ⟨(3290466399948973377449583801011 / 3125000000000000000000000000000), (335420028599 / 100000000000000000000000000000000)⟩
lemma CA1_2_13I2_sound : CA1_2_13I2H.Encloses (stageACapacity (shape 1 2 13) 2) := by
  have hb := contains_sound (Ball.add_sound CA1_2_13I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_2_13I2Group_sound)))
    (show contains (.add CA1_2_13I2PairH (.neg (.mul (.exact 2) CA1_2_13I2Group))) CA1_2_13I2H = true by decide +kernel)
  unfold CA1_2_13I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
