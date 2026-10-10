import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal4_2_2

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 4 2 2)) (shape 4 2 2) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) a
def CB4_2_2I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) a
lemma CB4_2_2I2PairRaw_sound (a : PairSlot) :
    (CB4_2_2I2PairRaw a).Encloses (CB4_2_2I2PairValue a) := by
  exact pairLawBall_sound_on (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) (fun u _ a => B4_2_2Little_sound (complement (shape 4 2 2) u) ((stageBPriority (shape 4 2 2)) 2) a) a
def CB4_2_2I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(264017467412789009261745911423 / 100000000000000000000000000000000), (90638611 / 100000000000000000000000000000000)⟩ ⟨(-801868459204174003272721095524521 / 100000000000000000000000000000000), (68821427729 / 25000000000000000000000000000000)⟩ ⟨-12, 32925283989199048774667657891, 24414062500000000000000000000⟩,
   .log ⟨(3924290670247618121826431431639 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩ ⟨(19973363265378585772023469851697 / 100000000000000000000000000000000), (8310008839 / 100000000000000000000000000000000)⟩ ⟨(-254483739148179485664331227253563 / 100000000000000000000000000000000), (26469779699 / 25000000000000000000000000000000)⟩ ⟨-4, 3924290670247618121826431431639, 3125000000000000000000000000000⟩,
   .log ⟨(77179955630623675545342364672979 / 100000000000000000000000000000000), (147 / 100000000000000000000000000000000)⟩ ⟨(19991955146403358793157370481653 / 100000000000000000000000000000000), (32686982831 / 100000000000000000000000000000000)⟩ ⟨(-5180608095211419303120443613199 / 20000000000000000000000000000000), (10587911889 / 25000000000000000000000000000000)⟩ ⟨-1, 77179955630623675545342364672979, 50000000000000000000000000000000⟩,
   .log ⟨(3365567162619738339457547396989 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(11414569039020176213057669577501 / 100000000000000000000000000000000), (4276119459 / 100000000000000000000000000000000)⟩ ⟨(-339157368951007371594172603698707 / 100000000000000000000000000000000), (15881867803 / 12500000000000000000000000000000)⟩ ⟨-5, 3365567162619738339457547396989, 3125000000000000000000000000000⟩,
   .log ⟨(20368549697998574430467468169 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(233274673747783325687614767143 / 12500000000000000000000000000000), (345056661 / 50000000000000000000000000000000)⟩ ⟨(-572634471296464055917993227639807 / 100000000000000000000000000000000), (52939559361 / 25000000000000000000000000000000)⟩ ⟨-9, 20368549697998574430467468169, 12207031250000000000000000000⟩]
lemma CB4_2_2I2PairCertificates_valid :
    CB4_2_2I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2PairCertificateIndex (a : PairSlot) : ℕ :=
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
def CB4_2_2I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2PairCertificates (CB4_2_2I2PairCertificateIndex a)).input
lemma CB4_2_2I2PairP_check : ∀ a : PairSlot, contains (CB4_2_2I2PairRaw a) (CB4_2_2I2PairP a) = true := by
  decide +kernel
lemma CB4_2_2I2PairP_sound (a : PairSlot) :
    (CB4_2_2I2PairP a).Encloses (CB4_2_2I2PairValue a) :=
  contains_sound (CB4_2_2I2PairRaw_sound a) (CB4_2_2I2PairP_check a)
def CB4_2_2I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2PairCertificates (CB4_2_2I2PairCertificateIndex a)).output
lemma CB4_2_2I2PairTerms_sound (a : PairSlot) :
    (CB4_2_2I2PairTerms a).Encloses (Foundation.entropyTerm (CB4_2_2I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2PairCertificates_valid
    (CB4_2_2I2PairCertificateIndex a) (CB4_2_2I2PairP_sound a)
def CB4_2_2I2PairEntropy : Ball := ⟨(85162052080008727387344059300039 / 100000000000000000000000000000000), (58730629971 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2PairEntropy_sound : CB4_2_2I2PairEntropy.Encloses (Foundation.finiteEntropy CB4_2_2I2PairValue) := by
  exact contains_sound (entropyPair_enclosed CB4_2_2I2PairValue CB4_2_2I2PairTerms CB4_2_2I2PairTerms_sound) (by decide +kernel)
def CB4_2_2I2PairMass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (233 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2PairMass_sound : CB4_2_2I2PairMass.Encloses (∑ a, CB4_2_2I2PairValue a) := by
  exact contains_sound (pairSumBall_sound CB4_2_2I2PairP CB4_2_2I2PairValue CB4_2_2I2PairP_sound) (by decide +kernel)
def CB4_2_2I2PairMassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def CB4_2_2I2PairMassTermLog : Ball := ⟨0, (42351647599 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2PairMassTermLog_sound : CB4_2_2I2PairMassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_2_2I2PairMass_sound) (w := CB4_2_2I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB4_2_2I2PairMassTerm : Ball := ⟨0, (105879119 / 250000000000000000000000000000)⟩
lemma CB4_2_2I2PairMassTerm_sound : CB4_2_2I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2PairMass_sound) CB4_2_2I2PairMassTermLog_sound) (by decide +kernel)
def CB4_2_2I2PairH : Ball := ⟨(85162052080008727387344059300039 / 100000000000000000000000000000000), (101082277571 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2PairH_sound : CB4_2_2I2PairH.Encloses (homogeneousEntropy CB4_2_2I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2PairValue CB4_2_2I2PairMassTerm_sound CB4_2_2I2PairEntropy_sound) (by decide +kernel)

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
def CB4_2_2I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 0 a
def CB4_2_2I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 0 a
lemma CB4_2_2I2R0Raw_sound (a : Fin 6) :
    (CB4_2_2I2R0Raw a).Encloses (CB4_2_2I2R0Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 0 a
def CB4_2_2I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(264017467412789009261745911423 / 100000000000000000000000000000000), (90638611 / 100000000000000000000000000000000)⟩ ⟨(-801868459204174003272721095524521 / 100000000000000000000000000000000), (68821427729 / 25000000000000000000000000000000)⟩ ⟨-12, 32925283989199048774667657891, 24414062500000000000000000000⟩]
lemma CB4_2_2I2R0Certificates_valid :
    CB4_2_2I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB4_2_2I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R0Certificates (CB4_2_2I2R0CertificateIndex a)).input
lemma CB4_2_2I2R0P_check : ∀ a : Fin 6, contains (CB4_2_2I2R0Raw a) (CB4_2_2I2R0P a) = true := by
  decide +kernel
lemma CB4_2_2I2R0P_sound (a : Fin 6) :
    (CB4_2_2I2R0P a).Encloses (CB4_2_2I2R0Value a) :=
  contains_sound (CB4_2_2I2R0Raw_sound a) (CB4_2_2I2R0P_check a)
def CB4_2_2I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R0Certificates (CB4_2_2I2R0CertificateIndex a)).output
lemma CB4_2_2I2R0Terms_sound (a : Fin 6) :
    (CB4_2_2I2R0Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R0Certificates_valid
    (CB4_2_2I2R0CertificateIndex a) (CB4_2_2I2R0P_sound a)
def CB4_2_2I2R0Entropy : Ball := ⟨(264017467412789009261745911423 / 100000000000000000000000000000000), (90638611 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2R0Entropy_sound : CB4_2_2I2R0Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R0Value CB4_2_2I2R0Terms CB4_2_2I2R0Terms_sound) (by decide +kernel)
def CB4_2_2I2R0Mass : Ball := ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2R0Mass_sound : CB4_2_2I2R0Mass.Encloses (∑ a, CB4_2_2I2R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R0P CB4_2_2I2R0Value CB4_2_2I2R0P_sound) (by decide +kernel)
def CB4_2_2I2R0MassTermLogWitness : LogWitness := ⟨-12, 32925283989199048774667657891, 24414062500000000000000000000⟩
def CB4_2_2I2R0MassTermLog : Ball := ⟨(-801868459204174003272721095524521 / 100000000000000000000000000000000), (68821427729 / 25000000000000000000000000000000)⟩
lemma CB4_2_2I2R0MassTermLog_sound : CB4_2_2I2R0MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_2_2I2R0Mass_sound) (w := CB4_2_2I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB4_2_2I2R0MassTerm : Ball := ⟨(264017467412789009261745911423 / 100000000000000000000000000000000), (90638611 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2R0MassTerm_sound : CB4_2_2I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2R0Mass_sound) CB4_2_2I2R0MassTermLog_sound) (by decide +kernel)
def CB4_2_2I2R0H : Ball := ⟨0, (90638611 / 50000000000000000000000000000000)⟩
lemma CB4_2_2I2R0H_sound : CB4_2_2I2R0H.Encloses (homogeneousEntropy CB4_2_2I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R0Value CB4_2_2I2R0MassTerm_sound CB4_2_2I2R0Entropy_sound) (by decide +kernel)
def CB4_2_2I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 1 a
def CB4_2_2I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 1 a
lemma CB4_2_2I2R1Raw_sound (a : Fin 6) :
    (CB4_2_2I2R1Raw a).Encloses (CB4_2_2I2R1Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 1 a
def CB4_2_2I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3924290670247618121826431431639 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩ ⟨(19973363265378585772023469851697 / 100000000000000000000000000000000), (8310008839 / 100000000000000000000000000000000)⟩ ⟨(-254483739148179485664331227253563 / 100000000000000000000000000000000), (26469779699 / 25000000000000000000000000000000)⟩ ⟨-4, 3924290670247618121826431431639, 3125000000000000000000000000000⟩]
lemma CB4_2_2I2R1Certificates_valid :
    CB4_2_2I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB4_2_2I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R1Certificates (CB4_2_2I2R1CertificateIndex a)).input
lemma CB4_2_2I2R1P_check : ∀ a : Fin 6, contains (CB4_2_2I2R1Raw a) (CB4_2_2I2R1P a) = true := by
  decide +kernel
lemma CB4_2_2I2R1P_sound (a : Fin 6) :
    (CB4_2_2I2R1P a).Encloses (CB4_2_2I2R1Value a) :=
  contains_sound (CB4_2_2I2R1Raw_sound a) (CB4_2_2I2R1P_check a)
def CB4_2_2I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R1Certificates (CB4_2_2I2R1CertificateIndex a)).output
lemma CB4_2_2I2R1Terms_sound (a : Fin 6) :
    (CB4_2_2I2R1Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R1Certificates_valid
    (CB4_2_2I2R1CertificateIndex a) (CB4_2_2I2R1P_sound a)
def CB4_2_2I2R1Entropy : Ball := ⟨(19973363265378585772023469851697 / 100000000000000000000000000000000), (8310008839 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2R1Entropy_sound : CB4_2_2I2R1Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R1Value CB4_2_2I2R1Terms CB4_2_2I2R1Terms_sound) (by decide +kernel)
def CB4_2_2I2R1Mass : Ball := ⟨(3924290670247618121826431431639 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
lemma CB4_2_2I2R1Mass_sound : CB4_2_2I2R1Mass.Encloses (∑ a, CB4_2_2I2R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R1P CB4_2_2I2R1Value CB4_2_2I2R1P_sound) (by decide +kernel)
def CB4_2_2I2R1MassTermLogWitness : LogWitness := ⟨-4, 3924290670247618121826431431639, 3125000000000000000000000000000⟩
def CB4_2_2I2R1MassTermLog : Ball := ⟨(-254483739148179485664331227253563 / 100000000000000000000000000000000), (26469779699 / 25000000000000000000000000000000)⟩
lemma CB4_2_2I2R1MassTermLog_sound : CB4_2_2I2R1MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_2_2I2R1Mass_sound) (w := CB4_2_2I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB4_2_2I2R1MassTerm : Ball := ⟨(19973363265378585772023469851697 / 100000000000000000000000000000000), (8310008839 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2R1MassTerm_sound : CB4_2_2I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2R1Mass_sound) CB4_2_2I2R1MassTermLog_sound) (by decide +kernel)
def CB4_2_2I2R1H : Ball := ⟨0, (8310008839 / 50000000000000000000000000000000)⟩
lemma CB4_2_2I2R1H_sound : CB4_2_2I2R1H.Encloses (homogeneousEntropy CB4_2_2I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R1Value CB4_2_2I2R1MassTerm_sound CB4_2_2I2R1Entropy_sound) (by decide +kernel)
def CB4_2_2I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 2 a
def CB4_2_2I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 2 a
lemma CB4_2_2I2R2Raw_sound (a : Fin 6) :
    (CB4_2_2I2R2Raw a).Encloses (CB4_2_2I2R2Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 2 a
def CB4_2_2I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(54606597188412179771489877547937 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩ ⟨(6607567353600587271775121013497 / 20000000000000000000000000000000), (23126793581 / 100000000000000000000000000000000)⟩ ⟨(-30250774145485251926939796014479 / 50000000000000000000000000000000), (1058791187 / 2500000000000000000000000000000)⟩ ⟨-1, 54606597188412179771489877547937, 50000000000000000000000000000000⟩,
   .log ⟨(81925921763941401533420105921 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(3295170994711641414745310598131 / 100000000000000000000000000000000), (1249091203 / 100000000000000000000000000000000)⟩ ⟨(-62845855968178721135666464092211 / 12500000000000000000000000000000), (47645603363 / 25000000000000000000000000000000)⟩ ⟨-8, 81925921763941401533420105921, 48828125000000000000000000000⟩]
lemma CB4_2_2I2R2Certificates_valid :
    CB4_2_2I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB4_2_2I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R2Certificates (CB4_2_2I2R2CertificateIndex a)).input
lemma CB4_2_2I2R2P_check : ∀ a : Fin 6, contains (CB4_2_2I2R2Raw a) (CB4_2_2I2R2P a) = true := by
  decide +kernel
lemma CB4_2_2I2R2P_sound (a : Fin 6) :
    (CB4_2_2I2R2P a).Encloses (CB4_2_2I2R2Value a) :=
  contains_sound (CB4_2_2I2R2Raw_sound a) (CB4_2_2I2R2P_check a)
def CB4_2_2I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R2Certificates (CB4_2_2I2R2CertificateIndex a)).output
lemma CB4_2_2I2R2Terms_sound (a : Fin 6) :
    (CB4_2_2I2R2Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R2Certificates_valid
    (CB4_2_2I2R2CertificateIndex a) (CB4_2_2I2R2P_sound a)
def CB4_2_2I2R2Entropy : Ball := ⟨(2270812985169661110851307229101 / 6250000000000000000000000000000), (1523492799 / 6250000000000000000000000000000)⟩
lemma CB4_2_2I2R2Entropy_sound : CB4_2_2I2R2Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R2Value CB4_2_2I2R2Terms CB4_2_2I2R2Terms_sound) (by decide +kernel)
def CB4_2_2I2R2Mass : Ball := ⟨(11052400912504742196751447679061 / 20000000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
lemma CB4_2_2I2R2Mass_sound : CB4_2_2I2R2Mass.Encloses (∑ a, CB4_2_2I2R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R2P CB4_2_2I2R2Value CB4_2_2I2R2P_sound) (by decide +kernel)
def CB4_2_2I2R2MassTermLogWitness : LogWitness := ⟨-1, 11052400912504742196751447679061, 10000000000000000000000000000000⟩
def CB4_2_2I2R2MassTermLog : Ball := ⟨(-29654229602087001636360652787339 / 50000000000000000000000000000000), (42351647483 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2R2MassTermLog_sound : CB4_2_2I2R2MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_2_2I2R2Mass_sound) (w := CB4_2_2I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB4_2_2I2R2MassTerm : Ball := ⟨(4096880428921643937267339657819 / 12500000000000000000000000000000), (5851092351 / 25000000000000000000000000000000)⟩
lemma CB4_2_2I2R2MassTerm_sound : CB4_2_2I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2R2Mass_sound) CB4_2_2I2R2MassTermLog_sound) (by decide +kernel)
def CB4_2_2I2R2H : Ball := ⟨(444745541417678284435274800383 / 12500000000000000000000000000000), (11945063547 / 25000000000000000000000000000000)⟩
lemma CB4_2_2I2R2H_sound : CB4_2_2I2R2H.Encloses (homogeneousEntropy CB4_2_2I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R2Value CB4_2_2I2R2MassTerm_sound CB4_2_2I2R2Entropy_sound) (by decide +kernel)
def CB4_2_2I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 3 a
def CB4_2_2I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 3 a
lemma CB4_2_2I2R3Raw_sound (a : Fin 6) :
    (CB4_2_2I2R3Raw a).Encloses (CB4_2_2I2R3Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 3 a
def CB4_2_2I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R3Certificates_valid :
    CB4_2_2I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R3Certificates (CB4_2_2I2R3CertificateIndex a)).input
lemma CB4_2_2I2R3P_check : ∀ a : Fin 6, contains (CB4_2_2I2R3Raw a) (CB4_2_2I2R3P a) = true := by
  decide +kernel
lemma CB4_2_2I2R3P_sound (a : Fin 6) :
    (CB4_2_2I2R3P a).Encloses (CB4_2_2I2R3Value a) :=
  contains_sound (CB4_2_2I2R3Raw_sound a) (CB4_2_2I2R3P_check a)
def CB4_2_2I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R3Certificates (CB4_2_2I2R3CertificateIndex a)).output
lemma CB4_2_2I2R3Terms_sound (a : Fin 6) :
    (CB4_2_2I2R3Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R3Certificates_valid
    (CB4_2_2I2R3CertificateIndex a) (CB4_2_2I2R3P_sound a)
def CB4_2_2I2R3Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R3Entropy_sound : CB4_2_2I2R3Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R3Value CB4_2_2I2R3Terms CB4_2_2I2R3Terms_sound) (by decide +kernel)
def CB4_2_2I2R3Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R3Mass_sound : CB4_2_2I2R3Mass.Encloses (∑ a, CB4_2_2I2R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R3P CB4_2_2I2R3Value CB4_2_2I2R3P_sound) (by decide +kernel)
def CB4_2_2I2R3MassTerm : Ball := .exact 0
lemma CB4_2_2I2R3MassTerm_sound : CB4_2_2I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R3Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R3Mass_sound)
def CB4_2_2I2R3H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R3H_sound : CB4_2_2I2R3H.Encloses (homogeneousEntropy CB4_2_2I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R3Value CB4_2_2I2R3MassTerm_sound CB4_2_2I2R3Entropy_sound) (by decide +kernel)
def CB4_2_2I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 4 a
def CB4_2_2I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 4 a
lemma CB4_2_2I2R4Raw_sound (a : Fin 6) :
    (CB4_2_2I2R4Raw a).Encloses (CB4_2_2I2R4Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 4 a
def CB4_2_2I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R4Certificates_valid :
    CB4_2_2I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R4Certificates (CB4_2_2I2R4CertificateIndex a)).input
lemma CB4_2_2I2R4P_check : ∀ a : Fin 6, contains (CB4_2_2I2R4Raw a) (CB4_2_2I2R4P a) = true := by
  decide +kernel
lemma CB4_2_2I2R4P_sound (a : Fin 6) :
    (CB4_2_2I2R4P a).Encloses (CB4_2_2I2R4Value a) :=
  contains_sound (CB4_2_2I2R4Raw_sound a) (CB4_2_2I2R4P_check a)
def CB4_2_2I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R4Certificates (CB4_2_2I2R4CertificateIndex a)).output
lemma CB4_2_2I2R4Terms_sound (a : Fin 6) :
    (CB4_2_2I2R4Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R4Certificates_valid
    (CB4_2_2I2R4CertificateIndex a) (CB4_2_2I2R4P_sound a)
def CB4_2_2I2R4Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R4Entropy_sound : CB4_2_2I2R4Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R4Value CB4_2_2I2R4Terms CB4_2_2I2R4Terms_sound) (by decide +kernel)
def CB4_2_2I2R4Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R4Mass_sound : CB4_2_2I2R4Mass.Encloses (∑ a, CB4_2_2I2R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R4P CB4_2_2I2R4Value CB4_2_2I2R4P_sound) (by decide +kernel)
def CB4_2_2I2R4MassTerm : Ball := .exact 0
lemma CB4_2_2I2R4MassTerm_sound : CB4_2_2I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R4Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R4Mass_sound)
def CB4_2_2I2R4H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R4H_sound : CB4_2_2I2R4H.Encloses (homogeneousEntropy CB4_2_2I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R4Value CB4_2_2I2R4MassTerm_sound CB4_2_2I2R4Entropy_sound) (by decide +kernel)
def CB4_2_2I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 5 a
def CB4_2_2I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 5 a
lemma CB4_2_2I2R5Raw_sound (a : Fin 6) :
    (CB4_2_2I2R5Raw a).Encloses (CB4_2_2I2R5Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 5 a
def CB4_2_2I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R5Certificates_valid :
    CB4_2_2I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R5Certificates (CB4_2_2I2R5CertificateIndex a)).input
lemma CB4_2_2I2R5P_check : ∀ a : Fin 6, contains (CB4_2_2I2R5Raw a) (CB4_2_2I2R5P a) = true := by
  decide +kernel
lemma CB4_2_2I2R5P_sound (a : Fin 6) :
    (CB4_2_2I2R5P a).Encloses (CB4_2_2I2R5Value a) :=
  contains_sound (CB4_2_2I2R5Raw_sound a) (CB4_2_2I2R5P_check a)
def CB4_2_2I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R5Certificates (CB4_2_2I2R5CertificateIndex a)).output
lemma CB4_2_2I2R5Terms_sound (a : Fin 6) :
    (CB4_2_2I2R5Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R5Certificates_valid
    (CB4_2_2I2R5CertificateIndex a) (CB4_2_2I2R5P_sound a)
def CB4_2_2I2R5Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R5Entropy_sound : CB4_2_2I2R5Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R5Value CB4_2_2I2R5Terms CB4_2_2I2R5Terms_sound) (by decide +kernel)
def CB4_2_2I2R5Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R5Mass_sound : CB4_2_2I2R5Mass.Encloses (∑ a, CB4_2_2I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R5P CB4_2_2I2R5Value CB4_2_2I2R5P_sound) (by decide +kernel)
def CB4_2_2I2R5MassTerm : Ball := .exact 0
lemma CB4_2_2I2R5MassTerm_sound : CB4_2_2I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R5Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R5Mass_sound)
def CB4_2_2I2R5H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R5H_sound : CB4_2_2I2R5H.Encloses (homogeneousEntropy CB4_2_2I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R5Value CB4_2_2I2R5MassTerm_sound CB4_2_2I2R5Entropy_sound) (by decide +kernel)
def CB4_2_2I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 6 a
def CB4_2_2I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 6 a
lemma CB4_2_2I2R6Raw_sound (a : Fin 6) :
    (CB4_2_2I2R6Raw a).Encloses (CB4_2_2I2R6Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 6 a
def CB4_2_2I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R6Certificates_valid :
    CB4_2_2I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R6Certificates (CB4_2_2I2R6CertificateIndex a)).input
lemma CB4_2_2I2R6P_check : ∀ a : Fin 6, contains (CB4_2_2I2R6Raw a) (CB4_2_2I2R6P a) = true := by
  decide +kernel
lemma CB4_2_2I2R6P_sound (a : Fin 6) :
    (CB4_2_2I2R6P a).Encloses (CB4_2_2I2R6Value a) :=
  contains_sound (CB4_2_2I2R6Raw_sound a) (CB4_2_2I2R6P_check a)
def CB4_2_2I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R6Certificates (CB4_2_2I2R6CertificateIndex a)).output
lemma CB4_2_2I2R6Terms_sound (a : Fin 6) :
    (CB4_2_2I2R6Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R6Certificates_valid
    (CB4_2_2I2R6CertificateIndex a) (CB4_2_2I2R6P_sound a)
def CB4_2_2I2R6Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R6Entropy_sound : CB4_2_2I2R6Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R6Value CB4_2_2I2R6Terms CB4_2_2I2R6Terms_sound) (by decide +kernel)
def CB4_2_2I2R6Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R6Mass_sound : CB4_2_2I2R6Mass.Encloses (∑ a, CB4_2_2I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R6P CB4_2_2I2R6Value CB4_2_2I2R6P_sound) (by decide +kernel)
def CB4_2_2I2R6MassTerm : Ball := .exact 0
lemma CB4_2_2I2R6MassTerm_sound : CB4_2_2I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R6Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R6Mass_sound)
def CB4_2_2I2R6H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R6H_sound : CB4_2_2I2R6H.Encloses (homogeneousEntropy CB4_2_2I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R6Value CB4_2_2I2R6MassTerm_sound CB4_2_2I2R6Entropy_sound) (by decide +kernel)
def CB4_2_2I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 7 a
def CB4_2_2I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 7 a
lemma CB4_2_2I2R7Raw_sound (a : Fin 6) :
    (CB4_2_2I2R7Raw a).Encloses (CB4_2_2I2R7Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 7 a
def CB4_2_2I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R7Certificates_valid :
    CB4_2_2I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R7Certificates (CB4_2_2I2R7CertificateIndex a)).input
lemma CB4_2_2I2R7P_check : ∀ a : Fin 6, contains (CB4_2_2I2R7Raw a) (CB4_2_2I2R7P a) = true := by
  decide +kernel
lemma CB4_2_2I2R7P_sound (a : Fin 6) :
    (CB4_2_2I2R7P a).Encloses (CB4_2_2I2R7Value a) :=
  contains_sound (CB4_2_2I2R7Raw_sound a) (CB4_2_2I2R7P_check a)
def CB4_2_2I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R7Certificates (CB4_2_2I2R7CertificateIndex a)).output
lemma CB4_2_2I2R7Terms_sound (a : Fin 6) :
    (CB4_2_2I2R7Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R7Certificates_valid
    (CB4_2_2I2R7CertificateIndex a) (CB4_2_2I2R7P_sound a)
def CB4_2_2I2R7Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R7Entropy_sound : CB4_2_2I2R7Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R7Value CB4_2_2I2R7Terms CB4_2_2I2R7Terms_sound) (by decide +kernel)
def CB4_2_2I2R7Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R7Mass_sound : CB4_2_2I2R7Mass.Encloses (∑ a, CB4_2_2I2R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R7P CB4_2_2I2R7Value CB4_2_2I2R7P_sound) (by decide +kernel)
def CB4_2_2I2R7MassTerm : Ball := .exact 0
lemma CB4_2_2I2R7MassTerm_sound : CB4_2_2I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R7Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R7Mass_sound)
def CB4_2_2I2R7H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R7H_sound : CB4_2_2I2R7H.Encloses (homogeneousEntropy CB4_2_2I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R7Value CB4_2_2I2R7MassTerm_sound CB4_2_2I2R7Entropy_sound) (by decide +kernel)
def CB4_2_2I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 8 a
def CB4_2_2I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 8 a
lemma CB4_2_2I2R8Raw_sound (a : Fin 6) :
    (CB4_2_2I2R8Raw a).Encloses (CB4_2_2I2R8Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 8 a
def CB4_2_2I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R8Certificates_valid :
    CB4_2_2I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R8Certificates (CB4_2_2I2R8CertificateIndex a)).input
lemma CB4_2_2I2R8P_check : ∀ a : Fin 6, contains (CB4_2_2I2R8Raw a) (CB4_2_2I2R8P a) = true := by
  decide +kernel
lemma CB4_2_2I2R8P_sound (a : Fin 6) :
    (CB4_2_2I2R8P a).Encloses (CB4_2_2I2R8Value a) :=
  contains_sound (CB4_2_2I2R8Raw_sound a) (CB4_2_2I2R8P_check a)
def CB4_2_2I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R8Certificates (CB4_2_2I2R8CertificateIndex a)).output
lemma CB4_2_2I2R8Terms_sound (a : Fin 6) :
    (CB4_2_2I2R8Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R8Certificates_valid
    (CB4_2_2I2R8CertificateIndex a) (CB4_2_2I2R8P_sound a)
def CB4_2_2I2R8Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R8Entropy_sound : CB4_2_2I2R8Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R8Value CB4_2_2I2R8Terms CB4_2_2I2R8Terms_sound) (by decide +kernel)
def CB4_2_2I2R8Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R8Mass_sound : CB4_2_2I2R8Mass.Encloses (∑ a, CB4_2_2I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R8P CB4_2_2I2R8Value CB4_2_2I2R8P_sound) (by decide +kernel)
def CB4_2_2I2R8MassTerm : Ball := .exact 0
lemma CB4_2_2I2R8MassTerm_sound : CB4_2_2I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R8Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R8Mass_sound)
def CB4_2_2I2R8H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R8H_sound : CB4_2_2I2R8H.Encloses (homogeneousEntropy CB4_2_2I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R8Value CB4_2_2I2R8MassTerm_sound CB4_2_2I2R8Entropy_sound) (by decide +kernel)
def CB4_2_2I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 9 a
def CB4_2_2I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 9 a
lemma CB4_2_2I2R9Raw_sound (a : Fin 6) :
    (CB4_2_2I2R9Raw a).Encloses (CB4_2_2I2R9Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 9 a
def CB4_2_2I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R9Certificates_valid :
    CB4_2_2I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R9Certificates (CB4_2_2I2R9CertificateIndex a)).input
lemma CB4_2_2I2R9P_check : ∀ a : Fin 6, contains (CB4_2_2I2R9Raw a) (CB4_2_2I2R9P a) = true := by
  decide +kernel
lemma CB4_2_2I2R9P_sound (a : Fin 6) :
    (CB4_2_2I2R9P a).Encloses (CB4_2_2I2R9Value a) :=
  contains_sound (CB4_2_2I2R9Raw_sound a) (CB4_2_2I2R9P_check a)
def CB4_2_2I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R9Certificates (CB4_2_2I2R9CertificateIndex a)).output
lemma CB4_2_2I2R9Terms_sound (a : Fin 6) :
    (CB4_2_2I2R9Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R9Certificates_valid
    (CB4_2_2I2R9CertificateIndex a) (CB4_2_2I2R9P_sound a)
def CB4_2_2I2R9Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R9Entropy_sound : CB4_2_2I2R9Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R9Value CB4_2_2I2R9Terms CB4_2_2I2R9Terms_sound) (by decide +kernel)
def CB4_2_2I2R9Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R9Mass_sound : CB4_2_2I2R9Mass.Encloses (∑ a, CB4_2_2I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R9P CB4_2_2I2R9Value CB4_2_2I2R9P_sound) (by decide +kernel)
def CB4_2_2I2R9MassTerm : Ball := .exact 0
lemma CB4_2_2I2R9MassTerm_sound : CB4_2_2I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R9Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R9Mass_sound)
def CB4_2_2I2R9H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R9H_sound : CB4_2_2I2R9H.Encloses (homogeneousEntropy CB4_2_2I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R9Value CB4_2_2I2R9MassTerm_sound CB4_2_2I2R9Entropy_sound) (by decide +kernel)
def CB4_2_2I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 10 a
def CB4_2_2I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 10 a
lemma CB4_2_2I2R10Raw_sound (a : Fin 6) :
    (CB4_2_2I2R10Raw a).Encloses (CB4_2_2I2R10Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 10 a
def CB4_2_2I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R10Certificates_valid :
    CB4_2_2I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R10Certificates (CB4_2_2I2R10CertificateIndex a)).input
lemma CB4_2_2I2R10P_check : ∀ a : Fin 6, contains (CB4_2_2I2R10Raw a) (CB4_2_2I2R10P a) = true := by
  decide +kernel
lemma CB4_2_2I2R10P_sound (a : Fin 6) :
    (CB4_2_2I2R10P a).Encloses (CB4_2_2I2R10Value a) :=
  contains_sound (CB4_2_2I2R10Raw_sound a) (CB4_2_2I2R10P_check a)
def CB4_2_2I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R10Certificates (CB4_2_2I2R10CertificateIndex a)).output
lemma CB4_2_2I2R10Terms_sound (a : Fin 6) :
    (CB4_2_2I2R10Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R10Certificates_valid
    (CB4_2_2I2R10CertificateIndex a) (CB4_2_2I2R10P_sound a)
def CB4_2_2I2R10Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R10Entropy_sound : CB4_2_2I2R10Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R10Value CB4_2_2I2R10Terms CB4_2_2I2R10Terms_sound) (by decide +kernel)
def CB4_2_2I2R10Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R10Mass_sound : CB4_2_2I2R10Mass.Encloses (∑ a, CB4_2_2I2R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R10P CB4_2_2I2R10Value CB4_2_2I2R10P_sound) (by decide +kernel)
def CB4_2_2I2R10MassTerm : Ball := .exact 0
lemma CB4_2_2I2R10MassTerm_sound : CB4_2_2I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R10Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R10Mass_sound)
def CB4_2_2I2R10H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R10H_sound : CB4_2_2I2R10H.Encloses (homogeneousEntropy CB4_2_2I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R10Value CB4_2_2I2R10MassTerm_sound CB4_2_2I2R10Entropy_sound) (by decide +kernel)
def CB4_2_2I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 11 a
def CB4_2_2I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 11 a
lemma CB4_2_2I2R11Raw_sound (a : Fin 6) :
    (CB4_2_2I2R11Raw a).Encloses (CB4_2_2I2R11Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 11 a
def CB4_2_2I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R11Certificates_valid :
    CB4_2_2I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R11Certificates (CB4_2_2I2R11CertificateIndex a)).input
lemma CB4_2_2I2R11P_check : ∀ a : Fin 6, contains (CB4_2_2I2R11Raw a) (CB4_2_2I2R11P a) = true := by
  decide +kernel
lemma CB4_2_2I2R11P_sound (a : Fin 6) :
    (CB4_2_2I2R11P a).Encloses (CB4_2_2I2R11Value a) :=
  contains_sound (CB4_2_2I2R11Raw_sound a) (CB4_2_2I2R11P_check a)
def CB4_2_2I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R11Certificates (CB4_2_2I2R11CertificateIndex a)).output
lemma CB4_2_2I2R11Terms_sound (a : Fin 6) :
    (CB4_2_2I2R11Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R11Certificates_valid
    (CB4_2_2I2R11CertificateIndex a) (CB4_2_2I2R11P_sound a)
def CB4_2_2I2R11Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R11Entropy_sound : CB4_2_2I2R11Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R11Value CB4_2_2I2R11Terms CB4_2_2I2R11Terms_sound) (by decide +kernel)
def CB4_2_2I2R11Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R11Mass_sound : CB4_2_2I2R11Mass.Encloses (∑ a, CB4_2_2I2R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R11P CB4_2_2I2R11Value CB4_2_2I2R11P_sound) (by decide +kernel)
def CB4_2_2I2R11MassTerm : Ball := .exact 0
lemma CB4_2_2I2R11MassTerm_sound : CB4_2_2I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R11Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R11Mass_sound)
def CB4_2_2I2R11H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R11H_sound : CB4_2_2I2R11H.Encloses (homogeneousEntropy CB4_2_2I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R11Value CB4_2_2I2R11MassTerm_sound CB4_2_2I2R11Entropy_sound) (by decide +kernel)
def CB4_2_2I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 12 a
def CB4_2_2I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 12 a
lemma CB4_2_2I2R12Raw_sound (a : Fin 6) :
    (CB4_2_2I2R12Raw a).Encloses (CB4_2_2I2R12Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 12 a
def CB4_2_2I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R12Certificates_valid :
    CB4_2_2I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R12Certificates (CB4_2_2I2R12CertificateIndex a)).input
lemma CB4_2_2I2R12P_check : ∀ a : Fin 6, contains (CB4_2_2I2R12Raw a) (CB4_2_2I2R12P a) = true := by
  decide +kernel
lemma CB4_2_2I2R12P_sound (a : Fin 6) :
    (CB4_2_2I2R12P a).Encloses (CB4_2_2I2R12Value a) :=
  contains_sound (CB4_2_2I2R12Raw_sound a) (CB4_2_2I2R12P_check a)
def CB4_2_2I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R12Certificates (CB4_2_2I2R12CertificateIndex a)).output
lemma CB4_2_2I2R12Terms_sound (a : Fin 6) :
    (CB4_2_2I2R12Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R12Certificates_valid
    (CB4_2_2I2R12CertificateIndex a) (CB4_2_2I2R12P_sound a)
def CB4_2_2I2R12Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R12Entropy_sound : CB4_2_2I2R12Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R12Value CB4_2_2I2R12Terms CB4_2_2I2R12Terms_sound) (by decide +kernel)
def CB4_2_2I2R12Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R12Mass_sound : CB4_2_2I2R12Mass.Encloses (∑ a, CB4_2_2I2R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R12P CB4_2_2I2R12Value CB4_2_2I2R12P_sound) (by decide +kernel)
def CB4_2_2I2R12MassTerm : Ball := .exact 0
lemma CB4_2_2I2R12MassTerm_sound : CB4_2_2I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R12Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R12Mass_sound)
def CB4_2_2I2R12H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R12H_sound : CB4_2_2I2R12H.Encloses (homogeneousEntropy CB4_2_2I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R12Value CB4_2_2I2R12MassTerm_sound CB4_2_2I2R12Entropy_sound) (by decide +kernel)
def CB4_2_2I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 13 a
def CB4_2_2I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 13 a
lemma CB4_2_2I2R13Raw_sound (a : Fin 6) :
    (CB4_2_2I2R13Raw a).Encloses (CB4_2_2I2R13Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 13 a
def CB4_2_2I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R13Certificates_valid :
    CB4_2_2I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R13Certificates (CB4_2_2I2R13CertificateIndex a)).input
lemma CB4_2_2I2R13P_check : ∀ a : Fin 6, contains (CB4_2_2I2R13Raw a) (CB4_2_2I2R13P a) = true := by
  decide +kernel
lemma CB4_2_2I2R13P_sound (a : Fin 6) :
    (CB4_2_2I2R13P a).Encloses (CB4_2_2I2R13Value a) :=
  contains_sound (CB4_2_2I2R13Raw_sound a) (CB4_2_2I2R13P_check a)
def CB4_2_2I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R13Certificates (CB4_2_2I2R13CertificateIndex a)).output
lemma CB4_2_2I2R13Terms_sound (a : Fin 6) :
    (CB4_2_2I2R13Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R13Certificates_valid
    (CB4_2_2I2R13CertificateIndex a) (CB4_2_2I2R13P_sound a)
def CB4_2_2I2R13Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R13Entropy_sound : CB4_2_2I2R13Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R13Value CB4_2_2I2R13Terms CB4_2_2I2R13Terms_sound) (by decide +kernel)
def CB4_2_2I2R13Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R13Mass_sound : CB4_2_2I2R13Mass.Encloses (∑ a, CB4_2_2I2R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R13P CB4_2_2I2R13Value CB4_2_2I2R13P_sound) (by decide +kernel)
def CB4_2_2I2R13MassTerm : Ball := .exact 0
lemma CB4_2_2I2R13MassTerm_sound : CB4_2_2I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R13Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R13Mass_sound)
def CB4_2_2I2R13H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R13H_sound : CB4_2_2I2R13H.Encloses (homogeneousEntropy CB4_2_2I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R13Value CB4_2_2I2R13MassTerm_sound CB4_2_2I2R13Entropy_sound) (by decide +kernel)
def CB4_2_2I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 14 a
def CB4_2_2I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 14 a
lemma CB4_2_2I2R14Raw_sound (a : Fin 6) :
    (CB4_2_2I2R14Raw a).Encloses (CB4_2_2I2R14Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 14 a
def CB4_2_2I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R14Certificates_valid :
    CB4_2_2I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R14Certificates (CB4_2_2I2R14CertificateIndex a)).input
lemma CB4_2_2I2R14P_check : ∀ a : Fin 6, contains (CB4_2_2I2R14Raw a) (CB4_2_2I2R14P a) = true := by
  decide +kernel
lemma CB4_2_2I2R14P_sound (a : Fin 6) :
    (CB4_2_2I2R14P a).Encloses (CB4_2_2I2R14Value a) :=
  contains_sound (CB4_2_2I2R14Raw_sound a) (CB4_2_2I2R14P_check a)
def CB4_2_2I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R14Certificates (CB4_2_2I2R14CertificateIndex a)).output
lemma CB4_2_2I2R14Terms_sound (a : Fin 6) :
    (CB4_2_2I2R14Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R14Certificates_valid
    (CB4_2_2I2R14CertificateIndex a) (CB4_2_2I2R14P_sound a)
def CB4_2_2I2R14Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R14Entropy_sound : CB4_2_2I2R14Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R14Value CB4_2_2I2R14Terms CB4_2_2I2R14Terms_sound) (by decide +kernel)
def CB4_2_2I2R14Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R14Mass_sound : CB4_2_2I2R14Mass.Encloses (∑ a, CB4_2_2I2R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R14P CB4_2_2I2R14Value CB4_2_2I2R14P_sound) (by decide +kernel)
def CB4_2_2I2R14MassTerm : Ball := .exact 0
lemma CB4_2_2I2R14MassTerm_sound : CB4_2_2I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R14Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R14Mass_sound)
def CB4_2_2I2R14H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R14H_sound : CB4_2_2I2R14H.Encloses (homogeneousEntropy CB4_2_2I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R14Value CB4_2_2I2R14MassTerm_sound CB4_2_2I2R14Entropy_sound) (by decide +kernel)
def CB4_2_2I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 15 a
def CB4_2_2I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 15 a
lemma CB4_2_2I2R15Raw_sound (a : Fin 6) :
    (CB4_2_2I2R15Raw a).Encloses (CB4_2_2I2R15Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 15 a
def CB4_2_2I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R15Certificates_valid :
    CB4_2_2I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R15Certificates (CB4_2_2I2R15CertificateIndex a)).input
lemma CB4_2_2I2R15P_check : ∀ a : Fin 6, contains (CB4_2_2I2R15Raw a) (CB4_2_2I2R15P a) = true := by
  decide +kernel
lemma CB4_2_2I2R15P_sound (a : Fin 6) :
    (CB4_2_2I2R15P a).Encloses (CB4_2_2I2R15Value a) :=
  contains_sound (CB4_2_2I2R15Raw_sound a) (CB4_2_2I2R15P_check a)
def CB4_2_2I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R15Certificates (CB4_2_2I2R15CertificateIndex a)).output
lemma CB4_2_2I2R15Terms_sound (a : Fin 6) :
    (CB4_2_2I2R15Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R15Certificates_valid
    (CB4_2_2I2R15CertificateIndex a) (CB4_2_2I2R15P_sound a)
def CB4_2_2I2R15Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R15Entropy_sound : CB4_2_2I2R15Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R15Value CB4_2_2I2R15Terms CB4_2_2I2R15Terms_sound) (by decide +kernel)
def CB4_2_2I2R15Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R15Mass_sound : CB4_2_2I2R15Mass.Encloses (∑ a, CB4_2_2I2R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R15P CB4_2_2I2R15Value CB4_2_2I2R15P_sound) (by decide +kernel)
def CB4_2_2I2R15MassTerm : Ball := .exact 0
lemma CB4_2_2I2R15MassTerm_sound : CB4_2_2I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R15Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R15Mass_sound)
def CB4_2_2I2R15H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R15H_sound : CB4_2_2I2R15H.Encloses (homogeneousEntropy CB4_2_2I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R15Value CB4_2_2I2R15MassTerm_sound CB4_2_2I2R15Entropy_sound) (by decide +kernel)
def CB4_2_2I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) 16 a
def CB4_2_2I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 4 2 2)) B4_2_2Law (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) 16 a
lemma CB4_2_2I2R16Raw_sound (a : Fin 6) :
    (CB4_2_2I2R16Raw a).Encloses (CB4_2_2I2R16Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 16 a
def CB4_2_2I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB4_2_2I2R16Certificates_valid :
    CB4_2_2I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R16Certificates (CB4_2_2I2R16CertificateIndex a)).input
lemma CB4_2_2I2R16P_check : ∀ a : Fin 6, contains (CB4_2_2I2R16Raw a) (CB4_2_2I2R16P a) = true := by
  decide +kernel
lemma CB4_2_2I2R16P_sound (a : Fin 6) :
    (CB4_2_2I2R16P a).Encloses (CB4_2_2I2R16Value a) :=
  contains_sound (CB4_2_2I2R16Raw_sound a) (CB4_2_2I2R16P_check a)
def CB4_2_2I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I2R16Certificates (CB4_2_2I2R16CertificateIndex a)).output
lemma CB4_2_2I2R16Terms_sound (a : Fin 6) :
    (CB4_2_2I2R16Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R16Certificates_valid
    (CB4_2_2I2R16CertificateIndex a) (CB4_2_2I2R16P_sound a)
def CB4_2_2I2R16Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R16Entropy_sound : CB4_2_2I2R16Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R16Value CB4_2_2I2R16Terms CB4_2_2I2R16Terms_sound) (by decide +kernel)
def CB4_2_2I2R16Mass : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R16Mass_sound : CB4_2_2I2R16Mass.Encloses (∑ a, CB4_2_2I2R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R16P CB4_2_2I2R16Value CB4_2_2I2R16P_sound) (by decide +kernel)
def CB4_2_2I2R16MassTerm : Ball := .exact 0
lemma CB4_2_2I2R16MassTerm_sound : CB4_2_2I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R16Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R16Mass_sound)
def CB4_2_2I2R16H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2R16H_sound : CB4_2_2I2R16H.Encloses (homogeneousEntropy CB4_2_2I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R16Value CB4_2_2I2R16MassTerm_sound CB4_2_2I2R16Entropy_sound) (by decide +kernel)
def CB4_2_2I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB4_2_2I2R0H
  | 1 => CB4_2_2I2R1H
  | 2 => CB4_2_2I2R2H
  | 3 => CB4_2_2I2R3H
  | 4 => CB4_2_2I2R4H
  | 5 => CB4_2_2I2R5H
  | 6 => CB4_2_2I2R6H
  | 7 => CB4_2_2I2R7H
  | 8 => CB4_2_2I2R8H
  | 9 => CB4_2_2I2R9H
  | 10 => CB4_2_2I2R10H
  | 11 => CB4_2_2I2R11H
  | 12 => CB4_2_2I2R12H
  | 13 => CB4_2_2I2R13H
  | 14 => CB4_2_2I2R14H
  | 15 => CB4_2_2I2R15H
  | 16 => CB4_2_2I2R16H
  | _ => (.exact 0)
lemma CB4_2_2I2ResidualEntropies_sound (k : Fin 17) :
    (CB4_2_2I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB4_2_2I2R0H_sound
  · exact CB4_2_2I2R1H_sound
  · exact CB4_2_2I2R2H_sound
  · exact CB4_2_2I2R3H_sound
  · exact CB4_2_2I2R4H_sound
  · exact CB4_2_2I2R5H_sound
  · exact CB4_2_2I2R6H_sound
  · exact CB4_2_2I2R7H_sound
  · exact CB4_2_2I2R8H_sound
  · exact CB4_2_2I2R9H_sound
  · exact CB4_2_2I2R10H_sound
  · exact CB4_2_2I2R11H_sound
  · exact CB4_2_2I2R12H_sound
  · exact CB4_2_2I2R13H_sound
  · exact CB4_2_2I2R14H_sound
  · exact CB4_2_2I2R15H_sound
  · exact CB4_2_2I2R16H_sound
def CB4_2_2I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 4 2 2) (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2) a : ℝ)
def CB4_2_2I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 447669, 250000⟩
def CB4_2_2I2S2_0_2E_2Log : Ball := ⟨(-11055397836918052136994139561117 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma CB4_2_2I2S2_0_2E_2Log_sound : CB4_2_2I2S2_0_2E_2Log.Encloses (Real.log (CB4_2_2I2S2_0_2Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B4_2_2Little_sound (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2)) (2 : Fin 6)) (w := CB4_2_2I2S2_0_2E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB4_2_2I2S2_0_2E_2 : Ball := ⟨(9898317788510534964232058926371 / 100000000000000000000000000000000), (151676157 / 400000000000000000000000000000)⟩
lemma CB4_2_2I2S2_0_2E_2_sound : CB4_2_2I2S2_0_2E_2.Encloses (Foundation.entropyTerm (CB4_2_2I2S2_0_2Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B4_2_2Little_sound (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2)) (2 : Fin 6)) CB4_2_2I2S2_0_2E_2Log_sound) (by decide +kernel)
def CB4_2_2I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 52331, 31250⟩
def CB4_2_2I2S2_0_2E_3Log : Ball := ⟨(-14106369804520244990198383124901 / 6250000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma CB4_2_2I2S2_0_2E_3Log_sound : CB4_2_2I2S2_0_2E_3Log.Encloses (Real.log (CB4_2_2I2S2_0_2Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B4_2_2Little_sound (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2)) (3 : Fin 6)) (w := CB4_2_2I2S2_0_2E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB4_2_2I2S2_0_2E_3 : Ball := ⟨(11811207011845583049313145396947 / 50000000000000000000000000000000), (2770380073 / 25000000000000000000000000000000)⟩
lemma CB4_2_2I2S2_0_2E_3_sound : CB4_2_2I2S2_0_2E_3.Encloses (Foundation.entropyTerm (CB4_2_2I2S2_0_2Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B4_2_2Little_sound (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2)) (3 : Fin 6)) CB4_2_2I2S2_0_2E_3Log_sound) (by decide +kernel)
def CB4_2_2I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9898317788510534964232058926371 / 100000000000000000000000000000000), (151676157 / 400000000000000000000000000000)⟩
  | 3 => ⟨(11811207011845583049313145396947 / 50000000000000000000000000000000), (2770380073 / 25000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB4_2_2I2S2_0_2Terms_sound (a : Fin 6) :
    (CB4_2_2I2S2_0_2Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2S2_0_2Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2)) (1 : Fin 6)))
  · exact CB4_2_2I2S2_0_2E_2_sound
  · exact CB4_2_2I2S2_0_2E_3_sound
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2)) (5 : Fin 6)))
def CB4_2_2I2S2_0_2Entropy : Ball := ⟨(6704146362440340212571669944053 / 20000000000000000000000000000000), (24500279771 / 50000000000000000000000000000000)⟩
lemma CB4_2_2I2S2_0_2Entropy_sound : CB4_2_2I2S2_0_2Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2S2_0_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2S2_0_2Value CB4_2_2I2S2_0_2Terms CB4_2_2I2S2_0_2Terms_sound) (by decide +kernel)
def CB4_2_2I2S2_0_2Mass : Ball := ⟨1, 0⟩
lemma CB4_2_2I2S2_0_2Mass_sound : CB4_2_2I2S2_0_2Mass.Encloses (∑ a, CB4_2_2I2S2_0_2Value a) := by
  exact contains_sound (finSumBall_sound 6 (B4_2_2Little (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2)) CB4_2_2I2S2_0_2Value (B4_2_2Little_sound (shape 2 0 2) ((stageBPriority (shape 4 2 2)) 2))) (by decide +kernel)
def CB4_2_2I2S2_0_2MassTermLog : Ball := .exact 0
lemma CB4_2_2I2S2_0_2MassTermLog_sound : CB4_2_2I2S2_0_2MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2S2_0_2Value a))) := by
  exact log_exact_one_ball (CB4_2_2I2S2_0_2Mass_sound)
def CB4_2_2I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S2_0_2MassTerm_sound : CB4_2_2I2S2_0_2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2S2_0_2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2S2_0_2Mass_sound) CB4_2_2I2S2_0_2MassTermLog_sound) (by decide +kernel)
def CB4_2_2I2S2_0_2H : Ball := ⟨(6704146362440340212571669944053 / 20000000000000000000000000000000), (24500279771 / 50000000000000000000000000000000)⟩
lemma CB4_2_2I2S2_0_2H_sound : CB4_2_2I2S2_0_2H.Encloses (homogeneousEntropy CB4_2_2I2S2_0_2Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2S2_0_2Value CB4_2_2I2S2_0_2MassTerm_sound CB4_2_2I2S2_0_2Entropy_sound) (by decide +kernel)
def CB4_2_2I2S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 2 2) (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2) a : ℝ)
def CB4_2_2I2S2_2_0E_2LogWitness : LogWitness := ⟨-1, 447549, 250000⟩
def CB4_2_2I2S2_2_0E_2Log : Ball := ⟨(-692637934343495837134511622293 / 6250000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma CB4_2_2I2S2_2_0E_2Log_sound : CB4_2_2I2S2_2_0E_2Log.Encloses (Real.log (CB4_2_2I2S2_2_0Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B4_2_2Little_sound (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2)) (2 : Fin 6)) (w := CB4_2_2I2S2_2_0E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB4_2_2I2S2_2_0E_2 : Ball := ⟨(495983063803995549461941667273 / 5000000000000000000000000000000), (7581774971 / 20000000000000000000000000000000)⟩
lemma CB4_2_2I2S2_2_0E_2_sound : CB4_2_2I2S2_2_0E_2.Encloses (Foundation.entropyTerm (CB4_2_2I2S2_2_0Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B4_2_2Little_sound (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2)) (2 : Fin 6)) CB4_2_2I2S2_2_0E_2Log_sound) (by decide +kernel)
def CB4_2_2I2S2_2_0E_3LogWitness : LogWitness := ⟨-4, 52451, 31250⟩
def CB4_2_2I2S2_2_0E_3Log : Ball := ⟨(-225472869798470476592187191794959 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma CB4_2_2I2S2_2_0E_3Log_sound : CB4_2_2I2S2_2_0E_3Log.Encloses (Real.log (CB4_2_2I2S2_2_0Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B4_2_2Little_sound (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2)) (3 : Fin 6)) (w := CB4_2_2I2S2_2_0E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB4_2_2I2S2_2_0E_3 : Ball := ⟨(946102199503965997418944831747 / 4000000000000000000000000000000), (11106931281 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2S2_2_0E_3_sound : CB4_2_2I2S2_2_0E_3.Encloses (Foundation.entropyTerm (CB4_2_2I2S2_2_0Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B4_2_2Little_sound (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2)) (3 : Fin 6)) CB4_2_2I2S2_2_0E_3Log_sound) (by decide +kernel)
def CB4_2_2I2S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(495983063803995549461941667273 / 5000000000000000000000000000000), (7581774971 / 20000000000000000000000000000000)⟩
  | 3 => ⟨(946102199503965997418944831747 / 4000000000000000000000000000000), (11106931281 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB4_2_2I2S2_2_0Terms_sound (a : Fin 6) :
    (CB4_2_2I2S2_2_0Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2S2_2_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2)) (1 : Fin 6)))
  · exact CB4_2_2I2S2_2_0E_2_sound
  · exact CB4_2_2I2S2_2_0E_3_sound
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2)) (5 : Fin 6)))
def CB4_2_2I2S2_2_0Entropy : Ball := ⟨(6714443252735812184942490827827 / 20000000000000000000000000000000), (6126975767 / 12500000000000000000000000000000)⟩
lemma CB4_2_2I2S2_2_0Entropy_sound : CB4_2_2I2S2_2_0Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2S2_2_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2S2_2_0Value CB4_2_2I2S2_2_0Terms CB4_2_2I2S2_2_0Terms_sound) (by decide +kernel)
def CB4_2_2I2S2_2_0Mass : Ball := ⟨1, 0⟩
lemma CB4_2_2I2S2_2_0Mass_sound : CB4_2_2I2S2_2_0Mass.Encloses (∑ a, CB4_2_2I2S2_2_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B4_2_2Little (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2)) CB4_2_2I2S2_2_0Value (B4_2_2Little_sound (shape 2 2 0) ((stageBPriority (shape 4 2 2)) 2))) (by decide +kernel)
def CB4_2_2I2S2_2_0MassTermLog : Ball := .exact 0
lemma CB4_2_2I2S2_2_0MassTermLog_sound : CB4_2_2I2S2_2_0MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2S2_2_0Value a))) := by
  exact log_exact_one_ball (CB4_2_2I2S2_2_0Mass_sound)
def CB4_2_2I2S2_2_0MassTerm : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S2_2_0MassTerm_sound : CB4_2_2I2S2_2_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2S2_2_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2S2_2_0Mass_sound) CB4_2_2I2S2_2_0MassTermLog_sound) (by decide +kernel)
def CB4_2_2I2S2_2_0H : Ball := ⟨(6714443252735812184942490827827 / 20000000000000000000000000000000), (6126975767 / 12500000000000000000000000000000)⟩
lemma CB4_2_2I2S2_2_0H_sound : CB4_2_2I2S2_2_0H.Encloses (homogeneousEntropy CB4_2_2I2S2_2_0Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2S2_2_0Value CB4_2_2I2S2_2_0MassTerm_sound CB4_2_2I2S2_2_0Entropy_sound) (by decide +kernel)
def CB4_2_2I2S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 4 2 2) (shape 3 0 1) ((stageBPriority (shape 4 2 2)) 2) a : ℝ)
def CB4_2_2I2S3_0_1E_4Log : Ball := .exact 0
lemma CB4_2_2I2S3_0_1E_4Log_sound : CB4_2_2I2S3_0_1E_4Log.Encloses (Real.log (CB4_2_2I2S3_0_1Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B4_2_2Little_sound (shape 3 0 1) ((stageBPriority (shape 4 2 2)) 2)) (4 : Fin 6))
def CB4_2_2I2S3_0_1E_4 : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S3_0_1E_4_sound : CB4_2_2I2S3_0_1E_4.Encloses (Foundation.entropyTerm (CB4_2_2I2S3_0_1Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B4_2_2Little_sound (shape 3 0 1) ((stageBPriority (shape 4 2 2)) 2)) (4 : Fin 6)) CB4_2_2I2S3_0_1E_4Log_sound) (by decide +kernel)
def CB4_2_2I2S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB4_2_2I2S3_0_1Terms_sound (a : Fin 6) :
    (CB4_2_2I2S3_0_1Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2S3_0_1Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 3 0 1) ((stageBPriority (shape 4 2 2)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 3 0 1) ((stageBPriority (shape 4 2 2)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 3 0 1) ((stageBPriority (shape 4 2 2)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 3 0 1) ((stageBPriority (shape 4 2 2)) 2)) (3 : Fin 6)))
  · exact CB4_2_2I2S3_0_1E_4_sound
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 3 0 1) ((stageBPriority (shape 4 2 2)) 2)) (5 : Fin 6)))
def CB4_2_2I2S3_0_1Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S3_0_1Entropy_sound : CB4_2_2I2S3_0_1Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2S3_0_1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2S3_0_1Value CB4_2_2I2S3_0_1Terms CB4_2_2I2S3_0_1Terms_sound) (by decide +kernel)
def CB4_2_2I2S3_0_1Mass : Ball := ⟨1, 0⟩
lemma CB4_2_2I2S3_0_1Mass_sound : CB4_2_2I2S3_0_1Mass.Encloses (∑ a, CB4_2_2I2S3_0_1Value a) := by
  exact contains_sound (finSumBall_sound 6 (B4_2_2Little (shape 3 0 1) ((stageBPriority (shape 4 2 2)) 2)) CB4_2_2I2S3_0_1Value (B4_2_2Little_sound (shape 3 0 1) ((stageBPriority (shape 4 2 2)) 2))) (by decide +kernel)
def CB4_2_2I2S3_0_1MassTermLog : Ball := .exact 0
lemma CB4_2_2I2S3_0_1MassTermLog_sound : CB4_2_2I2S3_0_1MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2S3_0_1Value a))) := by
  exact log_exact_one_ball (CB4_2_2I2S3_0_1Mass_sound)
def CB4_2_2I2S3_0_1MassTerm : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S3_0_1MassTerm_sound : CB4_2_2I2S3_0_1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2S3_0_1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2S3_0_1Mass_sound) CB4_2_2I2S3_0_1MassTermLog_sound) (by decide +kernel)
def CB4_2_2I2S3_0_1H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S3_0_1H_sound : CB4_2_2I2S3_0_1H.Encloses (homogeneousEntropy CB4_2_2I2S3_0_1Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2S3_0_1Value CB4_2_2I2S3_0_1MassTerm_sound CB4_2_2I2S3_0_1Entropy_sound) (by decide +kernel)
def CB4_2_2I2S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 2 2) (shape 3 1 0) ((stageBPriority (shape 4 2 2)) 2) a : ℝ)
def CB4_2_2I2S3_1_0E_4Log : Ball := .exact 0
lemma CB4_2_2I2S3_1_0E_4Log_sound : CB4_2_2I2S3_1_0E_4Log.Encloses (Real.log (CB4_2_2I2S3_1_0Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B4_2_2Little_sound (shape 3 1 0) ((stageBPriority (shape 4 2 2)) 2)) (4 : Fin 6))
def CB4_2_2I2S3_1_0E_4 : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S3_1_0E_4_sound : CB4_2_2I2S3_1_0E_4.Encloses (Foundation.entropyTerm (CB4_2_2I2S3_1_0Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B4_2_2Little_sound (shape 3 1 0) ((stageBPriority (shape 4 2 2)) 2)) (4 : Fin 6)) CB4_2_2I2S3_1_0E_4Log_sound) (by decide +kernel)
def CB4_2_2I2S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB4_2_2I2S3_1_0Terms_sound (a : Fin 6) :
    (CB4_2_2I2S3_1_0Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2S3_1_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 3 1 0) ((stageBPriority (shape 4 2 2)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 3 1 0) ((stageBPriority (shape 4 2 2)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 3 1 0) ((stageBPriority (shape 4 2 2)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 3 1 0) ((stageBPriority (shape 4 2 2)) 2)) (3 : Fin 6)))
  · exact CB4_2_2I2S3_1_0E_4_sound
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 3 1 0) ((stageBPriority (shape 4 2 2)) 2)) (5 : Fin 6)))
def CB4_2_2I2S3_1_0Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S3_1_0Entropy_sound : CB4_2_2I2S3_1_0Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2S3_1_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2S3_1_0Value CB4_2_2I2S3_1_0Terms CB4_2_2I2S3_1_0Terms_sound) (by decide +kernel)
def CB4_2_2I2S3_1_0Mass : Ball := ⟨1, 0⟩
lemma CB4_2_2I2S3_1_0Mass_sound : CB4_2_2I2S3_1_0Mass.Encloses (∑ a, CB4_2_2I2S3_1_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B4_2_2Little (shape 3 1 0) ((stageBPriority (shape 4 2 2)) 2)) CB4_2_2I2S3_1_0Value (B4_2_2Little_sound (shape 3 1 0) ((stageBPriority (shape 4 2 2)) 2))) (by decide +kernel)
def CB4_2_2I2S3_1_0MassTermLog : Ball := .exact 0
lemma CB4_2_2I2S3_1_0MassTermLog_sound : CB4_2_2I2S3_1_0MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2S3_1_0Value a))) := by
  exact log_exact_one_ball (CB4_2_2I2S3_1_0Mass_sound)
def CB4_2_2I2S3_1_0MassTerm : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S3_1_0MassTerm_sound : CB4_2_2I2S3_1_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2S3_1_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2S3_1_0Mass_sound) CB4_2_2I2S3_1_0MassTermLog_sound) (by decide +kernel)
def CB4_2_2I2S3_1_0H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S3_1_0H_sound : CB4_2_2I2S3_1_0H.Encloses (homogeneousEntropy CB4_2_2I2S3_1_0Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2S3_1_0Value CB4_2_2I2S3_1_0MassTerm_sound CB4_2_2I2S3_1_0Entropy_sound) (by decide +kernel)
def CB4_2_2I2S4_0_0Value (a : Fin 6) : ℝ := (littleLaw (shape 4 2 2) (shape 4 0 0) ((stageBPriority (shape 4 2 2)) 2) a : ℝ)
def CB4_2_2I2S4_0_0E_5Log : Ball := .exact 0
lemma CB4_2_2I2S4_0_0E_5Log_sound : CB4_2_2I2S4_0_0E_5Log.Encloses (Real.log (CB4_2_2I2S4_0_0Value (5 : Fin 6))) := by
  exact log_exact_one_ball ((B4_2_2Little_sound (shape 4 0 0) ((stageBPriority (shape 4 2 2)) 2)) (5 : Fin 6))
def CB4_2_2I2S4_0_0E_5 : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S4_0_0E_5_sound : CB4_2_2I2S4_0_0E_5.Encloses (Foundation.entropyTerm (CB4_2_2I2S4_0_0Value (5 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B4_2_2Little_sound (shape 4 0 0) ((stageBPriority (shape 4 2 2)) 2)) (5 : Fin 6)) CB4_2_2I2S4_0_0E_5Log_sound) (by decide +kernel)
def CB4_2_2I2S4_0_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB4_2_2I2S4_0_0Terms_sound (a : Fin 6) :
    (CB4_2_2I2S4_0_0Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2S4_0_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 4 0 0) ((stageBPriority (shape 4 2 2)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 4 0 0) ((stageBPriority (shape 4 2 2)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 4 0 0) ((stageBPriority (shape 4 2 2)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 4 0 0) ((stageBPriority (shape 4 2 2)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B4_2_2Little_sound (shape 4 0 0) ((stageBPriority (shape 4 2 2)) 2)) (4 : Fin 6)))
  · exact CB4_2_2I2S4_0_0E_5_sound
def CB4_2_2I2S4_0_0Entropy : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S4_0_0Entropy_sound : CB4_2_2I2S4_0_0Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2S4_0_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2S4_0_0Value CB4_2_2I2S4_0_0Terms CB4_2_2I2S4_0_0Terms_sound) (by decide +kernel)
def CB4_2_2I2S4_0_0Mass : Ball := ⟨1, 0⟩
lemma CB4_2_2I2S4_0_0Mass_sound : CB4_2_2I2S4_0_0Mass.Encloses (∑ a, CB4_2_2I2S4_0_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B4_2_2Little (shape 4 0 0) ((stageBPriority (shape 4 2 2)) 2)) CB4_2_2I2S4_0_0Value (B4_2_2Little_sound (shape 4 0 0) ((stageBPriority (shape 4 2 2)) 2))) (by decide +kernel)
def CB4_2_2I2S4_0_0MassTermLog : Ball := .exact 0
lemma CB4_2_2I2S4_0_0MassTermLog_sound : CB4_2_2I2S4_0_0MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2S4_0_0Value a))) := by
  exact log_exact_one_ball (CB4_2_2I2S4_0_0Mass_sound)
def CB4_2_2I2S4_0_0MassTerm : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S4_0_0MassTerm_sound : CB4_2_2I2S4_0_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2S4_0_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2S4_0_0Mass_sound) CB4_2_2I2S4_0_0MassTermLog_sound) (by decide +kernel)
def CB4_2_2I2S4_0_0H : Ball := ⟨0, 0⟩
lemma CB4_2_2I2S4_0_0H_sound : CB4_2_2I2S4_0_0H.Encloses (homogeneousEntropy CB4_2_2I2S4_0_0Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2S4_0_0Value CB4_2_2I2S4_0_0MassTerm_sound CB4_2_2I2S4_0_0Entropy_sound) (by decide +kernel)
def CB4_2_2I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 0, 2 => CB4_2_2I2S2_0_2H
  | 2, 2, 0 => CB4_2_2I2S2_2_0H
  | 3, 0, 1 => CB4_2_2I2S3_0_1H
  | 3, 1, 0 => CB4_2_2I2S3_1_0H
  | 4, 0, 0 => CB4_2_2I2S4_0_0H
  | _, _, _ => (.exact 0)
lemma CB4_2_2I2Singles_sound (u : Shape) (hu : u ∈ below (shape 4 2 2))
    (hd : designated (stageBPriority (shape 4 2 2)) 2 u) :
    (CB4_2_2I2Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) u)) := by
  rw [B4_2_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (stageBPriority (shape 4 2 2)) 2 (shape 0 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 4 2 2)) 2 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 4 2 2)) 2 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact CB4_2_2I2S2_0_2H_sound
  · exact (show ¬ designated (stageBPriority (shape 4 2 2)) 2 (shape 2 1 1) by decide +kernel) hd |>.elim
  · exact CB4_2_2I2S2_2_0H_sound
  · exact CB4_2_2I2S3_0_1H_sound
  · exact CB4_2_2I2S3_1_0H_sound
  · exact CB4_2_2I2S4_0_0H_sound
def CB4_2_2I2Singleton : Ball := ⟨(388803395094619629894314275621 / 4000000000000000000000000000000), (2840022457 / 20000000000000000000000000000000)⟩
lemma CB4_2_2I2Singleton_sound : CB4_2_2I2Singleton.Encloses
    (singletonEntropy (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2
    CB4_2_2I2Singles (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) CB4_2_2I2Singles_sound) (by decide +kernel)
def CB4_2_2I2Group : Ball := ⟨(13278049208706917022840055293589 / 100000000000000000000000000000000), (78781661373 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2Group_sound : CB4_2_2I2Group.Encloses
    (groupedEntropy (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB4_2_2I2Singleton_sound
    (finSumBall_sound 17 CB4_2_2I2ResidualEntropies _ CB4_2_2I2ResidualEntropies_sound)) (by decide +kernel)

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
def CB4_2_2I2H : Ball := ⟨(58605953662594893341663948712861 / 100000000000000000000000000000000), (258645600317 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I2_sound : CB4_2_2I2H.Encloses (stageBCapacity (shape 4 2 2) 2) := by
  have hb := contains_sound (Ball.add_sound CB4_2_2I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB4_2_2I2Group_sound)))
    (show contains (.add CB4_2_2I2PairH (.neg (.mul (.exact 2) CB4_2_2I2Group))) CB4_2_2I2H = true by decide +kernel)
  simp only [stageBCapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg]
  exact hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
