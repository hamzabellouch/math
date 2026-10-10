import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB1_4_3

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_4_3I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 1 4 3)) (shape 1 4 3) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) a
def CB1_4_3I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) a
lemma CB1_4_3I2PairRaw_sound (a : PairSlot) :
    (CB1_4_3I2PairRaw a).Encloses (CB1_4_3I2PairValue a) := by
  exact pairLawBall_sound_on (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) (fun u _ a => B1_4_3Little_sound (complement (shape 1 4 3) u) ((stageBPriority (shape 1 4 3)) 2) a) a
def CB1_4_3I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1966519024111033745643559687113 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(2500046291848775426899270047709 / 12500000000000000000000000000000), (4164266039 / 50000000000000000000000000000000)⟩ ⟨(-31782635474107897879846636975989 / 12500000000000000000000000000000), (21175823721 / 20000000000000000000000000000000)⟩ ⟨-4, 1966519024111033745643559687113, 1562500000000000000000000000000⟩,
   .log ⟨(18979543218321732038291109031929 / 25000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩ ⟨(20916526955163493478275969474021 / 100000000000000000000000000000000), (4019074611 / 12500000000000000000000000000000)⟩ ⟨(-27551409845011327169321236621291 / 100000000000000000000000000000000), (1323488981 / 3125000000000000000000000000000)⟩ ⟨-1, 18979543218321732038291109031929, 12500000000000000000000000000000⟩,
   .log ⟨(4129064322164561216004098570321 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(6579910422115434244921685085979 / 50000000000000000000000000000000), (5246180293 / 100000000000000000000000000000000)⟩ ⟨(-159355968052977115286473929248967 / 50000000000000000000000000000000), (63527471073 / 50000000000000000000000000000000)⟩ ⟨-5, 4129064322164561216004098570321, 3125000000000000000000000000000⟩,
   .log ⟨(3076084781593046714415474453 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(204493841992591654814814542237 / 100000000000000000000000000000000), (8468023 / 12500000000000000000000000000000)⟩ ⟨(-103872828871755020970832134190087 / 12500000000000000000000000000000), (137642855971 / 50000000000000000000000000000000)⟩ ⟨-12, 3076084781593046714415474453, 3051757812500000000000000000⟩,
   .log ⟨(33468805621467537981782719557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(66956953162162032020595243473 / 25000000000000000000000000000000), (1439607 / 1562500000000000000000000000000)⟩ ⟨(-800231163543099963826328472368741 / 100000000000000000000000000000000), (137642855433 / 50000000000000000000000000000000)⟩ ⟨-12, 33468805621467537981782719557, 24414062500000000000000000000⟩]
lemma CB1_4_3I2PairCertificates_valid :
    CB1_4_3I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 4 => 1
  | 2, 2 => 2
  | 2, 3 => 3
  | 3, 2 => 3
  | 3, 3 => 4
  | 4, 1 => 1
  | 5, 0 => 5
  | 0, 5 => 5
  | _, _ => 0
def CB1_4_3I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2PairCertificates (CB1_4_3I2PairCertificateIndex a)).input
lemma CB1_4_3I2PairP_check : ∀ a : PairSlot, contains (CB1_4_3I2PairRaw a) (CB1_4_3I2PairP a) = true := by
  decide +kernel
lemma CB1_4_3I2PairP_sound (a : PairSlot) :
    (CB1_4_3I2PairP a).Encloses (CB1_4_3I2PairValue a) :=
  contains_sound (CB1_4_3I2PairRaw_sound a) (CB1_4_3I2PairP_check a)
def CB1_4_3I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2PairCertificates (CB1_4_3I2PairCertificateIndex a)).output
lemma CB1_4_3I2PairTerms_sound (a : PairSlot) :
    (CB1_4_3I2PairTerms a).Encloses (Foundation.entropyTerm (CB1_4_3I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2PairCertificates_valid
    (CB1_4_3I2PairCertificateIndex a) (CB1_4_3I2PairP_sound a)
def CB1_4_3I2PairEntropy : Ball := ⟨(43988529390247762599665303535651 / 50000000000000000000000000000000), (5955403551 / 10000000000000000000000000000000)⟩
lemma CB1_4_3I2PairEntropy_sound : CB1_4_3I2PairEntropy.Encloses (Foundation.finiteEntropy CB1_4_3I2PairValue) := by
  exact contains_sound (entropyPair_enclosed CB1_4_3I2PairValue CB1_4_3I2PairTerms CB1_4_3I2PairTerms_sound) (by decide +kernel)
def CB1_4_3I2PairMass : Ball := ⟨1, (57 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I2PairMass_sound : CB1_4_3I2PairMass.Encloses (∑ a, CB1_4_3I2PairValue a) := by
  exact contains_sound (pairSumBall_sound CB1_4_3I2PairP CB1_4_3I2PairValue CB1_4_3I2PairP_sound) (by decide +kernel)
def CB1_4_3I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_4_3I2PairMassTermLog : Ball := ⟨0, (21175823739 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I2PairMassTermLog_sound : CB1_4_3I2PairMassTermLog.Encloses (Real.log ((∑ a, CB1_4_3I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_4_3I2PairMass_sound) (w := CB1_4_3I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_4_3I2PairMassTerm : Ball := ⟨0, (1058791187 / 5000000000000000000000000000000)⟩
lemma CB1_4_3I2PairMassTerm_sound : CB1_4_3I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB1_4_3I2PairMass_sound) CB1_4_3I2PairMassTermLog_sound) (by decide +kernel)
def CB1_4_3I2PairH : Ball := ⟨(43988529390247762599665303535651 / 50000000000000000000000000000000), (322919437 / 400000000000000000000000000000)⟩
lemma CB1_4_3I2PairH_sound : CB1_4_3I2PairH.Encloses (homogeneousEntropy CB1_4_3I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2PairValue CB1_4_3I2PairMassTerm_sound CB1_4_3I2PairEntropy_sound) (by decide +kernel)

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
def CB1_4_3I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 0 a
def CB1_4_3I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 0 a
lemma CB1_4_3I2R0Raw_sound (a : Fin 6) :
    (CB1_4_3I2R0Raw a).Encloses (CB1_4_3I2R0Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 0 a
def CB1_4_3I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(33468805621467537981782719557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(66956953162162032020595243473 / 25000000000000000000000000000000), (1439607 / 1562500000000000000000000000000)⟩ ⟨(-800231163543099963826328472368741 / 100000000000000000000000000000000), (137642855433 / 50000000000000000000000000000000)⟩ ⟨-12, 33468805621467537981782719557, 24414062500000000000000000000⟩]
lemma CB1_4_3I2R0Certificates_valid :
    CB1_4_3I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB1_4_3I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R0Certificates (CB1_4_3I2R0CertificateIndex a)).input
lemma CB1_4_3I2R0P_check : ∀ a : Fin 6, contains (CB1_4_3I2R0Raw a) (CB1_4_3I2R0P a) = true := by
  decide +kernel
lemma CB1_4_3I2R0P_sound (a : Fin 6) :
    (CB1_4_3I2R0P a).Encloses (CB1_4_3I2R0Value a) :=
  contains_sound (CB1_4_3I2R0Raw_sound a) (CB1_4_3I2R0P_check a)
def CB1_4_3I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R0Certificates (CB1_4_3I2R0CertificateIndex a)).output
lemma CB1_4_3I2R0Terms_sound (a : Fin 6) :
    (CB1_4_3I2R0Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R0Certificates_valid
    (CB1_4_3I2R0CertificateIndex a) (CB1_4_3I2R0P_sound a)
def CB1_4_3I2R0Entropy : Ball := ⟨(66956953162162032020595243473 / 25000000000000000000000000000000), (1439607 / 1562500000000000000000000000000)⟩
lemma CB1_4_3I2R0Entropy_sound : CB1_4_3I2R0Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R0Value CB1_4_3I2R0Terms CB1_4_3I2R0Terms_sound) (by decide +kernel)
def CB1_4_3I2R0Mass : Ball := ⟨(33468805621467537981782719557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I2R0Mass_sound : CB1_4_3I2R0Mass.Encloses (∑ a, CB1_4_3I2R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R0P CB1_4_3I2R0Value CB1_4_3I2R0P_sound) (by decide +kernel)
def CB1_4_3I2R0MassTermLogWitness : LogWitness := ⟨-12, 33468805621467537981782719557, 24414062500000000000000000000⟩
def CB1_4_3I2R0MassTermLog : Ball := ⟨(-800231163543099963826328472368741 / 100000000000000000000000000000000), (137642855433 / 50000000000000000000000000000000)⟩
lemma CB1_4_3I2R0MassTermLog_sound : CB1_4_3I2R0MassTermLog.Encloses (Real.log ((∑ a, CB1_4_3I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_4_3I2R0Mass_sound) (w := CB1_4_3I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_4_3I2R0MassTerm : Ball := ⟨(66956953162162032020595243473 / 25000000000000000000000000000000), (1439607 / 1562500000000000000000000000000)⟩
lemma CB1_4_3I2R0MassTerm_sound : CB1_4_3I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_4_3I2R0Mass_sound) CB1_4_3I2R0MassTermLog_sound) (by decide +kernel)
def CB1_4_3I2R0H : Ball := ⟨0, (1439607 / 781250000000000000000000000000)⟩
lemma CB1_4_3I2R0H_sound : CB1_4_3I2R0H.Encloses (homogeneousEntropy CB1_4_3I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R0Value CB1_4_3I2R0MassTerm_sound CB1_4_3I2R0Entropy_sound) (by decide +kernel)
def CB1_4_3I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 1 a
def CB1_4_3I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 1 a
lemma CB1_4_3I2R1Raw_sound (a : Fin 6) :
    (CB1_4_3I2R1Raw a).Encloses (CB1_4_3I2R1Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 1 a
def CB1_4_3I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5275191590850223000844657229 / 80000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(17929134143311901936334016847311 / 100000000000000000000000000000000), (6981657981 / 100000000000000000000000000000000)⟩ ⟨(-271901163543099963826328625133483 / 100000000000000000000000000000000), (105879118581 / 100000000000000000000000000000000)⟩ ⟨-4, 5275191590850223000844657229, 5000000000000000000000000000⟩]
lemma CB1_4_3I2R1Certificates_valid :
    CB1_4_3I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_4_3I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R1Certificates (CB1_4_3I2R1CertificateIndex a)).input
lemma CB1_4_3I2R1P_check : ∀ a : Fin 6, contains (CB1_4_3I2R1Raw a) (CB1_4_3I2R1P a) = true := by
  decide +kernel
lemma CB1_4_3I2R1P_sound (a : Fin 6) :
    (CB1_4_3I2R1P a).Encloses (CB1_4_3I2R1Value a) :=
  contains_sound (CB1_4_3I2R1Raw_sound a) (CB1_4_3I2R1P_check a)
def CB1_4_3I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R1Certificates (CB1_4_3I2R1CertificateIndex a)).output
lemma CB1_4_3I2R1Terms_sound (a : Fin 6) :
    (CB1_4_3I2R1Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R1Certificates_valid
    (CB1_4_3I2R1CertificateIndex a) (CB1_4_3I2R1P_sound a)
def CB1_4_3I2R1Entropy : Ball := ⟨(17929134143311901936334016847311 / 100000000000000000000000000000000), (6981657981 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I2R1Entropy_sound : CB1_4_3I2R1Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R1Value CB1_4_3I2R1Terms CB1_4_3I2R1Terms_sound) (by decide +kernel)
def CB1_4_3I2R1Mass : Ball := ⟨(5275191590850223000844657229 / 80000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I2R1Mass_sound : CB1_4_3I2R1Mass.Encloses (∑ a, CB1_4_3I2R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R1P CB1_4_3I2R1Value CB1_4_3I2R1P_sound) (by decide +kernel)
def CB1_4_3I2R1MassTermLogWitness : LogWitness := ⟨-4, 5275191590850223000844657229, 5000000000000000000000000000⟩
def CB1_4_3I2R1MassTermLog : Ball := ⟨(-271901163543099963826328625133483 / 100000000000000000000000000000000), (105879118581 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I2R1MassTermLog_sound : CB1_4_3I2R1MassTermLog.Encloses (Real.log ((∑ a, CB1_4_3I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_4_3I2R1Mass_sound) (w := CB1_4_3I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_4_3I2R1MassTerm : Ball := ⟨(17929134143311901936334016847311 / 100000000000000000000000000000000), (6981657981 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I2R1MassTerm_sound : CB1_4_3I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_4_3I2R1Mass_sound) CB1_4_3I2R1MassTermLog_sound) (by decide +kernel)
def CB1_4_3I2R1H : Ball := ⟨0, (6981657981 / 50000000000000000000000000000000)⟩
lemma CB1_4_3I2R1H_sound : CB1_4_3I2R1H.Encloses (homogeneousEntropy CB1_4_3I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R1Value CB1_4_3I2R1MassTerm_sound CB1_4_3I2R1Entropy_sound) (by decide +kernel)
def CB1_4_3I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 2 a
def CB1_4_3I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 2 a
lemma CB1_4_3I2R2Raw_sound (a : Fin 6) :
    (CB1_4_3I2R2Raw a).Encloses (CB1_4_3I2R2Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 2 a
def CB1_4_3I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(41971754006700012026349318289619 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(7287751384299208008243384830007 / 20000000000000000000000000000000), (13331796949 / 50000000000000000000000000000000)⟩ ⟨(-86817331760019532117576094675033 / 100000000000000000000000000000000), (63527471077 / 100000000000000000000000000000000)⟩ ⟨-2, 41971754006700012026349318289619, 25000000000000000000000000000000⟩,
   .log ⟨(32175272808596363273665060593 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(428280736599910395168193615563 / 50000000000000000000000000000000), (149894343 / 50000000000000000000000000000000)⟩ ⟨(-166385821787610980937163065740823 / 25000000000000000000000000000000), (232934061289 / 100000000000000000000000000000000)⟩ ⟨-10, 32175272808596363273665060593, 24414062500000000000000000000⟩]
lemma CB1_4_3I2R2Certificates_valid :
    CB1_4_3I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB1_4_3I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R2Certificates (CB1_4_3I2R2CertificateIndex a)).input
lemma CB1_4_3I2R2P_check : ∀ a : Fin 6, contains (CB1_4_3I2R2Raw a) (CB1_4_3I2R2P a) = true := by
  decide +kernel
lemma CB1_4_3I2R2P_sound (a : Fin 6) :
    (CB1_4_3I2R2P a).Encloses (CB1_4_3I2R2Value a) :=
  contains_sound (CB1_4_3I2R2Raw_sound a) (CB1_4_3I2R2P_check a)
def CB1_4_3I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R2Certificates (CB1_4_3I2R2CertificateIndex a)).output
lemma CB1_4_3I2R2Terms_sound (a : Fin 6) :
    (CB1_4_3I2R2Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R2Certificates_valid
    (CB1_4_3I2R2CertificateIndex a) (CB1_4_3I2R2P_sound a)
def CB1_4_3I2R2Entropy : Ball := ⟨(37295318394695860831553311381161 / 100000000000000000000000000000000), (3370422823 / 12500000000000000000000000000000)⟩
lemma CB1_4_3I2R2Entropy_sound : CB1_4_3I2R2Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R2Value CB1_4_3I2R2Terms CB1_4_3I2R2Terms_sound) (by decide +kernel)
def CB1_4_3I2R2Mass : Ball := ⟨(42100455097934397479443978531991 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I2R2Mass_sound : CB1_4_3I2R2Mass.Encloses (∑ a, CB1_4_3I2R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R2P CB1_4_3I2R2Value CB1_4_3I2R2P_sound) (by decide +kernel)
def CB1_4_3I2R2MassTermLogWitness : LogWitness := ⟨-2, 42100455097934397479443978531991, 25000000000000000000000000000000⟩
def CB1_4_3I2R2MassTermLog : Ball := ⟨(-86511163543099963826328663324499 / 100000000000000000000000000000000), (1588186777 / 2500000000000000000000000000000)⟩
lemma CB1_4_3I2R2MassTermLog_sound : CB1_4_3I2R2MassTermLog.Encloses (Real.log ((∑ a, CB1_4_3I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_4_3I2R2Mass_sound) (w := CB1_4_3I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_4_3I2R2MassTerm : Ball := ⟨(36421593562163392644111126100921 / 100000000000000000000000000000000), (26745354449 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I2R2MassTerm_sound : CB1_4_3I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_4_3I2R2Mass_sound) CB1_4_3I2R2MassTermLog_sound) (by decide +kernel)
def CB1_4_3I2R2H : Ball := ⟨(10921560406655852343027316003 / 1250000000000000000000000000000), (53708737033 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I2R2H_sound : CB1_4_3I2R2H.Encloses (homogeneousEntropy CB1_4_3I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R2Value CB1_4_3I2R2MassTerm_sound CB1_4_3I2R2Entropy_sound) (by decide +kernel)
def CB1_4_3I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 3 a
def CB1_4_3I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 3 a
lemma CB1_4_3I2R3Raw_sound (a : Fin 6) :
    (CB1_4_3I2R3Raw a).Encloses (CB1_4_3I2R3Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 3 a
def CB1_4_3I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R3Certificates_valid :
    CB1_4_3I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R3Certificates (CB1_4_3I2R3CertificateIndex a)).input
lemma CB1_4_3I2R3P_check : ∀ a : Fin 6, contains (CB1_4_3I2R3Raw a) (CB1_4_3I2R3P a) = true := by
  decide +kernel
lemma CB1_4_3I2R3P_sound (a : Fin 6) :
    (CB1_4_3I2R3P a).Encloses (CB1_4_3I2R3Value a) :=
  contains_sound (CB1_4_3I2R3Raw_sound a) (CB1_4_3I2R3P_check a)
def CB1_4_3I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R3Certificates (CB1_4_3I2R3CertificateIndex a)).output
lemma CB1_4_3I2R3Terms_sound (a : Fin 6) :
    (CB1_4_3I2R3Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R3Certificates_valid
    (CB1_4_3I2R3CertificateIndex a) (CB1_4_3I2R3P_sound a)
def CB1_4_3I2R3Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R3Entropy_sound : CB1_4_3I2R3Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R3Value CB1_4_3I2R3Terms CB1_4_3I2R3Terms_sound) (by decide +kernel)
def CB1_4_3I2R3Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R3Mass_sound : CB1_4_3I2R3Mass.Encloses (∑ a, CB1_4_3I2R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R3P CB1_4_3I2R3Value CB1_4_3I2R3P_sound) (by decide +kernel)
def CB1_4_3I2R3MassTerm : Ball := .exact 0
lemma CB1_4_3I2R3MassTerm_sound : CB1_4_3I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R3Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R3Mass_sound)
def CB1_4_3I2R3H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R3H_sound : CB1_4_3I2R3H.Encloses (homogeneousEntropy CB1_4_3I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R3Value CB1_4_3I2R3MassTerm_sound CB1_4_3I2R3Entropy_sound) (by decide +kernel)
def CB1_4_3I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 4 a
def CB1_4_3I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 4 a
lemma CB1_4_3I2R4Raw_sound (a : Fin 6) :
    (CB1_4_3I2R4Raw a).Encloses (CB1_4_3I2R4Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 4 a
def CB1_4_3I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R4Certificates_valid :
    CB1_4_3I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R4Certificates (CB1_4_3I2R4CertificateIndex a)).input
lemma CB1_4_3I2R4P_check : ∀ a : Fin 6, contains (CB1_4_3I2R4Raw a) (CB1_4_3I2R4P a) = true := by
  decide +kernel
lemma CB1_4_3I2R4P_sound (a : Fin 6) :
    (CB1_4_3I2R4P a).Encloses (CB1_4_3I2R4Value a) :=
  contains_sound (CB1_4_3I2R4Raw_sound a) (CB1_4_3I2R4P_check a)
def CB1_4_3I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R4Certificates (CB1_4_3I2R4CertificateIndex a)).output
lemma CB1_4_3I2R4Terms_sound (a : Fin 6) :
    (CB1_4_3I2R4Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R4Certificates_valid
    (CB1_4_3I2R4CertificateIndex a) (CB1_4_3I2R4P_sound a)
def CB1_4_3I2R4Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R4Entropy_sound : CB1_4_3I2R4Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R4Value CB1_4_3I2R4Terms CB1_4_3I2R4Terms_sound) (by decide +kernel)
def CB1_4_3I2R4Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R4Mass_sound : CB1_4_3I2R4Mass.Encloses (∑ a, CB1_4_3I2R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R4P CB1_4_3I2R4Value CB1_4_3I2R4P_sound) (by decide +kernel)
def CB1_4_3I2R4MassTerm : Ball := .exact 0
lemma CB1_4_3I2R4MassTerm_sound : CB1_4_3I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R4Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R4Mass_sound)
def CB1_4_3I2R4H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R4H_sound : CB1_4_3I2R4H.Encloses (homogeneousEntropy CB1_4_3I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R4Value CB1_4_3I2R4MassTerm_sound CB1_4_3I2R4Entropy_sound) (by decide +kernel)
def CB1_4_3I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 5 a
def CB1_4_3I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 5 a
lemma CB1_4_3I2R5Raw_sound (a : Fin 6) :
    (CB1_4_3I2R5Raw a).Encloses (CB1_4_3I2R5Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 5 a
def CB1_4_3I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R5Certificates_valid :
    CB1_4_3I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R5Certificates (CB1_4_3I2R5CertificateIndex a)).input
lemma CB1_4_3I2R5P_check : ∀ a : Fin 6, contains (CB1_4_3I2R5Raw a) (CB1_4_3I2R5P a) = true := by
  decide +kernel
lemma CB1_4_3I2R5P_sound (a : Fin 6) :
    (CB1_4_3I2R5P a).Encloses (CB1_4_3I2R5Value a) :=
  contains_sound (CB1_4_3I2R5Raw_sound a) (CB1_4_3I2R5P_check a)
def CB1_4_3I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R5Certificates (CB1_4_3I2R5CertificateIndex a)).output
lemma CB1_4_3I2R5Terms_sound (a : Fin 6) :
    (CB1_4_3I2R5Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R5Certificates_valid
    (CB1_4_3I2R5CertificateIndex a) (CB1_4_3I2R5P_sound a)
def CB1_4_3I2R5Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R5Entropy_sound : CB1_4_3I2R5Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R5Value CB1_4_3I2R5Terms CB1_4_3I2R5Terms_sound) (by decide +kernel)
def CB1_4_3I2R5Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R5Mass_sound : CB1_4_3I2R5Mass.Encloses (∑ a, CB1_4_3I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R5P CB1_4_3I2R5Value CB1_4_3I2R5P_sound) (by decide +kernel)
def CB1_4_3I2R5MassTerm : Ball := .exact 0
lemma CB1_4_3I2R5MassTerm_sound : CB1_4_3I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R5Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R5Mass_sound)
def CB1_4_3I2R5H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R5H_sound : CB1_4_3I2R5H.Encloses (homogeneousEntropy CB1_4_3I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R5Value CB1_4_3I2R5MassTerm_sound CB1_4_3I2R5Entropy_sound) (by decide +kernel)
def CB1_4_3I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 6 a
def CB1_4_3I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 6 a
lemma CB1_4_3I2R6Raw_sound (a : Fin 6) :
    (CB1_4_3I2R6Raw a).Encloses (CB1_4_3I2R6Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 6 a
def CB1_4_3I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R6Certificates_valid :
    CB1_4_3I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R6Certificates (CB1_4_3I2R6CertificateIndex a)).input
lemma CB1_4_3I2R6P_check : ∀ a : Fin 6, contains (CB1_4_3I2R6Raw a) (CB1_4_3I2R6P a) = true := by
  decide +kernel
lemma CB1_4_3I2R6P_sound (a : Fin 6) :
    (CB1_4_3I2R6P a).Encloses (CB1_4_3I2R6Value a) :=
  contains_sound (CB1_4_3I2R6Raw_sound a) (CB1_4_3I2R6P_check a)
def CB1_4_3I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R6Certificates (CB1_4_3I2R6CertificateIndex a)).output
lemma CB1_4_3I2R6Terms_sound (a : Fin 6) :
    (CB1_4_3I2R6Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R6Certificates_valid
    (CB1_4_3I2R6CertificateIndex a) (CB1_4_3I2R6P_sound a)
def CB1_4_3I2R6Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R6Entropy_sound : CB1_4_3I2R6Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R6Value CB1_4_3I2R6Terms CB1_4_3I2R6Terms_sound) (by decide +kernel)
def CB1_4_3I2R6Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R6Mass_sound : CB1_4_3I2R6Mass.Encloses (∑ a, CB1_4_3I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R6P CB1_4_3I2R6Value CB1_4_3I2R6P_sound) (by decide +kernel)
def CB1_4_3I2R6MassTerm : Ball := .exact 0
lemma CB1_4_3I2R6MassTerm_sound : CB1_4_3I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R6Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R6Mass_sound)
def CB1_4_3I2R6H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R6H_sound : CB1_4_3I2R6H.Encloses (homogeneousEntropy CB1_4_3I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R6Value CB1_4_3I2R6MassTerm_sound CB1_4_3I2R6Entropy_sound) (by decide +kernel)
def CB1_4_3I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 7 a
def CB1_4_3I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 7 a
lemma CB1_4_3I2R7Raw_sound (a : Fin 6) :
    (CB1_4_3I2R7Raw a).Encloses (CB1_4_3I2R7Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 7 a
def CB1_4_3I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R7Certificates_valid :
    CB1_4_3I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R7Certificates (CB1_4_3I2R7CertificateIndex a)).input
lemma CB1_4_3I2R7P_check : ∀ a : Fin 6, contains (CB1_4_3I2R7Raw a) (CB1_4_3I2R7P a) = true := by
  decide +kernel
lemma CB1_4_3I2R7P_sound (a : Fin 6) :
    (CB1_4_3I2R7P a).Encloses (CB1_4_3I2R7Value a) :=
  contains_sound (CB1_4_3I2R7Raw_sound a) (CB1_4_3I2R7P_check a)
def CB1_4_3I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R7Certificates (CB1_4_3I2R7CertificateIndex a)).output
lemma CB1_4_3I2R7Terms_sound (a : Fin 6) :
    (CB1_4_3I2R7Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R7Certificates_valid
    (CB1_4_3I2R7CertificateIndex a) (CB1_4_3I2R7P_sound a)
def CB1_4_3I2R7Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R7Entropy_sound : CB1_4_3I2R7Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R7Value CB1_4_3I2R7Terms CB1_4_3I2R7Terms_sound) (by decide +kernel)
def CB1_4_3I2R7Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R7Mass_sound : CB1_4_3I2R7Mass.Encloses (∑ a, CB1_4_3I2R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R7P CB1_4_3I2R7Value CB1_4_3I2R7P_sound) (by decide +kernel)
def CB1_4_3I2R7MassTerm : Ball := .exact 0
lemma CB1_4_3I2R7MassTerm_sound : CB1_4_3I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R7Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R7Mass_sound)
def CB1_4_3I2R7H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R7H_sound : CB1_4_3I2R7H.Encloses (homogeneousEntropy CB1_4_3I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R7Value CB1_4_3I2R7MassTerm_sound CB1_4_3I2R7Entropy_sound) (by decide +kernel)
def CB1_4_3I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 8 a
def CB1_4_3I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 8 a
lemma CB1_4_3I2R8Raw_sound (a : Fin 6) :
    (CB1_4_3I2R8Raw a).Encloses (CB1_4_3I2R8Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 8 a
def CB1_4_3I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R8Certificates_valid :
    CB1_4_3I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R8Certificates (CB1_4_3I2R8CertificateIndex a)).input
lemma CB1_4_3I2R8P_check : ∀ a : Fin 6, contains (CB1_4_3I2R8Raw a) (CB1_4_3I2R8P a) = true := by
  decide +kernel
lemma CB1_4_3I2R8P_sound (a : Fin 6) :
    (CB1_4_3I2R8P a).Encloses (CB1_4_3I2R8Value a) :=
  contains_sound (CB1_4_3I2R8Raw_sound a) (CB1_4_3I2R8P_check a)
def CB1_4_3I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R8Certificates (CB1_4_3I2R8CertificateIndex a)).output
lemma CB1_4_3I2R8Terms_sound (a : Fin 6) :
    (CB1_4_3I2R8Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R8Certificates_valid
    (CB1_4_3I2R8CertificateIndex a) (CB1_4_3I2R8P_sound a)
def CB1_4_3I2R8Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R8Entropy_sound : CB1_4_3I2R8Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R8Value CB1_4_3I2R8Terms CB1_4_3I2R8Terms_sound) (by decide +kernel)
def CB1_4_3I2R8Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R8Mass_sound : CB1_4_3I2R8Mass.Encloses (∑ a, CB1_4_3I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R8P CB1_4_3I2R8Value CB1_4_3I2R8P_sound) (by decide +kernel)
def CB1_4_3I2R8MassTerm : Ball := .exact 0
lemma CB1_4_3I2R8MassTerm_sound : CB1_4_3I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R8Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R8Mass_sound)
def CB1_4_3I2R8H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R8H_sound : CB1_4_3I2R8H.Encloses (homogeneousEntropy CB1_4_3I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R8Value CB1_4_3I2R8MassTerm_sound CB1_4_3I2R8Entropy_sound) (by decide +kernel)
def CB1_4_3I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 9 a
def CB1_4_3I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 9 a
lemma CB1_4_3I2R9Raw_sound (a : Fin 6) :
    (CB1_4_3I2R9Raw a).Encloses (CB1_4_3I2R9Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 9 a
def CB1_4_3I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R9Certificates_valid :
    CB1_4_3I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R9Certificates (CB1_4_3I2R9CertificateIndex a)).input
lemma CB1_4_3I2R9P_check : ∀ a : Fin 6, contains (CB1_4_3I2R9Raw a) (CB1_4_3I2R9P a) = true := by
  decide +kernel
lemma CB1_4_3I2R9P_sound (a : Fin 6) :
    (CB1_4_3I2R9P a).Encloses (CB1_4_3I2R9Value a) :=
  contains_sound (CB1_4_3I2R9Raw_sound a) (CB1_4_3I2R9P_check a)
def CB1_4_3I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R9Certificates (CB1_4_3I2R9CertificateIndex a)).output
lemma CB1_4_3I2R9Terms_sound (a : Fin 6) :
    (CB1_4_3I2R9Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R9Certificates_valid
    (CB1_4_3I2R9CertificateIndex a) (CB1_4_3I2R9P_sound a)
def CB1_4_3I2R9Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R9Entropy_sound : CB1_4_3I2R9Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R9Value CB1_4_3I2R9Terms CB1_4_3I2R9Terms_sound) (by decide +kernel)
def CB1_4_3I2R9Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R9Mass_sound : CB1_4_3I2R9Mass.Encloses (∑ a, CB1_4_3I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R9P CB1_4_3I2R9Value CB1_4_3I2R9P_sound) (by decide +kernel)
def CB1_4_3I2R9MassTerm : Ball := .exact 0
lemma CB1_4_3I2R9MassTerm_sound : CB1_4_3I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R9Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R9Mass_sound)
def CB1_4_3I2R9H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R9H_sound : CB1_4_3I2R9H.Encloses (homogeneousEntropy CB1_4_3I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R9Value CB1_4_3I2R9MassTerm_sound CB1_4_3I2R9Entropy_sound) (by decide +kernel)
def CB1_4_3I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 10 a
def CB1_4_3I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 10 a
lemma CB1_4_3I2R10Raw_sound (a : Fin 6) :
    (CB1_4_3I2R10Raw a).Encloses (CB1_4_3I2R10Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 10 a
def CB1_4_3I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R10Certificates_valid :
    CB1_4_3I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R10Certificates (CB1_4_3I2R10CertificateIndex a)).input
lemma CB1_4_3I2R10P_check : ∀ a : Fin 6, contains (CB1_4_3I2R10Raw a) (CB1_4_3I2R10P a) = true := by
  decide +kernel
lemma CB1_4_3I2R10P_sound (a : Fin 6) :
    (CB1_4_3I2R10P a).Encloses (CB1_4_3I2R10Value a) :=
  contains_sound (CB1_4_3I2R10Raw_sound a) (CB1_4_3I2R10P_check a)
def CB1_4_3I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R10Certificates (CB1_4_3I2R10CertificateIndex a)).output
lemma CB1_4_3I2R10Terms_sound (a : Fin 6) :
    (CB1_4_3I2R10Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R10Certificates_valid
    (CB1_4_3I2R10CertificateIndex a) (CB1_4_3I2R10P_sound a)
def CB1_4_3I2R10Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R10Entropy_sound : CB1_4_3I2R10Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R10Value CB1_4_3I2R10Terms CB1_4_3I2R10Terms_sound) (by decide +kernel)
def CB1_4_3I2R10Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R10Mass_sound : CB1_4_3I2R10Mass.Encloses (∑ a, CB1_4_3I2R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R10P CB1_4_3I2R10Value CB1_4_3I2R10P_sound) (by decide +kernel)
def CB1_4_3I2R10MassTerm : Ball := .exact 0
lemma CB1_4_3I2R10MassTerm_sound : CB1_4_3I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R10Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R10Mass_sound)
def CB1_4_3I2R10H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R10H_sound : CB1_4_3I2R10H.Encloses (homogeneousEntropy CB1_4_3I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R10Value CB1_4_3I2R10MassTerm_sound CB1_4_3I2R10Entropy_sound) (by decide +kernel)
def CB1_4_3I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 11 a
def CB1_4_3I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 11 a
lemma CB1_4_3I2R11Raw_sound (a : Fin 6) :
    (CB1_4_3I2R11Raw a).Encloses (CB1_4_3I2R11Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 11 a
def CB1_4_3I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R11Certificates_valid :
    CB1_4_3I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R11Certificates (CB1_4_3I2R11CertificateIndex a)).input
lemma CB1_4_3I2R11P_check : ∀ a : Fin 6, contains (CB1_4_3I2R11Raw a) (CB1_4_3I2R11P a) = true := by
  decide +kernel
lemma CB1_4_3I2R11P_sound (a : Fin 6) :
    (CB1_4_3I2R11P a).Encloses (CB1_4_3I2R11Value a) :=
  contains_sound (CB1_4_3I2R11Raw_sound a) (CB1_4_3I2R11P_check a)
def CB1_4_3I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R11Certificates (CB1_4_3I2R11CertificateIndex a)).output
lemma CB1_4_3I2R11Terms_sound (a : Fin 6) :
    (CB1_4_3I2R11Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R11Certificates_valid
    (CB1_4_3I2R11CertificateIndex a) (CB1_4_3I2R11P_sound a)
def CB1_4_3I2R11Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R11Entropy_sound : CB1_4_3I2R11Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R11Value CB1_4_3I2R11Terms CB1_4_3I2R11Terms_sound) (by decide +kernel)
def CB1_4_3I2R11Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R11Mass_sound : CB1_4_3I2R11Mass.Encloses (∑ a, CB1_4_3I2R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R11P CB1_4_3I2R11Value CB1_4_3I2R11P_sound) (by decide +kernel)
def CB1_4_3I2R11MassTerm : Ball := .exact 0
lemma CB1_4_3I2R11MassTerm_sound : CB1_4_3I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R11Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R11Mass_sound)
def CB1_4_3I2R11H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R11H_sound : CB1_4_3I2R11H.Encloses (homogeneousEntropy CB1_4_3I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R11Value CB1_4_3I2R11MassTerm_sound CB1_4_3I2R11Entropy_sound) (by decide +kernel)
def CB1_4_3I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 12 a
def CB1_4_3I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 12 a
lemma CB1_4_3I2R12Raw_sound (a : Fin 6) :
    (CB1_4_3I2R12Raw a).Encloses (CB1_4_3I2R12Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 12 a
def CB1_4_3I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R12Certificates_valid :
    CB1_4_3I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R12Certificates (CB1_4_3I2R12CertificateIndex a)).input
lemma CB1_4_3I2R12P_check : ∀ a : Fin 6, contains (CB1_4_3I2R12Raw a) (CB1_4_3I2R12P a) = true := by
  decide +kernel
lemma CB1_4_3I2R12P_sound (a : Fin 6) :
    (CB1_4_3I2R12P a).Encloses (CB1_4_3I2R12Value a) :=
  contains_sound (CB1_4_3I2R12Raw_sound a) (CB1_4_3I2R12P_check a)
def CB1_4_3I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R12Certificates (CB1_4_3I2R12CertificateIndex a)).output
lemma CB1_4_3I2R12Terms_sound (a : Fin 6) :
    (CB1_4_3I2R12Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R12Certificates_valid
    (CB1_4_3I2R12CertificateIndex a) (CB1_4_3I2R12P_sound a)
def CB1_4_3I2R12Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R12Entropy_sound : CB1_4_3I2R12Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R12Value CB1_4_3I2R12Terms CB1_4_3I2R12Terms_sound) (by decide +kernel)
def CB1_4_3I2R12Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R12Mass_sound : CB1_4_3I2R12Mass.Encloses (∑ a, CB1_4_3I2R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R12P CB1_4_3I2R12Value CB1_4_3I2R12P_sound) (by decide +kernel)
def CB1_4_3I2R12MassTerm : Ball := .exact 0
lemma CB1_4_3I2R12MassTerm_sound : CB1_4_3I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R12Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R12Mass_sound)
def CB1_4_3I2R12H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R12H_sound : CB1_4_3I2R12H.Encloses (homogeneousEntropy CB1_4_3I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R12Value CB1_4_3I2R12MassTerm_sound CB1_4_3I2R12Entropy_sound) (by decide +kernel)
def CB1_4_3I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 13 a
def CB1_4_3I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 13 a
lemma CB1_4_3I2R13Raw_sound (a : Fin 6) :
    (CB1_4_3I2R13Raw a).Encloses (CB1_4_3I2R13Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 13 a
def CB1_4_3I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R13Certificates_valid :
    CB1_4_3I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R13Certificates (CB1_4_3I2R13CertificateIndex a)).input
lemma CB1_4_3I2R13P_check : ∀ a : Fin 6, contains (CB1_4_3I2R13Raw a) (CB1_4_3I2R13P a) = true := by
  decide +kernel
lemma CB1_4_3I2R13P_sound (a : Fin 6) :
    (CB1_4_3I2R13P a).Encloses (CB1_4_3I2R13Value a) :=
  contains_sound (CB1_4_3I2R13Raw_sound a) (CB1_4_3I2R13P_check a)
def CB1_4_3I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R13Certificates (CB1_4_3I2R13CertificateIndex a)).output
lemma CB1_4_3I2R13Terms_sound (a : Fin 6) :
    (CB1_4_3I2R13Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R13Certificates_valid
    (CB1_4_3I2R13CertificateIndex a) (CB1_4_3I2R13P_sound a)
def CB1_4_3I2R13Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R13Entropy_sound : CB1_4_3I2R13Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R13Value CB1_4_3I2R13Terms CB1_4_3I2R13Terms_sound) (by decide +kernel)
def CB1_4_3I2R13Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R13Mass_sound : CB1_4_3I2R13Mass.Encloses (∑ a, CB1_4_3I2R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R13P CB1_4_3I2R13Value CB1_4_3I2R13P_sound) (by decide +kernel)
def CB1_4_3I2R13MassTerm : Ball := .exact 0
lemma CB1_4_3I2R13MassTerm_sound : CB1_4_3I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R13Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R13Mass_sound)
def CB1_4_3I2R13H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R13H_sound : CB1_4_3I2R13H.Encloses (homogeneousEntropy CB1_4_3I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R13Value CB1_4_3I2R13MassTerm_sound CB1_4_3I2R13Entropy_sound) (by decide +kernel)
def CB1_4_3I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 14 a
def CB1_4_3I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 14 a
lemma CB1_4_3I2R14Raw_sound (a : Fin 6) :
    (CB1_4_3I2R14Raw a).Encloses (CB1_4_3I2R14Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 14 a
def CB1_4_3I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R14Certificates_valid :
    CB1_4_3I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R14Certificates (CB1_4_3I2R14CertificateIndex a)).input
lemma CB1_4_3I2R14P_check : ∀ a : Fin 6, contains (CB1_4_3I2R14Raw a) (CB1_4_3I2R14P a) = true := by
  decide +kernel
lemma CB1_4_3I2R14P_sound (a : Fin 6) :
    (CB1_4_3I2R14P a).Encloses (CB1_4_3I2R14Value a) :=
  contains_sound (CB1_4_3I2R14Raw_sound a) (CB1_4_3I2R14P_check a)
def CB1_4_3I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R14Certificates (CB1_4_3I2R14CertificateIndex a)).output
lemma CB1_4_3I2R14Terms_sound (a : Fin 6) :
    (CB1_4_3I2R14Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R14Certificates_valid
    (CB1_4_3I2R14CertificateIndex a) (CB1_4_3I2R14P_sound a)
def CB1_4_3I2R14Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R14Entropy_sound : CB1_4_3I2R14Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R14Value CB1_4_3I2R14Terms CB1_4_3I2R14Terms_sound) (by decide +kernel)
def CB1_4_3I2R14Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R14Mass_sound : CB1_4_3I2R14Mass.Encloses (∑ a, CB1_4_3I2R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R14P CB1_4_3I2R14Value CB1_4_3I2R14P_sound) (by decide +kernel)
def CB1_4_3I2R14MassTerm : Ball := .exact 0
lemma CB1_4_3I2R14MassTerm_sound : CB1_4_3I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R14Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R14Mass_sound)
def CB1_4_3I2R14H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R14H_sound : CB1_4_3I2R14H.Encloses (homogeneousEntropy CB1_4_3I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R14Value CB1_4_3I2R14MassTerm_sound CB1_4_3I2R14Entropy_sound) (by decide +kernel)
def CB1_4_3I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 15 a
def CB1_4_3I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 15 a
lemma CB1_4_3I2R15Raw_sound (a : Fin 6) :
    (CB1_4_3I2R15Raw a).Encloses (CB1_4_3I2R15Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 15 a
def CB1_4_3I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R15Certificates_valid :
    CB1_4_3I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R15Certificates (CB1_4_3I2R15CertificateIndex a)).input
lemma CB1_4_3I2R15P_check : ∀ a : Fin 6, contains (CB1_4_3I2R15Raw a) (CB1_4_3I2R15P a) = true := by
  decide +kernel
lemma CB1_4_3I2R15P_sound (a : Fin 6) :
    (CB1_4_3I2R15P a).Encloses (CB1_4_3I2R15Value a) :=
  contains_sound (CB1_4_3I2R15Raw_sound a) (CB1_4_3I2R15P_check a)
def CB1_4_3I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R15Certificates (CB1_4_3I2R15CertificateIndex a)).output
lemma CB1_4_3I2R15Terms_sound (a : Fin 6) :
    (CB1_4_3I2R15Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R15Certificates_valid
    (CB1_4_3I2R15CertificateIndex a) (CB1_4_3I2R15P_sound a)
def CB1_4_3I2R15Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R15Entropy_sound : CB1_4_3I2R15Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R15Value CB1_4_3I2R15Terms CB1_4_3I2R15Terms_sound) (by decide +kernel)
def CB1_4_3I2R15Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R15Mass_sound : CB1_4_3I2R15Mass.Encloses (∑ a, CB1_4_3I2R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R15P CB1_4_3I2R15Value CB1_4_3I2R15P_sound) (by decide +kernel)
def CB1_4_3I2R15MassTerm : Ball := .exact 0
lemma CB1_4_3I2R15MassTerm_sound : CB1_4_3I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R15Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R15Mass_sound)
def CB1_4_3I2R15H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R15H_sound : CB1_4_3I2R15H.Encloses (homogeneousEntropy CB1_4_3I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R15Value CB1_4_3I2R15MassTerm_sound CB1_4_3I2R15Entropy_sound) (by decide +kernel)
def CB1_4_3I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) 16 a
def CB1_4_3I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 1 4 3)) B1_4_3Law (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) 16 a
lemma CB1_4_3I2R16Raw_sound (a : Fin 6) :
    (CB1_4_3I2R16Raw a).Encloses (CB1_4_3I2R16Value a) := by
  exact residualBall_sound_on (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u => B1_4_3Little u ((stageBPriority (shape 1 4 3)) 2)) (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) (fun u _ a => B1_4_3Little_sound u ((stageBPriority (shape 1 4 3)) 2) a) 16 a
def CB1_4_3I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_4_3I2R16Certificates_valid :
    CB1_4_3I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R16Certificates (CB1_4_3I2R16CertificateIndex a)).input
lemma CB1_4_3I2R16P_check : ∀ a : Fin 6, contains (CB1_4_3I2R16Raw a) (CB1_4_3I2R16P a) = true := by
  decide +kernel
lemma CB1_4_3I2R16P_sound (a : Fin 6) :
    (CB1_4_3I2R16P a).Encloses (CB1_4_3I2R16Value a) :=
  contains_sound (CB1_4_3I2R16Raw_sound a) (CB1_4_3I2R16P_check a)
def CB1_4_3I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I2R16Certificates (CB1_4_3I2R16CertificateIndex a)).output
lemma CB1_4_3I2R16Terms_sound (a : Fin 6) :
    (CB1_4_3I2R16Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I2R16Certificates_valid
    (CB1_4_3I2R16CertificateIndex a) (CB1_4_3I2R16P_sound a)
def CB1_4_3I2R16Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R16Entropy_sound : CB1_4_3I2R16Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2R16Value CB1_4_3I2R16Terms CB1_4_3I2R16Terms_sound) (by decide +kernel)
def CB1_4_3I2R16Mass : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R16Mass_sound : CB1_4_3I2R16Mass.Encloses (∑ a, CB1_4_3I2R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_4_3I2R16P CB1_4_3I2R16Value CB1_4_3I2R16P_sound) (by decide +kernel)
def CB1_4_3I2R16MassTerm : Ball := .exact 0
lemma CB1_4_3I2R16MassTerm_sound : CB1_4_3I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2R16Value a))) :=
  entropyTerm_zero_ball (CB1_4_3I2R16Mass_sound)
def CB1_4_3I2R16H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2R16H_sound : CB1_4_3I2R16H.Encloses (homogeneousEntropy CB1_4_3I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2R16Value CB1_4_3I2R16MassTerm_sound CB1_4_3I2R16Entropy_sound) (by decide +kernel)
def CB1_4_3I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_4_3I2R0H
  | 1 => CB1_4_3I2R1H
  | 2 => CB1_4_3I2R2H
  | 3 => CB1_4_3I2R3H
  | 4 => CB1_4_3I2R4H
  | 5 => CB1_4_3I2R5H
  | 6 => CB1_4_3I2R6H
  | 7 => CB1_4_3I2R7H
  | 8 => CB1_4_3I2R8H
  | 9 => CB1_4_3I2R9H
  | 10 => CB1_4_3I2R10H
  | 11 => CB1_4_3I2R11H
  | 12 => CB1_4_3I2R12H
  | 13 => CB1_4_3I2R13H
  | 14 => CB1_4_3I2R14H
  | 15 => CB1_4_3I2R15H
  | 16 => CB1_4_3I2R16H
  | _ => (.exact 0)
lemma CB1_4_3I2ResidualEntropies_sound (k : Fin 17) :
    (CB1_4_3I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB1_4_3I2R0H_sound
  · exact CB1_4_3I2R1H_sound
  · exact CB1_4_3I2R2H_sound
  · exact CB1_4_3I2R3H_sound
  · exact CB1_4_3I2R4H_sound
  · exact CB1_4_3I2R5H_sound
  · exact CB1_4_3I2R6H_sound
  · exact CB1_4_3I2R7H_sound
  · exact CB1_4_3I2R8H_sound
  · exact CB1_4_3I2R9H_sound
  · exact CB1_4_3I2R10H_sound
  · exact CB1_4_3I2R11H_sound
  · exact CB1_4_3I2R12H_sound
  · exact CB1_4_3I2R13H_sound
  · exact CB1_4_3I2R14H_sound
  · exact CB1_4_3I2R15H_sound
  · exact CB1_4_3I2R16H_sound
def CB1_4_3I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 4 3) (shape 0 1 3) ((stageBPriority (shape 1 4 3)) 2) a : ℝ)
def CB1_4_3I2S0_1_3E_1Log : Ball := .exact 0
lemma CB1_4_3I2S0_1_3E_1Log_sound : CB1_4_3I2S0_1_3E_1Log.Encloses (Real.log (CB1_4_3I2S0_1_3Value (1 : Fin 6))) := by
  exact log_exact_one_ball ((B1_4_3Little_sound (shape 0 1 3) ((stageBPriority (shape 1 4 3)) 2)) (1 : Fin 6))
def CB1_4_3I2S0_1_3E_1 : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_1_3E_1_sound : CB1_4_3I2S0_1_3E_1.Encloses (Foundation.entropyTerm (CB1_4_3I2S0_1_3Value (1 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_4_3Little_sound (shape 0 1 3) ((stageBPriority (shape 1 4 3)) 2)) (1 : Fin 6)) CB1_4_3I2S0_1_3E_1Log_sound) (by decide +kernel)
def CB1_4_3I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB1_4_3I2S0_1_3Terms_sound (a : Fin 6) :
    (CB1_4_3I2S0_1_3Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2S0_1_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 1 3) ((stageBPriority (shape 1 4 3)) 2)) (0 : Fin 6)))
  · exact CB1_4_3I2S0_1_3E_1_sound
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 1 3) ((stageBPriority (shape 1 4 3)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 1 3) ((stageBPriority (shape 1 4 3)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 1 3) ((stageBPriority (shape 1 4 3)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 1 3) ((stageBPriority (shape 1 4 3)) 2)) (5 : Fin 6)))
def CB1_4_3I2S0_1_3Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_1_3Entropy_sound : CB1_4_3I2S0_1_3Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2S0_1_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2S0_1_3Value CB1_4_3I2S0_1_3Terms CB1_4_3I2S0_1_3Terms_sound) (by decide +kernel)
def CB1_4_3I2S0_1_3Mass : Ball := ⟨1, 0⟩
lemma CB1_4_3I2S0_1_3Mass_sound : CB1_4_3I2S0_1_3Mass.Encloses (∑ a, CB1_4_3I2S0_1_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_4_3Little (shape 0 1 3) ((stageBPriority (shape 1 4 3)) 2)) CB1_4_3I2S0_1_3Value (B1_4_3Little_sound (shape 0 1 3) ((stageBPriority (shape 1 4 3)) 2))) (by decide +kernel)
def CB1_4_3I2S0_1_3MassTermLog : Ball := .exact 0
lemma CB1_4_3I2S0_1_3MassTermLog_sound : CB1_4_3I2S0_1_3MassTermLog.Encloses (Real.log ((∑ a, CB1_4_3I2S0_1_3Value a))) := by
  exact log_exact_one_ball (CB1_4_3I2S0_1_3Mass_sound)
def CB1_4_3I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_1_3MassTerm_sound : CB1_4_3I2S0_1_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2S0_1_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_4_3I2S0_1_3Mass_sound) CB1_4_3I2S0_1_3MassTermLog_sound) (by decide +kernel)
def CB1_4_3I2S0_1_3H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_1_3H_sound : CB1_4_3I2S0_1_3H.Encloses (homogeneousEntropy CB1_4_3I2S0_1_3Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2S0_1_3Value CB1_4_3I2S0_1_3MassTerm_sound CB1_4_3I2S0_1_3Entropy_sound) (by decide +kernel)
def CB1_4_3I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 1 4 3) (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2) a : ℝ)
def CB1_4_3I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 226099, 125000⟩
def CB1_4_3I2S0_2_2E_2Log : Ball := ⟨(-2512199035246581498367078978841 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma CB1_4_3I2S0_2_2E_2Log_sound : CB1_4_3I2S0_2_2E_2Log.Encloses (Real.log (CB1_4_3I2S0_2_2Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B1_4_3Little_sound (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2)) (2 : Fin 6)) (w := CB1_4_3I2S0_2_2E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_4_3I2S0_2_2E_2 : Ball := ⟨(568005689670216830199298190037 / 6250000000000000000000000000000), (4787832559 / 12500000000000000000000000000000)⟩
lemma CB1_4_3I2S0_2_2E_2_sound : CB1_4_3I2S0_2_2E_2.Encloses (Foundation.entropyTerm (CB1_4_3I2S0_2_2Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_4_3Little_sound (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2)) (2 : Fin 6)) CB1_4_3I2S0_2_2E_2Log_sound) (by decide +kernel)
def CB1_4_3I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 23901, 15625⟩
def CB1_4_3I2S0_2_2E_3Log : Ball := ⟨(-234754061879590774959727984514419 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma CB1_4_3I2S0_2_2E_3Log_sound : CB1_4_3I2S0_2_2E_3Log.Encloses (Real.log (CB1_4_3I2S0_2_2Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B1_4_3Little_sound (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2)) (3 : Fin 6)) (w := CB1_4_3I2S0_2_2E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_4_3I2S0_2_2E_3 : Ball := ⟨(22443427331936396449249834231517 / 100000000000000000000000000000000), (5061233619 / 50000000000000000000000000000000)⟩
lemma CB1_4_3I2S0_2_2E_3_sound : CB1_4_3I2S0_2_2E_3.Encloses (Foundation.entropyTerm (CB1_4_3I2S0_2_2Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_4_3Little_sound (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2)) (3 : Fin 6)) CB1_4_3I2S0_2_2E_3Log_sound) (by decide +kernel)
def CB1_4_3I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(568005689670216830199298190037 / 6250000000000000000000000000000), (4787832559 / 12500000000000000000000000000000)⟩
  | 3 => ⟨(22443427331936396449249834231517 / 100000000000000000000000000000000), (5061233619 / 50000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB1_4_3I2S0_2_2Terms_sound (a : Fin 6) :
    (CB1_4_3I2S0_2_2Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2S0_2_2Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2)) (1 : Fin 6)))
  · exact CB1_4_3I2S0_2_2E_2_sound
  · exact CB1_4_3I2S0_2_2E_3_sound
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2)) (5 : Fin 6)))
def CB1_4_3I2S0_2_2Entropy : Ball := ⟨(31531518366659865732438605272109 / 100000000000000000000000000000000), (4842512771 / 10000000000000000000000000000000)⟩
lemma CB1_4_3I2S0_2_2Entropy_sound : CB1_4_3I2S0_2_2Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2S0_2_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2S0_2_2Value CB1_4_3I2S0_2_2Terms CB1_4_3I2S0_2_2Terms_sound) (by decide +kernel)
def CB1_4_3I2S0_2_2Mass : Ball := ⟨1, 0⟩
lemma CB1_4_3I2S0_2_2Mass_sound : CB1_4_3I2S0_2_2Mass.Encloses (∑ a, CB1_4_3I2S0_2_2Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_4_3Little (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2)) CB1_4_3I2S0_2_2Value (B1_4_3Little_sound (shape 0 2 2) ((stageBPriority (shape 1 4 3)) 2))) (by decide +kernel)
def CB1_4_3I2S0_2_2MassTermLog : Ball := .exact 0
lemma CB1_4_3I2S0_2_2MassTermLog_sound : CB1_4_3I2S0_2_2MassTermLog.Encloses (Real.log ((∑ a, CB1_4_3I2S0_2_2Value a))) := by
  exact log_exact_one_ball (CB1_4_3I2S0_2_2Mass_sound)
def CB1_4_3I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_2_2MassTerm_sound : CB1_4_3I2S0_2_2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2S0_2_2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_4_3I2S0_2_2Mass_sound) CB1_4_3I2S0_2_2MassTermLog_sound) (by decide +kernel)
def CB1_4_3I2S0_2_2H : Ball := ⟨(31531518366659865732438605272109 / 100000000000000000000000000000000), (4842512771 / 10000000000000000000000000000000)⟩
lemma CB1_4_3I2S0_2_2H_sound : CB1_4_3I2S0_2_2H.Encloses (homogeneousEntropy CB1_4_3I2S0_2_2Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2S0_2_2Value CB1_4_3I2S0_2_2MassTerm_sound CB1_4_3I2S0_2_2Entropy_sound) (by decide +kernel)
def CB1_4_3I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 1 4 3) (shape 0 3 1) ((stageBPriority (shape 1 4 3)) 2) a : ℝ)
def CB1_4_3I2S0_3_1E_4Log : Ball := .exact 0
lemma CB1_4_3I2S0_3_1E_4Log_sound : CB1_4_3I2S0_3_1E_4Log.Encloses (Real.log (CB1_4_3I2S0_3_1Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B1_4_3Little_sound (shape 0 3 1) ((stageBPriority (shape 1 4 3)) 2)) (4 : Fin 6))
def CB1_4_3I2S0_3_1E_4 : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_3_1E_4_sound : CB1_4_3I2S0_3_1E_4.Encloses (Foundation.entropyTerm (CB1_4_3I2S0_3_1Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_4_3Little_sound (shape 0 3 1) ((stageBPriority (shape 1 4 3)) 2)) (4 : Fin 6)) CB1_4_3I2S0_3_1E_4Log_sound) (by decide +kernel)
def CB1_4_3I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB1_4_3I2S0_3_1Terms_sound (a : Fin 6) :
    (CB1_4_3I2S0_3_1Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2S0_3_1Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 3 1) ((stageBPriority (shape 1 4 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 3 1) ((stageBPriority (shape 1 4 3)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 3 1) ((stageBPriority (shape 1 4 3)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 3 1) ((stageBPriority (shape 1 4 3)) 2)) (3 : Fin 6)))
  · exact CB1_4_3I2S0_3_1E_4_sound
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 3 1) ((stageBPriority (shape 1 4 3)) 2)) (5 : Fin 6)))
def CB1_4_3I2S0_3_1Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_3_1Entropy_sound : CB1_4_3I2S0_3_1Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2S0_3_1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2S0_3_1Value CB1_4_3I2S0_3_1Terms CB1_4_3I2S0_3_1Terms_sound) (by decide +kernel)
def CB1_4_3I2S0_3_1Mass : Ball := ⟨1, 0⟩
lemma CB1_4_3I2S0_3_1Mass_sound : CB1_4_3I2S0_3_1Mass.Encloses (∑ a, CB1_4_3I2S0_3_1Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_4_3Little (shape 0 3 1) ((stageBPriority (shape 1 4 3)) 2)) CB1_4_3I2S0_3_1Value (B1_4_3Little_sound (shape 0 3 1) ((stageBPriority (shape 1 4 3)) 2))) (by decide +kernel)
def CB1_4_3I2S0_3_1MassTermLog : Ball := .exact 0
lemma CB1_4_3I2S0_3_1MassTermLog_sound : CB1_4_3I2S0_3_1MassTermLog.Encloses (Real.log ((∑ a, CB1_4_3I2S0_3_1Value a))) := by
  exact log_exact_one_ball (CB1_4_3I2S0_3_1Mass_sound)
def CB1_4_3I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_3_1MassTerm_sound : CB1_4_3I2S0_3_1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2S0_3_1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_4_3I2S0_3_1Mass_sound) CB1_4_3I2S0_3_1MassTermLog_sound) (by decide +kernel)
def CB1_4_3I2S0_3_1H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_3_1H_sound : CB1_4_3I2S0_3_1H.Encloses (homogeneousEntropy CB1_4_3I2S0_3_1Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2S0_3_1Value CB1_4_3I2S0_3_1MassTerm_sound CB1_4_3I2S0_3_1Entropy_sound) (by decide +kernel)
def CB1_4_3I2S0_4_0Value (a : Fin 6) : ℝ := (littleLaw (shape 1 4 3) (shape 0 4 0) ((stageBPriority (shape 1 4 3)) 2) a : ℝ)
def CB1_4_3I2S0_4_0E_5Log : Ball := .exact 0
lemma CB1_4_3I2S0_4_0E_5Log_sound : CB1_4_3I2S0_4_0E_5Log.Encloses (Real.log (CB1_4_3I2S0_4_0Value (5 : Fin 6))) := by
  exact log_exact_one_ball ((B1_4_3Little_sound (shape 0 4 0) ((stageBPriority (shape 1 4 3)) 2)) (5 : Fin 6))
def CB1_4_3I2S0_4_0E_5 : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_4_0E_5_sound : CB1_4_3I2S0_4_0E_5.Encloses (Foundation.entropyTerm (CB1_4_3I2S0_4_0Value (5 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_4_3Little_sound (shape 0 4 0) ((stageBPriority (shape 1 4 3)) 2)) (5 : Fin 6)) CB1_4_3I2S0_4_0E_5Log_sound) (by decide +kernel)
def CB1_4_3I2S0_4_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB1_4_3I2S0_4_0Terms_sound (a : Fin 6) :
    (CB1_4_3I2S0_4_0Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2S0_4_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 4 0) ((stageBPriority (shape 1 4 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 4 0) ((stageBPriority (shape 1 4 3)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 4 0) ((stageBPriority (shape 1 4 3)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 4 0) ((stageBPriority (shape 1 4 3)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 0 4 0) ((stageBPriority (shape 1 4 3)) 2)) (4 : Fin 6)))
  · exact CB1_4_3I2S0_4_0E_5_sound
def CB1_4_3I2S0_4_0Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_4_0Entropy_sound : CB1_4_3I2S0_4_0Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2S0_4_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2S0_4_0Value CB1_4_3I2S0_4_0Terms CB1_4_3I2S0_4_0Terms_sound) (by decide +kernel)
def CB1_4_3I2S0_4_0Mass : Ball := ⟨1, 0⟩
lemma CB1_4_3I2S0_4_0Mass_sound : CB1_4_3I2S0_4_0Mass.Encloses (∑ a, CB1_4_3I2S0_4_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_4_3Little (shape 0 4 0) ((stageBPriority (shape 1 4 3)) 2)) CB1_4_3I2S0_4_0Value (B1_4_3Little_sound (shape 0 4 0) ((stageBPriority (shape 1 4 3)) 2))) (by decide +kernel)
def CB1_4_3I2S0_4_0MassTermLog : Ball := .exact 0
lemma CB1_4_3I2S0_4_0MassTermLog_sound : CB1_4_3I2S0_4_0MassTermLog.Encloses (Real.log ((∑ a, CB1_4_3I2S0_4_0Value a))) := by
  exact log_exact_one_ball (CB1_4_3I2S0_4_0Mass_sound)
def CB1_4_3I2S0_4_0MassTerm : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_4_0MassTerm_sound : CB1_4_3I2S0_4_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2S0_4_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_4_3I2S0_4_0Mass_sound) CB1_4_3I2S0_4_0MassTermLog_sound) (by decide +kernel)
def CB1_4_3I2S0_4_0H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S0_4_0H_sound : CB1_4_3I2S0_4_0H.Encloses (homogeneousEntropy CB1_4_3I2S0_4_0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2S0_4_0Value CB1_4_3I2S0_4_0MassTerm_sound CB1_4_3I2S0_4_0Entropy_sound) (by decide +kernel)
def CB1_4_3I2S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 1 4 3) (shape 1 3 0) ((stageBPriority (shape 1 4 3)) 2) a : ℝ)
def CB1_4_3I2S1_3_0E_4Log : Ball := .exact 0
lemma CB1_4_3I2S1_3_0E_4Log_sound : CB1_4_3I2S1_3_0E_4Log.Encloses (Real.log (CB1_4_3I2S1_3_0Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B1_4_3Little_sound (shape 1 3 0) ((stageBPriority (shape 1 4 3)) 2)) (4 : Fin 6))
def CB1_4_3I2S1_3_0E_4 : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S1_3_0E_4_sound : CB1_4_3I2S1_3_0E_4.Encloses (Foundation.entropyTerm (CB1_4_3I2S1_3_0Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_4_3Little_sound (shape 1 3 0) ((stageBPriority (shape 1 4 3)) 2)) (4 : Fin 6)) CB1_4_3I2S1_3_0E_4Log_sound) (by decide +kernel)
def CB1_4_3I2S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB1_4_3I2S1_3_0Terms_sound (a : Fin 6) :
    (CB1_4_3I2S1_3_0Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I2S1_3_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 1 3 0) ((stageBPriority (shape 1 4 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 1 3 0) ((stageBPriority (shape 1 4 3)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 1 3 0) ((stageBPriority (shape 1 4 3)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 1 3 0) ((stageBPriority (shape 1 4 3)) 2)) (3 : Fin 6)))
  · exact CB1_4_3I2S1_3_0E_4_sound
  · exact (entropyTerm_zero_ball ((B1_4_3Little_sound (shape 1 3 0) ((stageBPriority (shape 1 4 3)) 2)) (5 : Fin 6)))
def CB1_4_3I2S1_3_0Entropy : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S1_3_0Entropy_sound : CB1_4_3I2S1_3_0Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I2S1_3_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_4_3I2S1_3_0Value CB1_4_3I2S1_3_0Terms CB1_4_3I2S1_3_0Terms_sound) (by decide +kernel)
def CB1_4_3I2S1_3_0Mass : Ball := ⟨1, 0⟩
lemma CB1_4_3I2S1_3_0Mass_sound : CB1_4_3I2S1_3_0Mass.Encloses (∑ a, CB1_4_3I2S1_3_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_4_3Little (shape 1 3 0) ((stageBPriority (shape 1 4 3)) 2)) CB1_4_3I2S1_3_0Value (B1_4_3Little_sound (shape 1 3 0) ((stageBPriority (shape 1 4 3)) 2))) (by decide +kernel)
def CB1_4_3I2S1_3_0MassTermLog : Ball := .exact 0
lemma CB1_4_3I2S1_3_0MassTermLog_sound : CB1_4_3I2S1_3_0MassTermLog.Encloses (Real.log ((∑ a, CB1_4_3I2S1_3_0Value a))) := by
  exact log_exact_one_ball (CB1_4_3I2S1_3_0Mass_sound)
def CB1_4_3I2S1_3_0MassTerm : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S1_3_0MassTerm_sound : CB1_4_3I2S1_3_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I2S1_3_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_4_3I2S1_3_0Mass_sound) CB1_4_3I2S1_3_0MassTermLog_sound) (by decide +kernel)
def CB1_4_3I2S1_3_0H : Ball := ⟨0, 0⟩
lemma CB1_4_3I2S1_3_0H_sound : CB1_4_3I2S1_3_0H.Encloses (homogeneousEntropy CB1_4_3I2S1_3_0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I2S1_3_0Value CB1_4_3I2S1_3_0MassTerm_sound CB1_4_3I2S1_3_0Entropy_sound) (by decide +kernel)
def CB1_4_3I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => CB1_4_3I2S0_1_3H
  | 0, 2, 2 => CB1_4_3I2S0_2_2H
  | 0, 3, 1 => CB1_4_3I2S0_3_1H
  | 0, 4, 0 => CB1_4_3I2S0_4_0H
  | 1, 3, 0 => CB1_4_3I2S1_3_0H
  | _, _, _ => (.exact 0)
lemma CB1_4_3I2Singles_sound (u : Shape) (hu : u ∈ below (shape 1 4 3))
    (hd : designated (stageBPriority (shape 1 4 3)) 2 u) :
    (CB1_4_3I2Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) u)) := by
  rw [B1_4_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CB1_4_3I2S0_1_3H_sound
  · exact CB1_4_3I2S0_2_2H_sound
  · exact CB1_4_3I2S0_3_1H_sound
  · exact CB1_4_3I2S0_4_0H_sound
  · exact (show ¬ designated (stageBPriority (shape 1 4 3)) 2 (shape 1 0 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 4 3)) 2 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 4 3)) 2 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact CB1_4_3I2S1_3_0H_sound
def CB1_4_3I2Singleton : Ball := ⟨(2654982546330514860850858021989 / 20000000000000000000000000000000), (1274199947 / 6250000000000000000000000000000)⟩
lemma CB1_4_3I2Singleton_sound : CB1_4_3I2Singleton.Encloses
    (singletonEntropy (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2
    CB1_4_3I2Singles (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ)) (fun u _ => B1_4_3Law_sound u) CB1_4_3I2Singles_sound) (by decide +kernel)
def CB1_4_3I2Group : Ball := ⟨(2829727512837008498339295078037 / 20000000000000000000000000000000), (88243521843 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I2Group_sound : CB1_4_3I2Group.Encloses
    (groupedEntropy (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (stageBPriority (shape 1 4 3)) 2 (fun u a => (littleLaw (shape 1 4 3) u ((stageBPriority (shape 1 4 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB1_4_3I2Singleton_sound
    (finSumBall_sound 17 CB1_4_3I2ResidualEntropies _ CB1_4_3I2ResidualEntropies_sound)) (by decide +kernel)

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
def CB1_4_3I2H : Ball := ⟨(14919945913031360053984414072733 / 25000000000000000000000000000000), (32152112867 / 12500000000000000000000000000000)⟩
lemma CB1_4_3I2_sound : CB1_4_3I2H.Encloses (stageBCapacity (shape 1 4 3) 2) := by
  have hb := contains_sound (Ball.add_sound CB1_4_3I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB1_4_3I2Group_sound)))
    (show contains (.add CB1_4_3I2PairH (.neg (.mul (.exact 2) CB1_4_3I2Group))) CB1_4_3I2H = true by decide +kernel)
  unfold CB1_4_3I2PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
