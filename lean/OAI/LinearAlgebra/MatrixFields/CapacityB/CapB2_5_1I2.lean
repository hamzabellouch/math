import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB2_5_1

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_5_1I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 2 5 1)) (shape 2 5 1) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) a
def CB2_5_1I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 2 5 1)) (shape 2 5 1) B2_5_1Law (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) a
lemma CB2_5_1I2PairRaw_sound (a : PairSlot) :
    (CB2_5_1I2PairRaw a).Encloses (CB2_5_1I2PairValue a) := by
  exact pairLawBall_sound_on (below (shape 2 5 1)) (shape 2 5 1) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) (fun u _ a => B2_5_1Little_sound (complement (shape 2 5 1) u) ((stageBPriority (shape 2 5 1)) 2) a) a
def CB2_5_1I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(9444123177522509382296864374047 / 20000000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩ ⟨(35431498578772633316469708350821 / 100000000000000000000000000000000), (7499515789 / 25000000000000000000000000000000)⟩ ⟨(-9379245143451059385188151570411 / 12500000000000000000000000000000), (63527471131 / 100000000000000000000000000000000)⟩ ⟨-2, 9444123177522509382296864374047, 5000000000000000000000000000000⟩,
   .log ⟨(2070184148321972828859570473807 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(8027206568925652293474225385487 / 100000000000000000000000000000000), (767162459 / 25000000000000000000000000000000)⟩ ⟨(-387753262212555215939813748030947 / 100000000000000000000000000000000), (74115382987 / 50000000000000000000000000000000)⟩ ⟨-6, 2070184148321972828859570473807, 1562500000000000000000000000000⟩,
   .log ⟨(354599982032740129828053827979 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(877420057559102802694039590203 / 25000000000000000000000000000000), (168951303 / 12500000000000000000000000000000)⟩ ⟨(-494878794143926844783046347417239 / 100000000000000000000000000000000), (19058241357 / 10000000000000000000000000000000)⟩ ⟨-8, 354599982032740129828053827979, 195312500000000000000000000000⟩]
lemma CB2_5_1I2PairCertificates_valid :
    CB2_5_1I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 2 => 1
  | 4, 3 => 2
  | 5, 1 => 3
  | 2, 4 => 1
  | 3, 4 => 2
  | 1, 5 => 3
  | _, _ => 0
def CB2_5_1I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2PairCertificates (CB2_5_1I2PairCertificateIndex a)).input
lemma CB2_5_1I2PairP_check : ∀ a : PairSlot, contains (CB2_5_1I2PairRaw a) (CB2_5_1I2PairP a) = true := by
  decide +kernel
lemma CB2_5_1I2PairP_sound (a : PairSlot) :
    (CB2_5_1I2PairP a).Encloses (CB2_5_1I2PairValue a) :=
  contains_sound (CB2_5_1I2PairRaw_sound a) (CB2_5_1I2PairP_check a)
def CB2_5_1I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2PairCertificates (CB2_5_1I2PairCertificateIndex a)).output
lemma CB2_5_1I2PairTerms_sound (a : PairSlot) :
    (CB2_5_1I2PairTerms a).Encloses (Foundation.entropyTerm (CB2_5_1I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2PairCertificates_valid
    (CB2_5_1I2PairCertificateIndex a) (CB2_5_1I2PairP_sound a)
def CB2_5_1I2PairEntropy : Ball := ⟨(293552408612091855129500575607 / 312500000000000000000000000000), (4302290427 / 6250000000000000000000000000000)⟩
lemma CB2_5_1I2PairEntropy_sound : CB2_5_1I2PairEntropy.Encloses (Foundation.finiteEntropy CB2_5_1I2PairValue) := by
  exact contains_sound (entropyPair_enclosed CB2_5_1I2PairValue CB2_5_1I2PairTerms CB2_5_1I2PairTerms_sound) (by decide +kernel)
def CB2_5_1I2PairMass : Ball := ⟨1, (23 / 25000000000000000000000000000000)⟩
lemma CB2_5_1I2PairMass_sound : CB2_5_1I2PairMass.Encloses (∑ a, CB2_5_1I2PairValue a) := by
  exact contains_sound (pairSumBall_sound CB2_5_1I2PairP CB2_5_1I2PairValue CB2_5_1I2PairP_sound) (by decide +kernel)
def CB2_5_1I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_5_1I2PairMassTermLog : Ball := ⟨0, (10587911887 / 50000000000000000000000000000000)⟩
lemma CB2_5_1I2PairMassTermLog_sound : CB2_5_1I2PairMassTermLog.Encloses (Real.log ((∑ a, CB2_5_1I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_5_1I2PairMass_sound) (w := CB2_5_1I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_5_1I2PairMassTerm : Ball := ⟨0, (847032951 / 4000000000000000000000000000000)⟩
lemma CB2_5_1I2PairMassTerm_sound : CB2_5_1I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB2_5_1I2PairMass_sound) CB2_5_1I2PairMassTermLog_sound) (by decide +kernel)
def CB2_5_1I2PairH : Ball := ⟨(293552408612091855129500575607 / 312500000000000000000000000000), (90012470607 / 100000000000000000000000000000000)⟩
lemma CB2_5_1I2PairH_sound : CB2_5_1I2PairH.Encloses (homogeneousEntropy CB2_5_1I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2PairValue CB2_5_1I2PairMassTerm_sound CB2_5_1I2PairEntropy_sound) (by decide +kernel)

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
def CB2_5_1I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 0 a
def CB2_5_1I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 0 a
lemma CB2_5_1I2R0Raw_sound (a : Fin 6) :
    (CB2_5_1I2R0Raw a).Encloses (CB2_5_1I2R0Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 0 a
def CB2_5_1I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R0Certificates_valid :
    CB2_5_1I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R0Certificates (CB2_5_1I2R0CertificateIndex a)).input
lemma CB2_5_1I2R0P_check : ∀ a : Fin 6, contains (CB2_5_1I2R0Raw a) (CB2_5_1I2R0P a) = true := by
  decide +kernel
lemma CB2_5_1I2R0P_sound (a : Fin 6) :
    (CB2_5_1I2R0P a).Encloses (CB2_5_1I2R0Value a) :=
  contains_sound (CB2_5_1I2R0Raw_sound a) (CB2_5_1I2R0P_check a)
def CB2_5_1I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R0Certificates (CB2_5_1I2R0CertificateIndex a)).output
lemma CB2_5_1I2R0Terms_sound (a : Fin 6) :
    (CB2_5_1I2R0Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R0Certificates_valid
    (CB2_5_1I2R0CertificateIndex a) (CB2_5_1I2R0P_sound a)
def CB2_5_1I2R0Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R0Entropy_sound : CB2_5_1I2R0Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R0Value CB2_5_1I2R0Terms CB2_5_1I2R0Terms_sound) (by decide +kernel)
def CB2_5_1I2R0Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R0Mass_sound : CB2_5_1I2R0Mass.Encloses (∑ a, CB2_5_1I2R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R0P CB2_5_1I2R0Value CB2_5_1I2R0P_sound) (by decide +kernel)
def CB2_5_1I2R0MassTerm : Ball := .exact 0
lemma CB2_5_1I2R0MassTerm_sound : CB2_5_1I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R0Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R0Mass_sound)
def CB2_5_1I2R0H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R0H_sound : CB2_5_1I2R0H.Encloses (homogeneousEntropy CB2_5_1I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R0Value CB2_5_1I2R0MassTerm_sound CB2_5_1I2R0Entropy_sound) (by decide +kernel)
def CB2_5_1I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 1 a
def CB2_5_1I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 1 a
lemma CB2_5_1I2R1Raw_sound (a : Fin 6) :
    (CB2_5_1I2R1Raw a).Encloses (CB2_5_1I2R1Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 1 a
def CB2_5_1I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(354599982032740129828053827979 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(877420057559102802694039590203 / 25000000000000000000000000000000), (168951303 / 12500000000000000000000000000000)⟩ ⟨(-494878794143926844783046347417239 / 100000000000000000000000000000000), (19058241357 / 10000000000000000000000000000000)⟩ ⟨-8, 354599982032740129828053827979, 195312500000000000000000000000⟩]
lemma CB2_5_1I2R1Certificates_valid :
    CB2_5_1I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_5_1I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R1Certificates (CB2_5_1I2R1CertificateIndex a)).input
lemma CB2_5_1I2R1P_check : ∀ a : Fin 6, contains (CB2_5_1I2R1Raw a) (CB2_5_1I2R1P a) = true := by
  decide +kernel
lemma CB2_5_1I2R1P_sound (a : Fin 6) :
    (CB2_5_1I2R1P a).Encloses (CB2_5_1I2R1Value a) :=
  contains_sound (CB2_5_1I2R1Raw_sound a) (CB2_5_1I2R1P_check a)
def CB2_5_1I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R1Certificates (CB2_5_1I2R1CertificateIndex a)).output
lemma CB2_5_1I2R1Terms_sound (a : Fin 6) :
    (CB2_5_1I2R1Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R1Certificates_valid
    (CB2_5_1I2R1CertificateIndex a) (CB2_5_1I2R1P_sound a)
def CB2_5_1I2R1Entropy : Ball := ⟨(877420057559102802694039590203 / 25000000000000000000000000000000), (168951303 / 12500000000000000000000000000000)⟩
lemma CB2_5_1I2R1Entropy_sound : CB2_5_1I2R1Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R1Value CB2_5_1I2R1Terms CB2_5_1I2R1Terms_sound) (by decide +kernel)
def CB2_5_1I2R1Mass : Ball := ⟨(354599982032740129828053827979 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma CB2_5_1I2R1Mass_sound : CB2_5_1I2R1Mass.Encloses (∑ a, CB2_5_1I2R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R1P CB2_5_1I2R1Value CB2_5_1I2R1P_sound) (by decide +kernel)
def CB2_5_1I2R1MassTermLogWitness : LogWitness := ⟨-8, 354599982032740129828053827979, 195312500000000000000000000000⟩
def CB2_5_1I2R1MassTermLog : Ball := ⟨(-494878794143926844783046347417239 / 100000000000000000000000000000000), (19058241357 / 10000000000000000000000000000000)⟩
lemma CB2_5_1I2R1MassTermLog_sound : CB2_5_1I2R1MassTermLog.Encloses (Real.log ((∑ a, CB2_5_1I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_5_1I2R1Mass_sound) (w := CB2_5_1I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_5_1I2R1MassTerm : Ball := ⟨(877420057559102802694039590203 / 25000000000000000000000000000000), (168951303 / 12500000000000000000000000000000)⟩
lemma CB2_5_1I2R1MassTerm_sound : CB2_5_1I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_5_1I2R1Mass_sound) CB2_5_1I2R1MassTermLog_sound) (by decide +kernel)
def CB2_5_1I2R1H : Ball := ⟨0, (168951303 / 6250000000000000000000000000000)⟩
lemma CB2_5_1I2R1H_sound : CB2_5_1I2R1H.Encloses (homogeneousEntropy CB2_5_1I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R1Value CB2_5_1I2R1MassTerm_sound CB2_5_1I2R1Entropy_sound) (by decide +kernel)
def CB2_5_1I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 2 a
def CB2_5_1I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 2 a
lemma CB2_5_1I2R2Raw_sound (a : Fin 6) :
    (CB2_5_1I2R2Raw a).Encloses (CB2_5_1I2R2Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 2 a
def CB2_5_1I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(31399400357554439564752537654833 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(4546560129505194253022711068703 / 12500000000000000000000000000000), (4986811251 / 25000000000000000000000000000000)⟩ ⟨(-115838139014940238562116354817541 / 100000000000000000000000000000000), (7940933887 / 12500000000000000000000000000000)⟩ ⟨-2, 31399400357554439564752537654833, 25000000000000000000000000000000⟩,
   .log ⟨(56517553003898872615455314497 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(766968855704191661385160206079 / 100000000000000000000000000000000), (263297271 / 100000000000000000000000000000000)⟩ ⟨(-339261351093562998797346046842591 / 50000000000000000000000000000000), (232934061397 / 100000000000000000000000000000000)⟩ ⟨-10, 56517553003898872615455314497, 48828125000000000000000000000⟩]
lemma CB2_5_1I2R2Certificates_valid :
    CB2_5_1I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_5_1I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R2Certificates (CB2_5_1I2R2CertificateIndex a)).input
lemma CB2_5_1I2R2P_check : ∀ a : Fin 6, contains (CB2_5_1I2R2Raw a) (CB2_5_1I2R2P a) = true := by
  decide +kernel
lemma CB2_5_1I2R2P_sound (a : Fin 6) :
    (CB2_5_1I2R2P a).Encloses (CB2_5_1I2R2Value a) :=
  contains_sound (CB2_5_1I2R2Raw_sound a) (CB2_5_1I2R2P_check a)
def CB2_5_1I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R2Certificates (CB2_5_1I2R2CertificateIndex a)).output
lemma CB2_5_1I2R2Terms_sound (a : Fin 6) :
    (CB2_5_1I2R2Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R2Certificates_valid
    (CB2_5_1I2R2CertificateIndex a) (CB2_5_1I2R2P_sound a)
def CB2_5_1I2R2Entropy : Ball := ⟨(37139449891745745685566848755703 / 100000000000000000000000000000000), (808421691 / 4000000000000000000000000000000)⟩
lemma CB2_5_1I2R2Entropy_sound : CB2_5_1I2R2Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R2Value CB2_5_1I2R2Terms CB2_5_1I2R2Terms_sound) (by decide +kernel)
def CB2_5_1I2R2Mass : Ball := ⟨(31512435463562237309983448283827 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
lemma CB2_5_1I2R2Mass_sound : CB2_5_1I2R2Mass.Encloses (∑ a, CB2_5_1I2R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R2P CB2_5_1I2R2Value CB2_5_1I2R2P_sound) (by decide +kernel)
def CB2_5_1I2R2MassTermLogWitness : LogWitness := ⟨-2, 31512435463562237309983448283827, 25000000000000000000000000000000⟩
def CB2_5_1I2R2MassTermLog : Ball := ⟨(-14434849267990855597880807746391 / 12500000000000000000000000000000), (63527471099 / 100000000000000000000000000000000)⟩
lemma CB2_5_1I2R2MassTermLog_sound : CB2_5_1I2R2MassTermLog.Encloses (Real.log ((∑ a, CB2_5_1I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_5_1I2R2Mass_sound) (w := CB2_5_1I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_5_1I2R2MassTerm : Ball := ⟨(18195090239352417580992918396093 / 50000000000000000000000000000000), (20019053351 / 100000000000000000000000000000000)⟩
lemma CB2_5_1I2R2MassTerm_sound : CB2_5_1I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_5_1I2R2Mass_sound) CB2_5_1I2R2MassTermLog_sound) (by decide +kernel)
def CB2_5_1I2R2H : Ball := ⟨(749269413040910523581011963517 / 100000000000000000000000000000000), (20114797813 / 50000000000000000000000000000000)⟩
lemma CB2_5_1I2R2H_sound : CB2_5_1I2R2H.Encloses (homogeneousEntropy CB2_5_1I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R2Value CB2_5_1I2R2MassTerm_sound CB2_5_1I2R2Entropy_sound) (by decide +kernel)
def CB2_5_1I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 3 a
def CB2_5_1I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 3 a
lemma CB2_5_1I2R3Raw_sound (a : Fin 6) :
    (CB2_5_1I2R3Raw a).Encloses (CB2_5_1I2R3Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 3 a
def CB2_5_1I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R3Certificates_valid :
    CB2_5_1I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R3Certificates (CB2_5_1I2R3CertificateIndex a)).input
lemma CB2_5_1I2R3P_check : ∀ a : Fin 6, contains (CB2_5_1I2R3Raw a) (CB2_5_1I2R3P a) = true := by
  decide +kernel
lemma CB2_5_1I2R3P_sound (a : Fin 6) :
    (CB2_5_1I2R3P a).Encloses (CB2_5_1I2R3Value a) :=
  contains_sound (CB2_5_1I2R3Raw_sound a) (CB2_5_1I2R3P_check a)
def CB2_5_1I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R3Certificates (CB2_5_1I2R3CertificateIndex a)).output
lemma CB2_5_1I2R3Terms_sound (a : Fin 6) :
    (CB2_5_1I2R3Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R3Certificates_valid
    (CB2_5_1I2R3CertificateIndex a) (CB2_5_1I2R3P_sound a)
def CB2_5_1I2R3Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R3Entropy_sound : CB2_5_1I2R3Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R3Value CB2_5_1I2R3Terms CB2_5_1I2R3Terms_sound) (by decide +kernel)
def CB2_5_1I2R3Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R3Mass_sound : CB2_5_1I2R3Mass.Encloses (∑ a, CB2_5_1I2R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R3P CB2_5_1I2R3Value CB2_5_1I2R3P_sound) (by decide +kernel)
def CB2_5_1I2R3MassTerm : Ball := .exact 0
lemma CB2_5_1I2R3MassTerm_sound : CB2_5_1I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R3Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R3Mass_sound)
def CB2_5_1I2R3H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R3H_sound : CB2_5_1I2R3H.Encloses (homogeneousEntropy CB2_5_1I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R3Value CB2_5_1I2R3MassTerm_sound CB2_5_1I2R3Entropy_sound) (by decide +kernel)
def CB2_5_1I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 4 a
def CB2_5_1I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 4 a
lemma CB2_5_1I2R4Raw_sound (a : Fin 6) :
    (CB2_5_1I2R4Raw a).Encloses (CB2_5_1I2R4Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 4 a
def CB2_5_1I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R4Certificates_valid :
    CB2_5_1I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R4Certificates (CB2_5_1I2R4CertificateIndex a)).input
lemma CB2_5_1I2R4P_check : ∀ a : Fin 6, contains (CB2_5_1I2R4Raw a) (CB2_5_1I2R4P a) = true := by
  decide +kernel
lemma CB2_5_1I2R4P_sound (a : Fin 6) :
    (CB2_5_1I2R4P a).Encloses (CB2_5_1I2R4Value a) :=
  contains_sound (CB2_5_1I2R4Raw_sound a) (CB2_5_1I2R4P_check a)
def CB2_5_1I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R4Certificates (CB2_5_1I2R4CertificateIndex a)).output
lemma CB2_5_1I2R4Terms_sound (a : Fin 6) :
    (CB2_5_1I2R4Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R4Certificates_valid
    (CB2_5_1I2R4CertificateIndex a) (CB2_5_1I2R4P_sound a)
def CB2_5_1I2R4Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R4Entropy_sound : CB2_5_1I2R4Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R4Value CB2_5_1I2R4Terms CB2_5_1I2R4Terms_sound) (by decide +kernel)
def CB2_5_1I2R4Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R4Mass_sound : CB2_5_1I2R4Mass.Encloses (∑ a, CB2_5_1I2R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R4P CB2_5_1I2R4Value CB2_5_1I2R4P_sound) (by decide +kernel)
def CB2_5_1I2R4MassTerm : Ball := .exact 0
lemma CB2_5_1I2R4MassTerm_sound : CB2_5_1I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R4Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R4Mass_sound)
def CB2_5_1I2R4H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R4H_sound : CB2_5_1I2R4H.Encloses (homogeneousEntropy CB2_5_1I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R4Value CB2_5_1I2R4MassTerm_sound CB2_5_1I2R4Entropy_sound) (by decide +kernel)
def CB2_5_1I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 5 a
def CB2_5_1I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 5 a
lemma CB2_5_1I2R5Raw_sound (a : Fin 6) :
    (CB2_5_1I2R5Raw a).Encloses (CB2_5_1I2R5Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 5 a
def CB2_5_1I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R5Certificates_valid :
    CB2_5_1I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R5Certificates (CB2_5_1I2R5CertificateIndex a)).input
lemma CB2_5_1I2R5P_check : ∀ a : Fin 6, contains (CB2_5_1I2R5Raw a) (CB2_5_1I2R5P a) = true := by
  decide +kernel
lemma CB2_5_1I2R5P_sound (a : Fin 6) :
    (CB2_5_1I2R5P a).Encloses (CB2_5_1I2R5Value a) :=
  contains_sound (CB2_5_1I2R5Raw_sound a) (CB2_5_1I2R5P_check a)
def CB2_5_1I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R5Certificates (CB2_5_1I2R5CertificateIndex a)).output
lemma CB2_5_1I2R5Terms_sound (a : Fin 6) :
    (CB2_5_1I2R5Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R5Certificates_valid
    (CB2_5_1I2R5CertificateIndex a) (CB2_5_1I2R5P_sound a)
def CB2_5_1I2R5Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R5Entropy_sound : CB2_5_1I2R5Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R5Value CB2_5_1I2R5Terms CB2_5_1I2R5Terms_sound) (by decide +kernel)
def CB2_5_1I2R5Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R5Mass_sound : CB2_5_1I2R5Mass.Encloses (∑ a, CB2_5_1I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R5P CB2_5_1I2R5Value CB2_5_1I2R5P_sound) (by decide +kernel)
def CB2_5_1I2R5MassTerm : Ball := .exact 0
lemma CB2_5_1I2R5MassTerm_sound : CB2_5_1I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R5Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R5Mass_sound)
def CB2_5_1I2R5H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R5H_sound : CB2_5_1I2R5H.Encloses (homogeneousEntropy CB2_5_1I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R5Value CB2_5_1I2R5MassTerm_sound CB2_5_1I2R5Entropy_sound) (by decide +kernel)
def CB2_5_1I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 6 a
def CB2_5_1I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 6 a
lemma CB2_5_1I2R6Raw_sound (a : Fin 6) :
    (CB2_5_1I2R6Raw a).Encloses (CB2_5_1I2R6Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 6 a
def CB2_5_1I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R6Certificates_valid :
    CB2_5_1I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R6Certificates (CB2_5_1I2R6CertificateIndex a)).input
lemma CB2_5_1I2R6P_check : ∀ a : Fin 6, contains (CB2_5_1I2R6Raw a) (CB2_5_1I2R6P a) = true := by
  decide +kernel
lemma CB2_5_1I2R6P_sound (a : Fin 6) :
    (CB2_5_1I2R6P a).Encloses (CB2_5_1I2R6Value a) :=
  contains_sound (CB2_5_1I2R6Raw_sound a) (CB2_5_1I2R6P_check a)
def CB2_5_1I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R6Certificates (CB2_5_1I2R6CertificateIndex a)).output
lemma CB2_5_1I2R6Terms_sound (a : Fin 6) :
    (CB2_5_1I2R6Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R6Certificates_valid
    (CB2_5_1I2R6CertificateIndex a) (CB2_5_1I2R6P_sound a)
def CB2_5_1I2R6Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R6Entropy_sound : CB2_5_1I2R6Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R6Value CB2_5_1I2R6Terms CB2_5_1I2R6Terms_sound) (by decide +kernel)
def CB2_5_1I2R6Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R6Mass_sound : CB2_5_1I2R6Mass.Encloses (∑ a, CB2_5_1I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R6P CB2_5_1I2R6Value CB2_5_1I2R6P_sound) (by decide +kernel)
def CB2_5_1I2R6MassTerm : Ball := .exact 0
lemma CB2_5_1I2R6MassTerm_sound : CB2_5_1I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R6Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R6Mass_sound)
def CB2_5_1I2R6H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R6H_sound : CB2_5_1I2R6H.Encloses (homogeneousEntropy CB2_5_1I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R6Value CB2_5_1I2R6MassTerm_sound CB2_5_1I2R6Entropy_sound) (by decide +kernel)
def CB2_5_1I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 7 a
def CB2_5_1I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 7 a
lemma CB2_5_1I2R7Raw_sound (a : Fin 6) :
    (CB2_5_1I2R7Raw a).Encloses (CB2_5_1I2R7Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 7 a
def CB2_5_1I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R7Certificates_valid :
    CB2_5_1I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R7Certificates (CB2_5_1I2R7CertificateIndex a)).input
lemma CB2_5_1I2R7P_check : ∀ a : Fin 6, contains (CB2_5_1I2R7Raw a) (CB2_5_1I2R7P a) = true := by
  decide +kernel
lemma CB2_5_1I2R7P_sound (a : Fin 6) :
    (CB2_5_1I2R7P a).Encloses (CB2_5_1I2R7Value a) :=
  contains_sound (CB2_5_1I2R7Raw_sound a) (CB2_5_1I2R7P_check a)
def CB2_5_1I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R7Certificates (CB2_5_1I2R7CertificateIndex a)).output
lemma CB2_5_1I2R7Terms_sound (a : Fin 6) :
    (CB2_5_1I2R7Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R7Certificates_valid
    (CB2_5_1I2R7CertificateIndex a) (CB2_5_1I2R7P_sound a)
def CB2_5_1I2R7Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R7Entropy_sound : CB2_5_1I2R7Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R7Value CB2_5_1I2R7Terms CB2_5_1I2R7Terms_sound) (by decide +kernel)
def CB2_5_1I2R7Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R7Mass_sound : CB2_5_1I2R7Mass.Encloses (∑ a, CB2_5_1I2R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R7P CB2_5_1I2R7Value CB2_5_1I2R7P_sound) (by decide +kernel)
def CB2_5_1I2R7MassTerm : Ball := .exact 0
lemma CB2_5_1I2R7MassTerm_sound : CB2_5_1I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R7Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R7Mass_sound)
def CB2_5_1I2R7H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R7H_sound : CB2_5_1I2R7H.Encloses (homogeneousEntropy CB2_5_1I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R7Value CB2_5_1I2R7MassTerm_sound CB2_5_1I2R7Entropy_sound) (by decide +kernel)
def CB2_5_1I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 8 a
def CB2_5_1I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 8 a
lemma CB2_5_1I2R8Raw_sound (a : Fin 6) :
    (CB2_5_1I2R8Raw a).Encloses (CB2_5_1I2R8Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 8 a
def CB2_5_1I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R8Certificates_valid :
    CB2_5_1I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R8Certificates (CB2_5_1I2R8CertificateIndex a)).input
lemma CB2_5_1I2R8P_check : ∀ a : Fin 6, contains (CB2_5_1I2R8Raw a) (CB2_5_1I2R8P a) = true := by
  decide +kernel
lemma CB2_5_1I2R8P_sound (a : Fin 6) :
    (CB2_5_1I2R8P a).Encloses (CB2_5_1I2R8Value a) :=
  contains_sound (CB2_5_1I2R8Raw_sound a) (CB2_5_1I2R8P_check a)
def CB2_5_1I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R8Certificates (CB2_5_1I2R8CertificateIndex a)).output
lemma CB2_5_1I2R8Terms_sound (a : Fin 6) :
    (CB2_5_1I2R8Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R8Certificates_valid
    (CB2_5_1I2R8CertificateIndex a) (CB2_5_1I2R8P_sound a)
def CB2_5_1I2R8Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R8Entropy_sound : CB2_5_1I2R8Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R8Value CB2_5_1I2R8Terms CB2_5_1I2R8Terms_sound) (by decide +kernel)
def CB2_5_1I2R8Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R8Mass_sound : CB2_5_1I2R8Mass.Encloses (∑ a, CB2_5_1I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R8P CB2_5_1I2R8Value CB2_5_1I2R8P_sound) (by decide +kernel)
def CB2_5_1I2R8MassTerm : Ball := .exact 0
lemma CB2_5_1I2R8MassTerm_sound : CB2_5_1I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R8Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R8Mass_sound)
def CB2_5_1I2R8H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R8H_sound : CB2_5_1I2R8H.Encloses (homogeneousEntropy CB2_5_1I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R8Value CB2_5_1I2R8MassTerm_sound CB2_5_1I2R8Entropy_sound) (by decide +kernel)
def CB2_5_1I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 9 a
def CB2_5_1I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 9 a
lemma CB2_5_1I2R9Raw_sound (a : Fin 6) :
    (CB2_5_1I2R9Raw a).Encloses (CB2_5_1I2R9Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 9 a
def CB2_5_1I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R9Certificates_valid :
    CB2_5_1I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R9Certificates (CB2_5_1I2R9CertificateIndex a)).input
lemma CB2_5_1I2R9P_check : ∀ a : Fin 6, contains (CB2_5_1I2R9Raw a) (CB2_5_1I2R9P a) = true := by
  decide +kernel
lemma CB2_5_1I2R9P_sound (a : Fin 6) :
    (CB2_5_1I2R9P a).Encloses (CB2_5_1I2R9Value a) :=
  contains_sound (CB2_5_1I2R9Raw_sound a) (CB2_5_1I2R9P_check a)
def CB2_5_1I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R9Certificates (CB2_5_1I2R9CertificateIndex a)).output
lemma CB2_5_1I2R9Terms_sound (a : Fin 6) :
    (CB2_5_1I2R9Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R9Certificates_valid
    (CB2_5_1I2R9CertificateIndex a) (CB2_5_1I2R9P_sound a)
def CB2_5_1I2R9Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R9Entropy_sound : CB2_5_1I2R9Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R9Value CB2_5_1I2R9Terms CB2_5_1I2R9Terms_sound) (by decide +kernel)
def CB2_5_1I2R9Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R9Mass_sound : CB2_5_1I2R9Mass.Encloses (∑ a, CB2_5_1I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R9P CB2_5_1I2R9Value CB2_5_1I2R9P_sound) (by decide +kernel)
def CB2_5_1I2R9MassTerm : Ball := .exact 0
lemma CB2_5_1I2R9MassTerm_sound : CB2_5_1I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R9Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R9Mass_sound)
def CB2_5_1I2R9H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R9H_sound : CB2_5_1I2R9H.Encloses (homogeneousEntropy CB2_5_1I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R9Value CB2_5_1I2R9MassTerm_sound CB2_5_1I2R9Entropy_sound) (by decide +kernel)
def CB2_5_1I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 10 a
def CB2_5_1I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 10 a
lemma CB2_5_1I2R10Raw_sound (a : Fin 6) :
    (CB2_5_1I2R10Raw a).Encloses (CB2_5_1I2R10Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 10 a
def CB2_5_1I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R10Certificates_valid :
    CB2_5_1I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R10Certificates (CB2_5_1I2R10CertificateIndex a)).input
lemma CB2_5_1I2R10P_check : ∀ a : Fin 6, contains (CB2_5_1I2R10Raw a) (CB2_5_1I2R10P a) = true := by
  decide +kernel
lemma CB2_5_1I2R10P_sound (a : Fin 6) :
    (CB2_5_1I2R10P a).Encloses (CB2_5_1I2R10Value a) :=
  contains_sound (CB2_5_1I2R10Raw_sound a) (CB2_5_1I2R10P_check a)
def CB2_5_1I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R10Certificates (CB2_5_1I2R10CertificateIndex a)).output
lemma CB2_5_1I2R10Terms_sound (a : Fin 6) :
    (CB2_5_1I2R10Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R10Certificates_valid
    (CB2_5_1I2R10CertificateIndex a) (CB2_5_1I2R10P_sound a)
def CB2_5_1I2R10Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R10Entropy_sound : CB2_5_1I2R10Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R10Value CB2_5_1I2R10Terms CB2_5_1I2R10Terms_sound) (by decide +kernel)
def CB2_5_1I2R10Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R10Mass_sound : CB2_5_1I2R10Mass.Encloses (∑ a, CB2_5_1I2R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R10P CB2_5_1I2R10Value CB2_5_1I2R10P_sound) (by decide +kernel)
def CB2_5_1I2R10MassTerm : Ball := .exact 0
lemma CB2_5_1I2R10MassTerm_sound : CB2_5_1I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R10Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R10Mass_sound)
def CB2_5_1I2R10H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R10H_sound : CB2_5_1I2R10H.Encloses (homogeneousEntropy CB2_5_1I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R10Value CB2_5_1I2R10MassTerm_sound CB2_5_1I2R10Entropy_sound) (by decide +kernel)
def CB2_5_1I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 11 a
def CB2_5_1I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 11 a
lemma CB2_5_1I2R11Raw_sound (a : Fin 6) :
    (CB2_5_1I2R11Raw a).Encloses (CB2_5_1I2R11Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 11 a
def CB2_5_1I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R11Certificates_valid :
    CB2_5_1I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R11Certificates (CB2_5_1I2R11CertificateIndex a)).input
lemma CB2_5_1I2R11P_check : ∀ a : Fin 6, contains (CB2_5_1I2R11Raw a) (CB2_5_1I2R11P a) = true := by
  decide +kernel
lemma CB2_5_1I2R11P_sound (a : Fin 6) :
    (CB2_5_1I2R11P a).Encloses (CB2_5_1I2R11Value a) :=
  contains_sound (CB2_5_1I2R11Raw_sound a) (CB2_5_1I2R11P_check a)
def CB2_5_1I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R11Certificates (CB2_5_1I2R11CertificateIndex a)).output
lemma CB2_5_1I2R11Terms_sound (a : Fin 6) :
    (CB2_5_1I2R11Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R11Certificates_valid
    (CB2_5_1I2R11CertificateIndex a) (CB2_5_1I2R11P_sound a)
def CB2_5_1I2R11Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R11Entropy_sound : CB2_5_1I2R11Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R11Value CB2_5_1I2R11Terms CB2_5_1I2R11Terms_sound) (by decide +kernel)
def CB2_5_1I2R11Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R11Mass_sound : CB2_5_1I2R11Mass.Encloses (∑ a, CB2_5_1I2R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R11P CB2_5_1I2R11Value CB2_5_1I2R11P_sound) (by decide +kernel)
def CB2_5_1I2R11MassTerm : Ball := .exact 0
lemma CB2_5_1I2R11MassTerm_sound : CB2_5_1I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R11Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R11Mass_sound)
def CB2_5_1I2R11H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R11H_sound : CB2_5_1I2R11H.Encloses (homogeneousEntropy CB2_5_1I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R11Value CB2_5_1I2R11MassTerm_sound CB2_5_1I2R11Entropy_sound) (by decide +kernel)
def CB2_5_1I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 12 a
def CB2_5_1I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 12 a
lemma CB2_5_1I2R12Raw_sound (a : Fin 6) :
    (CB2_5_1I2R12Raw a).Encloses (CB2_5_1I2R12Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 12 a
def CB2_5_1I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R12Certificates_valid :
    CB2_5_1I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R12Certificates (CB2_5_1I2R12CertificateIndex a)).input
lemma CB2_5_1I2R12P_check : ∀ a : Fin 6, contains (CB2_5_1I2R12Raw a) (CB2_5_1I2R12P a) = true := by
  decide +kernel
lemma CB2_5_1I2R12P_sound (a : Fin 6) :
    (CB2_5_1I2R12P a).Encloses (CB2_5_1I2R12Value a) :=
  contains_sound (CB2_5_1I2R12Raw_sound a) (CB2_5_1I2R12P_check a)
def CB2_5_1I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R12Certificates (CB2_5_1I2R12CertificateIndex a)).output
lemma CB2_5_1I2R12Terms_sound (a : Fin 6) :
    (CB2_5_1I2R12Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R12Certificates_valid
    (CB2_5_1I2R12CertificateIndex a) (CB2_5_1I2R12P_sound a)
def CB2_5_1I2R12Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R12Entropy_sound : CB2_5_1I2R12Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R12Value CB2_5_1I2R12Terms CB2_5_1I2R12Terms_sound) (by decide +kernel)
def CB2_5_1I2R12Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R12Mass_sound : CB2_5_1I2R12Mass.Encloses (∑ a, CB2_5_1I2R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R12P CB2_5_1I2R12Value CB2_5_1I2R12P_sound) (by decide +kernel)
def CB2_5_1I2R12MassTerm : Ball := .exact 0
lemma CB2_5_1I2R12MassTerm_sound : CB2_5_1I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R12Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R12Mass_sound)
def CB2_5_1I2R12H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R12H_sound : CB2_5_1I2R12H.Encloses (homogeneousEntropy CB2_5_1I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R12Value CB2_5_1I2R12MassTerm_sound CB2_5_1I2R12Entropy_sound) (by decide +kernel)
def CB2_5_1I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 13 a
def CB2_5_1I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 13 a
lemma CB2_5_1I2R13Raw_sound (a : Fin 6) :
    (CB2_5_1I2R13Raw a).Encloses (CB2_5_1I2R13Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 13 a
def CB2_5_1I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R13Certificates_valid :
    CB2_5_1I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R13Certificates (CB2_5_1I2R13CertificateIndex a)).input
lemma CB2_5_1I2R13P_check : ∀ a : Fin 6, contains (CB2_5_1I2R13Raw a) (CB2_5_1I2R13P a) = true := by
  decide +kernel
lemma CB2_5_1I2R13P_sound (a : Fin 6) :
    (CB2_5_1I2R13P a).Encloses (CB2_5_1I2R13Value a) :=
  contains_sound (CB2_5_1I2R13Raw_sound a) (CB2_5_1I2R13P_check a)
def CB2_5_1I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R13Certificates (CB2_5_1I2R13CertificateIndex a)).output
lemma CB2_5_1I2R13Terms_sound (a : Fin 6) :
    (CB2_5_1I2R13Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R13Certificates_valid
    (CB2_5_1I2R13CertificateIndex a) (CB2_5_1I2R13P_sound a)
def CB2_5_1I2R13Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R13Entropy_sound : CB2_5_1I2R13Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R13Value CB2_5_1I2R13Terms CB2_5_1I2R13Terms_sound) (by decide +kernel)
def CB2_5_1I2R13Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R13Mass_sound : CB2_5_1I2R13Mass.Encloses (∑ a, CB2_5_1I2R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R13P CB2_5_1I2R13Value CB2_5_1I2R13P_sound) (by decide +kernel)
def CB2_5_1I2R13MassTerm : Ball := .exact 0
lemma CB2_5_1I2R13MassTerm_sound : CB2_5_1I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R13Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R13Mass_sound)
def CB2_5_1I2R13H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R13H_sound : CB2_5_1I2R13H.Encloses (homogeneousEntropy CB2_5_1I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R13Value CB2_5_1I2R13MassTerm_sound CB2_5_1I2R13Entropy_sound) (by decide +kernel)
def CB2_5_1I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 14 a
def CB2_5_1I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 14 a
lemma CB2_5_1I2R14Raw_sound (a : Fin 6) :
    (CB2_5_1I2R14Raw a).Encloses (CB2_5_1I2R14Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 14 a
def CB2_5_1I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R14Certificates_valid :
    CB2_5_1I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R14Certificates (CB2_5_1I2R14CertificateIndex a)).input
lemma CB2_5_1I2R14P_check : ∀ a : Fin 6, contains (CB2_5_1I2R14Raw a) (CB2_5_1I2R14P a) = true := by
  decide +kernel
lemma CB2_5_1I2R14P_sound (a : Fin 6) :
    (CB2_5_1I2R14P a).Encloses (CB2_5_1I2R14Value a) :=
  contains_sound (CB2_5_1I2R14Raw_sound a) (CB2_5_1I2R14P_check a)
def CB2_5_1I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R14Certificates (CB2_5_1I2R14CertificateIndex a)).output
lemma CB2_5_1I2R14Terms_sound (a : Fin 6) :
    (CB2_5_1I2R14Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R14Certificates_valid
    (CB2_5_1I2R14CertificateIndex a) (CB2_5_1I2R14P_sound a)
def CB2_5_1I2R14Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R14Entropy_sound : CB2_5_1I2R14Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R14Value CB2_5_1I2R14Terms CB2_5_1I2R14Terms_sound) (by decide +kernel)
def CB2_5_1I2R14Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R14Mass_sound : CB2_5_1I2R14Mass.Encloses (∑ a, CB2_5_1I2R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R14P CB2_5_1I2R14Value CB2_5_1I2R14P_sound) (by decide +kernel)
def CB2_5_1I2R14MassTerm : Ball := .exact 0
lemma CB2_5_1I2R14MassTerm_sound : CB2_5_1I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R14Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R14Mass_sound)
def CB2_5_1I2R14H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R14H_sound : CB2_5_1I2R14H.Encloses (homogeneousEntropy CB2_5_1I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R14Value CB2_5_1I2R14MassTerm_sound CB2_5_1I2R14Entropy_sound) (by decide +kernel)
def CB2_5_1I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 15 a
def CB2_5_1I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 15 a
lemma CB2_5_1I2R15Raw_sound (a : Fin 6) :
    (CB2_5_1I2R15Raw a).Encloses (CB2_5_1I2R15Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 15 a
def CB2_5_1I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R15Certificates_valid :
    CB2_5_1I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R15Certificates (CB2_5_1I2R15CertificateIndex a)).input
lemma CB2_5_1I2R15P_check : ∀ a : Fin 6, contains (CB2_5_1I2R15Raw a) (CB2_5_1I2R15P a) = true := by
  decide +kernel
lemma CB2_5_1I2R15P_sound (a : Fin 6) :
    (CB2_5_1I2R15P a).Encloses (CB2_5_1I2R15Value a) :=
  contains_sound (CB2_5_1I2R15Raw_sound a) (CB2_5_1I2R15P_check a)
def CB2_5_1I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R15Certificates (CB2_5_1I2R15CertificateIndex a)).output
lemma CB2_5_1I2R15Terms_sound (a : Fin 6) :
    (CB2_5_1I2R15Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R15Certificates_valid
    (CB2_5_1I2R15CertificateIndex a) (CB2_5_1I2R15P_sound a)
def CB2_5_1I2R15Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R15Entropy_sound : CB2_5_1I2R15Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R15Value CB2_5_1I2R15Terms CB2_5_1I2R15Terms_sound) (by decide +kernel)
def CB2_5_1I2R15Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R15Mass_sound : CB2_5_1I2R15Mass.Encloses (∑ a, CB2_5_1I2R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R15P CB2_5_1I2R15Value CB2_5_1I2R15P_sound) (by decide +kernel)
def CB2_5_1I2R15MassTerm : Ball := .exact 0
lemma CB2_5_1I2R15MassTerm_sound : CB2_5_1I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R15Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R15Mass_sound)
def CB2_5_1I2R15H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R15H_sound : CB2_5_1I2R15H.Encloses (homogeneousEntropy CB2_5_1I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R15Value CB2_5_1I2R15MassTerm_sound CB2_5_1I2R15Entropy_sound) (by decide +kernel)
def CB2_5_1I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) 16 a
def CB2_5_1I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 2 5 1)) B2_5_1Law (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) 16 a
lemma CB2_5_1I2R16Raw_sound (a : Fin 6) :
    (CB2_5_1I2R16Raw a).Encloses (CB2_5_1I2R16Value a) := by
  exact residualBall_sound_on (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u => B2_5_1Little u ((stageBPriority (shape 2 5 1)) 2)) (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) (fun u _ a => B2_5_1Little_sound u ((stageBPriority (shape 2 5 1)) 2) a) 16 a
def CB2_5_1I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_5_1I2R16Certificates_valid :
    CB2_5_1I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R16Certificates (CB2_5_1I2R16CertificateIndex a)).input
lemma CB2_5_1I2R16P_check : ∀ a : Fin 6, contains (CB2_5_1I2R16Raw a) (CB2_5_1I2R16P a) = true := by
  decide +kernel
lemma CB2_5_1I2R16P_sound (a : Fin 6) :
    (CB2_5_1I2R16P a).Encloses (CB2_5_1I2R16Value a) :=
  contains_sound (CB2_5_1I2R16Raw_sound a) (CB2_5_1I2R16P_check a)
def CB2_5_1I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I2R16Certificates (CB2_5_1I2R16CertificateIndex a)).output
lemma CB2_5_1I2R16Terms_sound (a : Fin 6) :
    (CB2_5_1I2R16Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I2R16Certificates_valid
    (CB2_5_1I2R16CertificateIndex a) (CB2_5_1I2R16P_sound a)
def CB2_5_1I2R16Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R16Entropy_sound : CB2_5_1I2R16Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2R16Value CB2_5_1I2R16Terms CB2_5_1I2R16Terms_sound) (by decide +kernel)
def CB2_5_1I2R16Mass : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R16Mass_sound : CB2_5_1I2R16Mass.Encloses (∑ a, CB2_5_1I2R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_5_1I2R16P CB2_5_1I2R16Value CB2_5_1I2R16P_sound) (by decide +kernel)
def CB2_5_1I2R16MassTerm : Ball := .exact 0
lemma CB2_5_1I2R16MassTerm_sound : CB2_5_1I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2R16Value a))) :=
  entropyTerm_zero_ball (CB2_5_1I2R16Mass_sound)
def CB2_5_1I2R16H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2R16H_sound : CB2_5_1I2R16H.Encloses (homogeneousEntropy CB2_5_1I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2R16Value CB2_5_1I2R16MassTerm_sound CB2_5_1I2R16Entropy_sound) (by decide +kernel)
def CB2_5_1I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_5_1I2R0H
  | 1 => CB2_5_1I2R1H
  | 2 => CB2_5_1I2R2H
  | 3 => CB2_5_1I2R3H
  | 4 => CB2_5_1I2R4H
  | 5 => CB2_5_1I2R5H
  | 6 => CB2_5_1I2R6H
  | 7 => CB2_5_1I2R7H
  | 8 => CB2_5_1I2R8H
  | 9 => CB2_5_1I2R9H
  | 10 => CB2_5_1I2R10H
  | 11 => CB2_5_1I2R11H
  | 12 => CB2_5_1I2R12H
  | 13 => CB2_5_1I2R13H
  | 14 => CB2_5_1I2R14H
  | 15 => CB2_5_1I2R15H
  | 16 => CB2_5_1I2R16H
  | _ => (.exact 0)
lemma CB2_5_1I2ResidualEntropies_sound (k : Fin 17) :
    (CB2_5_1I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB2_5_1I2R0H_sound
  · exact CB2_5_1I2R1H_sound
  · exact CB2_5_1I2R2H_sound
  · exact CB2_5_1I2R3H_sound
  · exact CB2_5_1I2R4H_sound
  · exact CB2_5_1I2R5H_sound
  · exact CB2_5_1I2R6H_sound
  · exact CB2_5_1I2R7H_sound
  · exact CB2_5_1I2R8H_sound
  · exact CB2_5_1I2R9H_sound
  · exact CB2_5_1I2R10H_sound
  · exact CB2_5_1I2R11H_sound
  · exact CB2_5_1I2R12H_sound
  · exact CB2_5_1I2R13H_sound
  · exact CB2_5_1I2R14H_sound
  · exact CB2_5_1I2R15H_sound
  · exact CB2_5_1I2R16H_sound
def CB2_5_1I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 2 5 1) (shape 0 3 1) ((stageBPriority (shape 2 5 1)) 2) a : ℝ)
def CB2_5_1I2S0_3_1E_4Log : Ball := .exact 0
lemma CB2_5_1I2S0_3_1E_4Log_sound : CB2_5_1I2S0_3_1E_4Log.Encloses (Real.log (CB2_5_1I2S0_3_1Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B2_5_1Little_sound (shape 0 3 1) ((stageBPriority (shape 2 5 1)) 2)) (4 : Fin 6))
def CB2_5_1I2S0_3_1E_4 : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S0_3_1E_4_sound : CB2_5_1I2S0_3_1E_4.Encloses (Foundation.entropyTerm (CB2_5_1I2S0_3_1Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_5_1Little_sound (shape 0 3 1) ((stageBPriority (shape 2 5 1)) 2)) (4 : Fin 6)) CB2_5_1I2S0_3_1E_4Log_sound) (by decide +kernel)
def CB2_5_1I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB2_5_1I2S0_3_1Terms_sound (a : Fin 6) :
    (CB2_5_1I2S0_3_1Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2S0_3_1Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 0 3 1) ((stageBPriority (shape 2 5 1)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 0 3 1) ((stageBPriority (shape 2 5 1)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 0 3 1) ((stageBPriority (shape 2 5 1)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 0 3 1) ((stageBPriority (shape 2 5 1)) 2)) (3 : Fin 6)))
  · exact CB2_5_1I2S0_3_1E_4_sound
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 0 3 1) ((stageBPriority (shape 2 5 1)) 2)) (5 : Fin 6)))
def CB2_5_1I2S0_3_1Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S0_3_1Entropy_sound : CB2_5_1I2S0_3_1Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2S0_3_1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2S0_3_1Value CB2_5_1I2S0_3_1Terms CB2_5_1I2S0_3_1Terms_sound) (by decide +kernel)
def CB2_5_1I2S0_3_1Mass : Ball := ⟨1, 0⟩
lemma CB2_5_1I2S0_3_1Mass_sound : CB2_5_1I2S0_3_1Mass.Encloses (∑ a, CB2_5_1I2S0_3_1Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_5_1Little (shape 0 3 1) ((stageBPriority (shape 2 5 1)) 2)) CB2_5_1I2S0_3_1Value (B2_5_1Little_sound (shape 0 3 1) ((stageBPriority (shape 2 5 1)) 2))) (by decide +kernel)
def CB2_5_1I2S0_3_1MassTermLog : Ball := .exact 0
lemma CB2_5_1I2S0_3_1MassTermLog_sound : CB2_5_1I2S0_3_1MassTermLog.Encloses (Real.log ((∑ a, CB2_5_1I2S0_3_1Value a))) := by
  exact log_exact_one_ball (CB2_5_1I2S0_3_1Mass_sound)
def CB2_5_1I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S0_3_1MassTerm_sound : CB2_5_1I2S0_3_1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2S0_3_1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_5_1I2S0_3_1Mass_sound) CB2_5_1I2S0_3_1MassTermLog_sound) (by decide +kernel)
def CB2_5_1I2S0_3_1H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S0_3_1H_sound : CB2_5_1I2S0_3_1H.Encloses (homogeneousEntropy CB2_5_1I2S0_3_1Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2S0_3_1Value CB2_5_1I2S0_3_1MassTerm_sound CB2_5_1I2S0_3_1Entropy_sound) (by decide +kernel)
def CB2_5_1I2S0_4_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 5 1) (shape 0 4 0) ((stageBPriority (shape 2 5 1)) 2) a : ℝ)
def CB2_5_1I2S0_4_0E_5Log : Ball := .exact 0
lemma CB2_5_1I2S0_4_0E_5Log_sound : CB2_5_1I2S0_4_0E_5Log.Encloses (Real.log (CB2_5_1I2S0_4_0Value (5 : Fin 6))) := by
  exact log_exact_one_ball ((B2_5_1Little_sound (shape 0 4 0) ((stageBPriority (shape 2 5 1)) 2)) (5 : Fin 6))
def CB2_5_1I2S0_4_0E_5 : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S0_4_0E_5_sound : CB2_5_1I2S0_4_0E_5.Encloses (Foundation.entropyTerm (CB2_5_1I2S0_4_0Value (5 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_5_1Little_sound (shape 0 4 0) ((stageBPriority (shape 2 5 1)) 2)) (5 : Fin 6)) CB2_5_1I2S0_4_0E_5Log_sound) (by decide +kernel)
def CB2_5_1I2S0_4_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB2_5_1I2S0_4_0Terms_sound (a : Fin 6) :
    (CB2_5_1I2S0_4_0Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2S0_4_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 0 4 0) ((stageBPriority (shape 2 5 1)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 0 4 0) ((stageBPriority (shape 2 5 1)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 0 4 0) ((stageBPriority (shape 2 5 1)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 0 4 0) ((stageBPriority (shape 2 5 1)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 0 4 0) ((stageBPriority (shape 2 5 1)) 2)) (4 : Fin 6)))
  · exact CB2_5_1I2S0_4_0E_5_sound
def CB2_5_1I2S0_4_0Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S0_4_0Entropy_sound : CB2_5_1I2S0_4_0Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2S0_4_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2S0_4_0Value CB2_5_1I2S0_4_0Terms CB2_5_1I2S0_4_0Terms_sound) (by decide +kernel)
def CB2_5_1I2S0_4_0Mass : Ball := ⟨1, 0⟩
lemma CB2_5_1I2S0_4_0Mass_sound : CB2_5_1I2S0_4_0Mass.Encloses (∑ a, CB2_5_1I2S0_4_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_5_1Little (shape 0 4 0) ((stageBPriority (shape 2 5 1)) 2)) CB2_5_1I2S0_4_0Value (B2_5_1Little_sound (shape 0 4 0) ((stageBPriority (shape 2 5 1)) 2))) (by decide +kernel)
def CB2_5_1I2S0_4_0MassTermLog : Ball := .exact 0
lemma CB2_5_1I2S0_4_0MassTermLog_sound : CB2_5_1I2S0_4_0MassTermLog.Encloses (Real.log ((∑ a, CB2_5_1I2S0_4_0Value a))) := by
  exact log_exact_one_ball (CB2_5_1I2S0_4_0Mass_sound)
def CB2_5_1I2S0_4_0MassTerm : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S0_4_0MassTerm_sound : CB2_5_1I2S0_4_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2S0_4_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_5_1I2S0_4_0Mass_sound) CB2_5_1I2S0_4_0MassTermLog_sound) (by decide +kernel)
def CB2_5_1I2S0_4_0H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S0_4_0H_sound : CB2_5_1I2S0_4_0H.Encloses (homogeneousEntropy CB2_5_1I2S0_4_0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2S0_4_0Value CB2_5_1I2S0_4_0MassTerm_sound CB2_5_1I2S0_4_0Entropy_sound) (by decide +kernel)
def CB2_5_1I2S1_3_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 5 1) (shape 1 3 0) ((stageBPriority (shape 2 5 1)) 2) a : ℝ)
def CB2_5_1I2S1_3_0E_4Log : Ball := .exact 0
lemma CB2_5_1I2S1_3_0E_4Log_sound : CB2_5_1I2S1_3_0E_4Log.Encloses (Real.log (CB2_5_1I2S1_3_0Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B2_5_1Little_sound (shape 1 3 0) ((stageBPriority (shape 2 5 1)) 2)) (4 : Fin 6))
def CB2_5_1I2S1_3_0E_4 : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S1_3_0E_4_sound : CB2_5_1I2S1_3_0E_4.Encloses (Foundation.entropyTerm (CB2_5_1I2S1_3_0Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_5_1Little_sound (shape 1 3 0) ((stageBPriority (shape 2 5 1)) 2)) (4 : Fin 6)) CB2_5_1I2S1_3_0E_4Log_sound) (by decide +kernel)
def CB2_5_1I2S1_3_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB2_5_1I2S1_3_0Terms_sound (a : Fin 6) :
    (CB2_5_1I2S1_3_0Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2S1_3_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 1 3 0) ((stageBPriority (shape 2 5 1)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 1 3 0) ((stageBPriority (shape 2 5 1)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 1 3 0) ((stageBPriority (shape 2 5 1)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 1 3 0) ((stageBPriority (shape 2 5 1)) 2)) (3 : Fin 6)))
  · exact CB2_5_1I2S1_3_0E_4_sound
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 1 3 0) ((stageBPriority (shape 2 5 1)) 2)) (5 : Fin 6)))
def CB2_5_1I2S1_3_0Entropy : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S1_3_0Entropy_sound : CB2_5_1I2S1_3_0Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2S1_3_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2S1_3_0Value CB2_5_1I2S1_3_0Terms CB2_5_1I2S1_3_0Terms_sound) (by decide +kernel)
def CB2_5_1I2S1_3_0Mass : Ball := ⟨1, 0⟩
lemma CB2_5_1I2S1_3_0Mass_sound : CB2_5_1I2S1_3_0Mass.Encloses (∑ a, CB2_5_1I2S1_3_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_5_1Little (shape 1 3 0) ((stageBPriority (shape 2 5 1)) 2)) CB2_5_1I2S1_3_0Value (B2_5_1Little_sound (shape 1 3 0) ((stageBPriority (shape 2 5 1)) 2))) (by decide +kernel)
def CB2_5_1I2S1_3_0MassTermLog : Ball := .exact 0
lemma CB2_5_1I2S1_3_0MassTermLog_sound : CB2_5_1I2S1_3_0MassTermLog.Encloses (Real.log ((∑ a, CB2_5_1I2S1_3_0Value a))) := by
  exact log_exact_one_ball (CB2_5_1I2S1_3_0Mass_sound)
def CB2_5_1I2S1_3_0MassTerm : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S1_3_0MassTerm_sound : CB2_5_1I2S1_3_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2S1_3_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_5_1I2S1_3_0Mass_sound) CB2_5_1I2S1_3_0MassTermLog_sound) (by decide +kernel)
def CB2_5_1I2S1_3_0H : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S1_3_0H_sound : CB2_5_1I2S1_3_0H.Encloses (homogeneousEntropy CB2_5_1I2S1_3_0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2S1_3_0Value CB2_5_1I2S1_3_0MassTerm_sound CB2_5_1I2S1_3_0Entropy_sound) (by decide +kernel)
def CB2_5_1I2S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 5 1) (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2) a : ℝ)
def CB2_5_1I2S2_2_0E_2LogWitness : LogWitness := ⟨-1, 444957, 250000⟩
def CB2_5_1I2S2_2_0E_2Log : Ball := ⟨(-583152250691689478453229215219 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma CB2_5_1I2S2_2_0E_2Log_sound : CB2_5_1I2S2_2_0E_2Log.Encloses (Real.log (CB2_5_1I2S2_2_0Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_5_1Little_sound (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2)) (2 : Fin 6)) (w := CB2_5_1I2S2_2_0E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_5_1I2S2_2_0E_2 : Ball := ⟨(1297388380055110376320567559581 / 12500000000000000000000000000000), (7537864783 / 20000000000000000000000000000000)⟩
lemma CB2_5_1I2S2_2_0E_2_sound : CB2_5_1I2S2_2_0E_2.Encloses (Foundation.entropyTerm (CB2_5_1I2S2_2_0Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_5_1Little_sound (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2)) (2 : Fin 6)) CB2_5_1I2S2_2_0E_2Log_sound) (by decide +kernel)
def CB2_5_1I2S2_2_0E_3LogWitness : LogWitness := ⟨-4, 55043, 31250⟩
def CB2_5_1I2S2_2_0E_3Log : Ball := ⟨(-22064934004685379356673449299827 / 10000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma CB2_5_1I2S2_2_0E_3Log_sound : CB2_5_1I2S2_2_0E_3Log.Encloses (Real.log (CB2_5_1I2S2_2_0Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_5_1Little_sound (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2)) (3 : Fin 6)) (w := CB2_5_1I2S2_2_0E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_5_1I2S2_2_0E_3 : Ball := ⟨(1518150203024871669911720837263 / 6250000000000000000000000000000), (11655808631 / 100000000000000000000000000000000)⟩
lemma CB2_5_1I2S2_2_0E_3_sound : CB2_5_1I2S2_2_0E_3.Encloses (Foundation.entropyTerm (CB2_5_1I2S2_2_0Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_5_1Little_sound (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2)) (3 : Fin 6)) CB2_5_1I2S2_2_0E_3Log_sound) (by decide +kernel)
def CB2_5_1I2S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(1297388380055110376320567559581 / 12500000000000000000000000000000), (7537864783 / 20000000000000000000000000000000)⟩
  | 3 => ⟨(1518150203024871669911720837263 / 6250000000000000000000000000000), (11655808631 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB2_5_1I2S2_2_0Terms_sound (a : Fin 6) :
    (CB2_5_1I2S2_2_0Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I2S2_2_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2)) (1 : Fin 6)))
  · exact CB2_5_1I2S2_2_0E_2_sound
  · exact CB2_5_1I2S2_2_0E_3_sound
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_5_1Little_sound (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2)) (5 : Fin 6)))
def CB2_5_1I2S2_2_0Entropy : Ball := ⟨(4333688786104853716144009234107 / 12500000000000000000000000000000), (24672566273 / 50000000000000000000000000000000)⟩
lemma CB2_5_1I2S2_2_0Entropy_sound : CB2_5_1I2S2_2_0Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I2S2_2_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_5_1I2S2_2_0Value CB2_5_1I2S2_2_0Terms CB2_5_1I2S2_2_0Terms_sound) (by decide +kernel)
def CB2_5_1I2S2_2_0Mass : Ball := ⟨1, 0⟩
lemma CB2_5_1I2S2_2_0Mass_sound : CB2_5_1I2S2_2_0Mass.Encloses (∑ a, CB2_5_1I2S2_2_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_5_1Little (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2)) CB2_5_1I2S2_2_0Value (B2_5_1Little_sound (shape 2 2 0) ((stageBPriority (shape 2 5 1)) 2))) (by decide +kernel)
def CB2_5_1I2S2_2_0MassTermLog : Ball := .exact 0
lemma CB2_5_1I2S2_2_0MassTermLog_sound : CB2_5_1I2S2_2_0MassTermLog.Encloses (Real.log ((∑ a, CB2_5_1I2S2_2_0Value a))) := by
  exact log_exact_one_ball (CB2_5_1I2S2_2_0Mass_sound)
def CB2_5_1I2S2_2_0MassTerm : Ball := ⟨0, 0⟩
lemma CB2_5_1I2S2_2_0MassTerm_sound : CB2_5_1I2S2_2_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I2S2_2_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_5_1I2S2_2_0Mass_sound) CB2_5_1I2S2_2_0MassTermLog_sound) (by decide +kernel)
def CB2_5_1I2S2_2_0H : Ball := ⟨(4333688786104853716144009234107 / 12500000000000000000000000000000), (24672566273 / 50000000000000000000000000000000)⟩
lemma CB2_5_1I2S2_2_0H_sound : CB2_5_1I2S2_2_0H.Encloses (homogeneousEntropy CB2_5_1I2S2_2_0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I2S2_2_0Value CB2_5_1I2S2_2_0MassTerm_sound CB2_5_1I2S2_2_0Entropy_sound) (by decide +kernel)
def CB2_5_1I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => CB2_5_1I2S0_3_1H
  | 0, 4, 0 => CB2_5_1I2S0_4_0H
  | 1, 3, 0 => CB2_5_1I2S1_3_0H
  | 2, 2, 0 => CB2_5_1I2S2_2_0H
  | _, _, _ => (.exact 0)
lemma CB2_5_1I2Singles_sound (u : Shape) (hu : u ∈ below (shape 2 5 1))
    (hd : designated (stageBPriority (shape 2 5 1)) 2 u) :
    (CB2_5_1I2Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) u)) := by
  rw [B2_5_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact CB2_5_1I2S0_3_1H_sound
  · exact CB2_5_1I2S0_4_0H_sound
  · exact (show ¬ designated (stageBPriority (shape 2 5 1)) 2 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact CB2_5_1I2S1_3_0H_sound
  · exact (show ¬ designated (stageBPriority (shape 2 5 1)) 2 (shape 2 1 1) by decide +kernel) hd |>.elim
  · exact CB2_5_1I2S2_2_0H_sound
def CB2_5_1I2Singleton : Ball := ⟨(770458991825735733780541157757 / 12500000000000000000000000000000), (8772757573 / 100000000000000000000000000000000)⟩
lemma CB2_5_1I2Singleton_sound : CB2_5_1I2Singleton.Encloses
    (singletonEntropy (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2
    CB2_5_1I2Singles (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ)) (fun u _ => B2_5_1Law_sound u) CB2_5_1I2Singles_sound) (by decide +kernel)
def CB2_5_1I2Group : Ball := ⟨(6912941347646796393825341225573 / 100000000000000000000000000000000), (51705574047 / 100000000000000000000000000000000)⟩
lemma CB2_5_1I2Group_sound : CB2_5_1I2Group.Encloses
    (groupedEntropy (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (stageBPriority (shape 2 5 1)) 2 (fun u a => (littleLaw (shape 2 5 1) u ((stageBPriority (shape 2 5 1)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB2_5_1I2Singleton_sound
    (finSumBall_sound 17 CB2_5_1I2ResidualEntropies _ CB2_5_1I2ResidualEntropies_sound)) (by decide +kernel)

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
def CB2_5_1I2H : Ball := ⟨(40055444030287900426894750871547 / 50000000000000000000000000000000), (193423618701 / 100000000000000000000000000000000)⟩
lemma CB2_5_1I2_sound : CB2_5_1I2H.Encloses (stageBCapacity (shape 2 5 1) 2) := by
  have hb := contains_sound (Ball.add_sound CB2_5_1I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB2_5_1I2Group_sound)))
    (show contains (.add CB2_5_1I2PairH (.neg (.mul (.exact 2) CB2_5_1I2Group))) CB2_5_1I2H = true by decide +kernel)
  simp only [stageBCapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg]
  exact hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
