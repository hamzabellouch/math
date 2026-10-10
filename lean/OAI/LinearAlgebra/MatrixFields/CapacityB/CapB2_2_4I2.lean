import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal2_2_4

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_2_4I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 2 2 4)) (shape 2 2 4) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) a
def CB2_2_4I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) a
lemma CB2_2_4I2PairRaw_sound (a : PairSlot) :
    (CB2_2_4I2PairRaw a).Encloses (CB2_2_4I2PairValue a) := by
  exact pairLawBall_sound_on (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) (fun u _ a => B2_2_4Little_sound (complement (shape 2 2 4) u) ((stageBPriority (shape 2 2 4)) 2) a) a
def CB2_2_4I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(186547899184436920742962037689 / 100000000000000000000000000000000), (32863847 / 50000000000000000000000000000000)⟩ ⟨(-841415254123273786972146125285279 / 100000000000000000000000000000000), (37057692009 / 12500000000000000000000000000000)⟩ ⟨-13, 22170729407421252075742212347, 12207031250000000000000000000⟩,
   .log ⟨(1877555123344146106224953559491 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(4860812523784326097575945646473 / 25000000000000000000000000000000), (7951755343 / 100000000000000000000000000000000)⟩ ⟨(-64722634016819814007605771245177 / 25000000000000000000000000000000), (2646977969 / 2500000000000000000000000000000)⟩ ⟨-4, 1877555123344146106224953559491, 1562500000000000000000000000000⟩,
   .log ⟨(1563542695666112973568998103859 / 2000000000000000000000000000000), (149 / 100000000000000000000000000000000)⟩ ⟨(19246661410204724567784176178127 / 100000000000000000000000000000000), (3310930463 / 10000000000000000000000000000000)⟩ ⟨(-24619297526768346836114256638117 / 100000000000000000000000000000000), (10587911889 / 25000000000000000000000000000000)⟩ ⟨-1, 1563542695666112973568998103859, 1000000000000000000000000000000⟩,
   .log ⟨(3219564442457119163781284689913 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(11062179065454635648473424295103 / 100000000000000000000000000000000), (1022653947 / 25000000000000000000000000000000)⟩ ⟨(-171796205094937635297027933365763 / 50000000000000000000000000000000), (127054942439 / 100000000000000000000000000000000)⟩ ⟨-5, 3219564442457119163781284689913, 3125000000000000000000000000000⟩,
   .log ⟨(79738471553025410009103131651 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(916654161094279129134379324297 / 50000000000000000000000000000000), (33770557 / 5000000000000000000000000000000)⟩ ⟨(-574787892996363653174845283243279 / 100000000000000000000000000000000), (211758237457 / 100000000000000000000000000000000)⟩ ⟨-9, 79738471553025410009103131651, 48828125000000000000000000000⟩]
lemma CB2_2_4I2PairCertificates_valid :
    CB2_2_4I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 0 => 1
  | 4, 1 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 1, 4 => 2
  | 0, 5 => 1
  | _, _ => 0
def CB2_2_4I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2PairCertificates (CB2_2_4I2PairCertificateIndex a)).input
lemma CB2_2_4I2PairP_check : ∀ a : PairSlot, contains (CB2_2_4I2PairRaw a) (CB2_2_4I2PairP a) = true := by
  decide +kernel
lemma CB2_2_4I2PairP_sound (a : PairSlot) :
    (CB2_2_4I2PairP a).Encloses (CB2_2_4I2PairValue a) :=
  contains_sound (CB2_2_4I2PairRaw_sound a) (CB2_2_4I2PairP_check a)
def CB2_2_4I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2PairCertificates (CB2_2_4I2PairCertificateIndex a)).output
lemma CB2_2_4I2PairTerms_sound (a : PairSlot) :
    (CB2_2_4I2PairTerms a).Encloses (Foundation.entropyTerm (CB2_2_4I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2PairCertificates_valid
    (CB2_2_4I2PairCertificateIndex a) (CB2_2_4I2PairP_sound a)
def CB2_2_4I2PairEntropy : Ball := ⟨(82463923851946036745093272664089 / 100000000000000000000000000000000), (2900045671 / 5000000000000000000000000000000)⟩
lemma CB2_2_4I2PairEntropy_sound : CB2_2_4I2PairEntropy.Encloses (Foundation.finiteEntropy CB2_2_4I2PairValue) := by
  exact contains_sound (entropyPair_enclosed CB2_2_4I2PairValue CB2_2_4I2PairTerms CB2_2_4I2PairTerms_sound) (by decide +kernel)
def CB2_2_4I2PairMass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (227 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I2PairMass_sound : CB2_2_4I2PairMass.Encloses (∑ a, CB2_2_4I2PairValue a) := by
  exact contains_sound (pairSumBall_sound CB2_2_4I2PairP CB2_2_4I2PairValue CB2_2_4I2PairP_sound) (by decide +kernel)
def CB2_2_4I2PairMassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB2_2_4I2PairMassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (21175823909 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I2PairMassTermLog_sound : CB2_2_4I2PairMassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_2_4I2PairMass_sound) (w := CB2_2_4I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I2PairMassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (2117582391 / 10000000000000000000000000000000)⟩
lemma CB2_2_4I2PairMassTerm_sound : CB2_2_4I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I2PairMass_sound) CB2_2_4I2PairMassTermLog_sound) (by decide +kernel)
def CB2_2_4I2PairH : Ball := ⟨(82463923851946036745093272664091 / 100000000000000000000000000000000), (7917673733 / 10000000000000000000000000000000)⟩
lemma CB2_2_4I2PairH_sound : CB2_2_4I2PairH.Encloses (homogeneousEntropy CB2_2_4I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2PairValue CB2_2_4I2PairMassTerm_sound CB2_2_4I2PairEntropy_sound) (by decide +kernel)

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
def CB2_2_4I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 0 a
def CB2_2_4I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 0 a
lemma CB2_2_4I2R0Raw_sound (a : Fin 6) :
    (CB2_2_4I2R0Raw a).Encloses (CB2_2_4I2R0Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 0 a
def CB2_2_4I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(186547899184436920742962037689 / 100000000000000000000000000000000), (32863847 / 50000000000000000000000000000000)⟩ ⟨(-841415254123273786972146125285279 / 100000000000000000000000000000000), (37057692009 / 12500000000000000000000000000000)⟩ ⟨-13, 22170729407421252075742212347, 12207031250000000000000000000⟩]
lemma CB2_2_4I2R0Certificates_valid :
    CB2_2_4I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB2_2_4I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R0Certificates (CB2_2_4I2R0CertificateIndex a)).input
lemma CB2_2_4I2R0P_check : ∀ a : Fin 6, contains (CB2_2_4I2R0Raw a) (CB2_2_4I2R0P a) = true := by
  decide +kernel
lemma CB2_2_4I2R0P_sound (a : Fin 6) :
    (CB2_2_4I2R0P a).Encloses (CB2_2_4I2R0Value a) :=
  contains_sound (CB2_2_4I2R0Raw_sound a) (CB2_2_4I2R0P_check a)
def CB2_2_4I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R0Certificates (CB2_2_4I2R0CertificateIndex a)).output
lemma CB2_2_4I2R0Terms_sound (a : Fin 6) :
    (CB2_2_4I2R0Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R0Certificates_valid
    (CB2_2_4I2R0CertificateIndex a) (CB2_2_4I2R0P_sound a)
def CB2_2_4I2R0Entropy : Ball := ⟨(186547899184436920742962037689 / 100000000000000000000000000000000), (32863847 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I2R0Entropy_sound : CB2_2_4I2R0Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R0Value CB2_2_4I2R0Terms CB2_2_4I2R0Terms_sound) (by decide +kernel)
def CB2_2_4I2R0Mass : Ball := ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I2R0Mass_sound : CB2_2_4I2R0Mass.Encloses (∑ a, CB2_2_4I2R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R0P CB2_2_4I2R0Value CB2_2_4I2R0P_sound) (by decide +kernel)
def CB2_2_4I2R0MassTermLogWitness : LogWitness := ⟨-13, 22170729407421252075742212347, 12207031250000000000000000000⟩
def CB2_2_4I2R0MassTermLog : Ball := ⟨(-841415254123273786972146125285279 / 100000000000000000000000000000000), (37057692009 / 12500000000000000000000000000000)⟩
lemma CB2_2_4I2R0MassTermLog_sound : CB2_2_4I2R0MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_2_4I2R0Mass_sound) (w := CB2_2_4I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I2R0MassTerm : Ball := ⟨(186547899184436920742962037689 / 100000000000000000000000000000000), (32863847 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I2R0MassTerm_sound : CB2_2_4I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I2R0Mass_sound) CB2_2_4I2R0MassTermLog_sound) (by decide +kernel)
def CB2_2_4I2R0H : Ball := ⟨0, (32863847 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I2R0H_sound : CB2_2_4I2R0H.Encloses (homogeneousEntropy CB2_2_4I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R0Value CB2_2_4I2R0MassTerm_sound CB2_2_4I2R0Entropy_sound) (by decide +kernel)
def CB2_2_4I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 1 a
def CB2_2_4I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 1 a
lemma CB2_2_4I2R1Raw_sound (a : Fin 6) :
    (CB2_2_4I2R1Raw a).Encloses (CB2_2_4I2R1Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 1 a
def CB2_2_4I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1877555123344146106224953559491 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(4860812523784326097575945646473 / 25000000000000000000000000000000), (7951755343 / 100000000000000000000000000000000)⟩ ⟨(-64722634016819814007605771245177 / 25000000000000000000000000000000), (2646977969 / 2500000000000000000000000000000)⟩ ⟨-4, 1877555123344146106224953559491, 1562500000000000000000000000000⟩]
lemma CB2_2_4I2R1Certificates_valid :
    CB2_2_4I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_2_4I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R1Certificates (CB2_2_4I2R1CertificateIndex a)).input
lemma CB2_2_4I2R1P_check : ∀ a : Fin 6, contains (CB2_2_4I2R1Raw a) (CB2_2_4I2R1P a) = true := by
  decide +kernel
lemma CB2_2_4I2R1P_sound (a : Fin 6) :
    (CB2_2_4I2R1P a).Encloses (CB2_2_4I2R1Value a) :=
  contains_sound (CB2_2_4I2R1Raw_sound a) (CB2_2_4I2R1P_check a)
def CB2_2_4I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R1Certificates (CB2_2_4I2R1CertificateIndex a)).output
lemma CB2_2_4I2R1Terms_sound (a : Fin 6) :
    (CB2_2_4I2R1Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R1Certificates_valid
    (CB2_2_4I2R1CertificateIndex a) (CB2_2_4I2R1P_sound a)
def CB2_2_4I2R1Entropy : Ball := ⟨(4860812523784326097575945646473 / 25000000000000000000000000000000), (7951755343 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I2R1Entropy_sound : CB2_2_4I2R1Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R1Value CB2_2_4I2R1Terms CB2_2_4I2R1Terms_sound) (by decide +kernel)
def CB2_2_4I2R1Mass : Ball := ⟨(1877555123344146106224953559491 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I2R1Mass_sound : CB2_2_4I2R1Mass.Encloses (∑ a, CB2_2_4I2R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R1P CB2_2_4I2R1Value CB2_2_4I2R1P_sound) (by decide +kernel)
def CB2_2_4I2R1MassTermLogWitness : LogWitness := ⟨-4, 1877555123344146106224953559491, 1562500000000000000000000000000⟩
def CB2_2_4I2R1MassTermLog : Ball := ⟨(-64722634016819814007605771245177 / 25000000000000000000000000000000), (2646977969 / 2500000000000000000000000000000)⟩
lemma CB2_2_4I2R1MassTermLog_sound : CB2_2_4I2R1MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_2_4I2R1Mass_sound) (w := CB2_2_4I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I2R1MassTerm : Ball := ⟨(4860812523784326097575945646473 / 25000000000000000000000000000000), (7951755343 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I2R1MassTerm_sound : CB2_2_4I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I2R1Mass_sound) CB2_2_4I2R1MassTermLog_sound) (by decide +kernel)
def CB2_2_4I2R1H : Ball := ⟨0, (7951755343 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I2R1H_sound : CB2_2_4I2R1H.Encloses (homogeneousEntropy CB2_2_4I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R1Value CB2_2_4I2R1MassTerm_sound CB2_2_4I2R1Entropy_sound) (by decide +kernel)
def CB2_2_4I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 2 a
def CB2_2_4I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 2 a
lemma CB2_2_4I2R2Raw_sound (a : Fin 6) :
    (CB2_2_4I2R2Raw a).Encloses (CB2_2_4I2R2Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 2 a
def CB2_2_4I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(55121373521289581568511787388219 / 100000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩ ⟨(4104011159699762125739736531073 / 12500000000000000000000000000000), (5836202459 / 25000000000000000000000000000000)⟩ ⟨(-29781632042348624815869460699111 / 50000000000000000000000000000000), (42351647477 / 100000000000000000000000000000000)⟩ ⟨-1, 55121373521289581568511787388219, 50000000000000000000000000000000⟩,
   .log ⟨(502786785008629530120537585437 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2661129417891119099712379167569 / 100000000000000000000000000000000), (191644639 / 20000000000000000000000000000000)⟩ ⟨(-33079745446241256546737430347809 / 6250000000000000000000000000000), (38116482669 / 20000000000000000000000000000000)⟩ ⟨-8, 502786785008629530120537585437, 390625000000000000000000000000⟩]
lemma CB2_2_4I2R2Certificates_valid :
    CB2_2_4I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_2_4I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R2Certificates (CB2_2_4I2R2CertificateIndex a)).input
lemma CB2_2_4I2R2P_check : ∀ a : Fin 6, contains (CB2_2_4I2R2Raw a) (CB2_2_4I2R2P a) = true := by
  decide +kernel
lemma CB2_2_4I2R2P_sound (a : Fin 6) :
    (CB2_2_4I2R2P a).Encloses (CB2_2_4I2R2Value a) :=
  contains_sound (CB2_2_4I2R2Raw_sound a) (CB2_2_4I2R2P_check a)
def CB2_2_4I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R2Certificates (CB2_2_4I2R2CertificateIndex a)).output
lemma CB2_2_4I2R2Terms_sound (a : Fin 6) :
    (CB2_2_4I2R2Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R2Certificates_valid
    (CB2_2_4I2R2CertificateIndex a) (CB2_2_4I2R2P_sound a)
def CB2_2_4I2R2Entropy : Ball := ⟨(35493218695489216105630271416153 / 100000000000000000000000000000000), (24303033031 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I2R2Entropy_sound : CB2_2_4I2R2Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R2Value CB2_2_4I2R2Terms CB2_2_4I2R2Terms_sound) (by decide +kernel)
def CB2_2_4I2R2Mass : Ball := ⟨(6953020038287276387329040621707 / 12500000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I2R2Mass_sound : CB2_2_4I2R2Mass.Encloses (∑ a, CB2_2_4I2R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R2P CB2_2_4I2R2Value CB2_2_4I2R2P_sound) (by decide +kernel)
def CB2_2_4I2R2MassTermLogWitness : LogWitness := ⟨-1, 6953020038287276387329040621707, 6250000000000000000000000000000⟩
def CB2_2_4I2R2MassTermLog : Ball := ⟨(-14663813530818446743036588603247 / 25000000000000000000000000000000), (42351647479 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I2R2MassTermLog_sound : CB2_2_4I2R2MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_2_4I2R2Mass_sound) (w := CB2_2_4I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I2R2MassTerm : Ball := ⟨(16313246290798201299195114300737 / 50000000000000000000000000000000), (5889437081 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I2R2MassTerm_sound : CB2_2_4I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I2R2Mass_sound) CB2_2_4I2R2MassTermLog_sound) (by decide +kernel)
def CB2_2_4I2R2H : Ball := ⟨(2866726113892813507240042814679 / 100000000000000000000000000000000), (9572156271 / 20000000000000000000000000000000)⟩
lemma CB2_2_4I2R2H_sound : CB2_2_4I2R2H.Encloses (homogeneousEntropy CB2_2_4I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R2Value CB2_2_4I2R2MassTerm_sound CB2_2_4I2R2Entropy_sound) (by decide +kernel)
def CB2_2_4I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 3 a
def CB2_2_4I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 3 a
lemma CB2_2_4I2R3Raw_sound (a : Fin 6) :
    (CB2_2_4I2R3Raw a).Encloses (CB2_2_4I2R3Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 3 a
def CB2_2_4I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R3Certificates_valid :
    CB2_2_4I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R3Certificates (CB2_2_4I2R3CertificateIndex a)).input
lemma CB2_2_4I2R3P_check : ∀ a : Fin 6, contains (CB2_2_4I2R3Raw a) (CB2_2_4I2R3P a) = true := by
  decide +kernel
lemma CB2_2_4I2R3P_sound (a : Fin 6) :
    (CB2_2_4I2R3P a).Encloses (CB2_2_4I2R3Value a) :=
  contains_sound (CB2_2_4I2R3Raw_sound a) (CB2_2_4I2R3P_check a)
def CB2_2_4I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R3Certificates (CB2_2_4I2R3CertificateIndex a)).output
lemma CB2_2_4I2R3Terms_sound (a : Fin 6) :
    (CB2_2_4I2R3Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R3Certificates_valid
    (CB2_2_4I2R3CertificateIndex a) (CB2_2_4I2R3P_sound a)
def CB2_2_4I2R3Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R3Entropy_sound : CB2_2_4I2R3Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R3Value CB2_2_4I2R3Terms CB2_2_4I2R3Terms_sound) (by decide +kernel)
def CB2_2_4I2R3Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R3Mass_sound : CB2_2_4I2R3Mass.Encloses (∑ a, CB2_2_4I2R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R3P CB2_2_4I2R3Value CB2_2_4I2R3P_sound) (by decide +kernel)
def CB2_2_4I2R3MassTerm : Ball := .exact 0
lemma CB2_2_4I2R3MassTerm_sound : CB2_2_4I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R3Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R3Mass_sound)
def CB2_2_4I2R3H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R3H_sound : CB2_2_4I2R3H.Encloses (homogeneousEntropy CB2_2_4I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R3Value CB2_2_4I2R3MassTerm_sound CB2_2_4I2R3Entropy_sound) (by decide +kernel)
def CB2_2_4I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 4 a
def CB2_2_4I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 4 a
lemma CB2_2_4I2R4Raw_sound (a : Fin 6) :
    (CB2_2_4I2R4Raw a).Encloses (CB2_2_4I2R4Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 4 a
def CB2_2_4I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R4Certificates_valid :
    CB2_2_4I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R4Certificates (CB2_2_4I2R4CertificateIndex a)).input
lemma CB2_2_4I2R4P_check : ∀ a : Fin 6, contains (CB2_2_4I2R4Raw a) (CB2_2_4I2R4P a) = true := by
  decide +kernel
lemma CB2_2_4I2R4P_sound (a : Fin 6) :
    (CB2_2_4I2R4P a).Encloses (CB2_2_4I2R4Value a) :=
  contains_sound (CB2_2_4I2R4Raw_sound a) (CB2_2_4I2R4P_check a)
def CB2_2_4I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R4Certificates (CB2_2_4I2R4CertificateIndex a)).output
lemma CB2_2_4I2R4Terms_sound (a : Fin 6) :
    (CB2_2_4I2R4Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R4Certificates_valid
    (CB2_2_4I2R4CertificateIndex a) (CB2_2_4I2R4P_sound a)
def CB2_2_4I2R4Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R4Entropy_sound : CB2_2_4I2R4Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R4Value CB2_2_4I2R4Terms CB2_2_4I2R4Terms_sound) (by decide +kernel)
def CB2_2_4I2R4Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R4Mass_sound : CB2_2_4I2R4Mass.Encloses (∑ a, CB2_2_4I2R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R4P CB2_2_4I2R4Value CB2_2_4I2R4P_sound) (by decide +kernel)
def CB2_2_4I2R4MassTerm : Ball := .exact 0
lemma CB2_2_4I2R4MassTerm_sound : CB2_2_4I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R4Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R4Mass_sound)
def CB2_2_4I2R4H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R4H_sound : CB2_2_4I2R4H.Encloses (homogeneousEntropy CB2_2_4I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R4Value CB2_2_4I2R4MassTerm_sound CB2_2_4I2R4Entropy_sound) (by decide +kernel)
def CB2_2_4I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 5 a
def CB2_2_4I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 5 a
lemma CB2_2_4I2R5Raw_sound (a : Fin 6) :
    (CB2_2_4I2R5Raw a).Encloses (CB2_2_4I2R5Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 5 a
def CB2_2_4I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R5Certificates_valid :
    CB2_2_4I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R5Certificates (CB2_2_4I2R5CertificateIndex a)).input
lemma CB2_2_4I2R5P_check : ∀ a : Fin 6, contains (CB2_2_4I2R5Raw a) (CB2_2_4I2R5P a) = true := by
  decide +kernel
lemma CB2_2_4I2R5P_sound (a : Fin 6) :
    (CB2_2_4I2R5P a).Encloses (CB2_2_4I2R5Value a) :=
  contains_sound (CB2_2_4I2R5Raw_sound a) (CB2_2_4I2R5P_check a)
def CB2_2_4I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R5Certificates (CB2_2_4I2R5CertificateIndex a)).output
lemma CB2_2_4I2R5Terms_sound (a : Fin 6) :
    (CB2_2_4I2R5Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R5Certificates_valid
    (CB2_2_4I2R5CertificateIndex a) (CB2_2_4I2R5P_sound a)
def CB2_2_4I2R5Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R5Entropy_sound : CB2_2_4I2R5Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R5Value CB2_2_4I2R5Terms CB2_2_4I2R5Terms_sound) (by decide +kernel)
def CB2_2_4I2R5Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R5Mass_sound : CB2_2_4I2R5Mass.Encloses (∑ a, CB2_2_4I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R5P CB2_2_4I2R5Value CB2_2_4I2R5P_sound) (by decide +kernel)
def CB2_2_4I2R5MassTerm : Ball := .exact 0
lemma CB2_2_4I2R5MassTerm_sound : CB2_2_4I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R5Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R5Mass_sound)
def CB2_2_4I2R5H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R5H_sound : CB2_2_4I2R5H.Encloses (homogeneousEntropy CB2_2_4I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R5Value CB2_2_4I2R5MassTerm_sound CB2_2_4I2R5Entropy_sound) (by decide +kernel)
def CB2_2_4I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 6 a
def CB2_2_4I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 6 a
lemma CB2_2_4I2R6Raw_sound (a : Fin 6) :
    (CB2_2_4I2R6Raw a).Encloses (CB2_2_4I2R6Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 6 a
def CB2_2_4I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R6Certificates_valid :
    CB2_2_4I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R6Certificates (CB2_2_4I2R6CertificateIndex a)).input
lemma CB2_2_4I2R6P_check : ∀ a : Fin 6, contains (CB2_2_4I2R6Raw a) (CB2_2_4I2R6P a) = true := by
  decide +kernel
lemma CB2_2_4I2R6P_sound (a : Fin 6) :
    (CB2_2_4I2R6P a).Encloses (CB2_2_4I2R6Value a) :=
  contains_sound (CB2_2_4I2R6Raw_sound a) (CB2_2_4I2R6P_check a)
def CB2_2_4I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R6Certificates (CB2_2_4I2R6CertificateIndex a)).output
lemma CB2_2_4I2R6Terms_sound (a : Fin 6) :
    (CB2_2_4I2R6Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R6Certificates_valid
    (CB2_2_4I2R6CertificateIndex a) (CB2_2_4I2R6P_sound a)
def CB2_2_4I2R6Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R6Entropy_sound : CB2_2_4I2R6Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R6Value CB2_2_4I2R6Terms CB2_2_4I2R6Terms_sound) (by decide +kernel)
def CB2_2_4I2R6Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R6Mass_sound : CB2_2_4I2R6Mass.Encloses (∑ a, CB2_2_4I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R6P CB2_2_4I2R6Value CB2_2_4I2R6P_sound) (by decide +kernel)
def CB2_2_4I2R6MassTerm : Ball := .exact 0
lemma CB2_2_4I2R6MassTerm_sound : CB2_2_4I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R6Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R6Mass_sound)
def CB2_2_4I2R6H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R6H_sound : CB2_2_4I2R6H.Encloses (homogeneousEntropy CB2_2_4I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R6Value CB2_2_4I2R6MassTerm_sound CB2_2_4I2R6Entropy_sound) (by decide +kernel)
def CB2_2_4I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 7 a
def CB2_2_4I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 7 a
lemma CB2_2_4I2R7Raw_sound (a : Fin 6) :
    (CB2_2_4I2R7Raw a).Encloses (CB2_2_4I2R7Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 7 a
def CB2_2_4I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R7Certificates_valid :
    CB2_2_4I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R7Certificates (CB2_2_4I2R7CertificateIndex a)).input
lemma CB2_2_4I2R7P_check : ∀ a : Fin 6, contains (CB2_2_4I2R7Raw a) (CB2_2_4I2R7P a) = true := by
  decide +kernel
lemma CB2_2_4I2R7P_sound (a : Fin 6) :
    (CB2_2_4I2R7P a).Encloses (CB2_2_4I2R7Value a) :=
  contains_sound (CB2_2_4I2R7Raw_sound a) (CB2_2_4I2R7P_check a)
def CB2_2_4I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R7Certificates (CB2_2_4I2R7CertificateIndex a)).output
lemma CB2_2_4I2R7Terms_sound (a : Fin 6) :
    (CB2_2_4I2R7Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R7Certificates_valid
    (CB2_2_4I2R7CertificateIndex a) (CB2_2_4I2R7P_sound a)
def CB2_2_4I2R7Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R7Entropy_sound : CB2_2_4I2R7Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R7Value CB2_2_4I2R7Terms CB2_2_4I2R7Terms_sound) (by decide +kernel)
def CB2_2_4I2R7Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R7Mass_sound : CB2_2_4I2R7Mass.Encloses (∑ a, CB2_2_4I2R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R7P CB2_2_4I2R7Value CB2_2_4I2R7P_sound) (by decide +kernel)
def CB2_2_4I2R7MassTerm : Ball := .exact 0
lemma CB2_2_4I2R7MassTerm_sound : CB2_2_4I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R7Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R7Mass_sound)
def CB2_2_4I2R7H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R7H_sound : CB2_2_4I2R7H.Encloses (homogeneousEntropy CB2_2_4I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R7Value CB2_2_4I2R7MassTerm_sound CB2_2_4I2R7Entropy_sound) (by decide +kernel)
def CB2_2_4I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 8 a
def CB2_2_4I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 8 a
lemma CB2_2_4I2R8Raw_sound (a : Fin 6) :
    (CB2_2_4I2R8Raw a).Encloses (CB2_2_4I2R8Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 8 a
def CB2_2_4I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R8Certificates_valid :
    CB2_2_4I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R8Certificates (CB2_2_4I2R8CertificateIndex a)).input
lemma CB2_2_4I2R8P_check : ∀ a : Fin 6, contains (CB2_2_4I2R8Raw a) (CB2_2_4I2R8P a) = true := by
  decide +kernel
lemma CB2_2_4I2R8P_sound (a : Fin 6) :
    (CB2_2_4I2R8P a).Encloses (CB2_2_4I2R8Value a) :=
  contains_sound (CB2_2_4I2R8Raw_sound a) (CB2_2_4I2R8P_check a)
def CB2_2_4I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R8Certificates (CB2_2_4I2R8CertificateIndex a)).output
lemma CB2_2_4I2R8Terms_sound (a : Fin 6) :
    (CB2_2_4I2R8Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R8Certificates_valid
    (CB2_2_4I2R8CertificateIndex a) (CB2_2_4I2R8P_sound a)
def CB2_2_4I2R8Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R8Entropy_sound : CB2_2_4I2R8Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R8Value CB2_2_4I2R8Terms CB2_2_4I2R8Terms_sound) (by decide +kernel)
def CB2_2_4I2R8Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R8Mass_sound : CB2_2_4I2R8Mass.Encloses (∑ a, CB2_2_4I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R8P CB2_2_4I2R8Value CB2_2_4I2R8P_sound) (by decide +kernel)
def CB2_2_4I2R8MassTerm : Ball := .exact 0
lemma CB2_2_4I2R8MassTerm_sound : CB2_2_4I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R8Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R8Mass_sound)
def CB2_2_4I2R8H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R8H_sound : CB2_2_4I2R8H.Encloses (homogeneousEntropy CB2_2_4I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R8Value CB2_2_4I2R8MassTerm_sound CB2_2_4I2R8Entropy_sound) (by decide +kernel)
def CB2_2_4I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 9 a
def CB2_2_4I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 9 a
lemma CB2_2_4I2R9Raw_sound (a : Fin 6) :
    (CB2_2_4I2R9Raw a).Encloses (CB2_2_4I2R9Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 9 a
def CB2_2_4I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R9Certificates_valid :
    CB2_2_4I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R9Certificates (CB2_2_4I2R9CertificateIndex a)).input
lemma CB2_2_4I2R9P_check : ∀ a : Fin 6, contains (CB2_2_4I2R9Raw a) (CB2_2_4I2R9P a) = true := by
  decide +kernel
lemma CB2_2_4I2R9P_sound (a : Fin 6) :
    (CB2_2_4I2R9P a).Encloses (CB2_2_4I2R9Value a) :=
  contains_sound (CB2_2_4I2R9Raw_sound a) (CB2_2_4I2R9P_check a)
def CB2_2_4I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R9Certificates (CB2_2_4I2R9CertificateIndex a)).output
lemma CB2_2_4I2R9Terms_sound (a : Fin 6) :
    (CB2_2_4I2R9Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R9Certificates_valid
    (CB2_2_4I2R9CertificateIndex a) (CB2_2_4I2R9P_sound a)
def CB2_2_4I2R9Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R9Entropy_sound : CB2_2_4I2R9Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R9Value CB2_2_4I2R9Terms CB2_2_4I2R9Terms_sound) (by decide +kernel)
def CB2_2_4I2R9Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R9Mass_sound : CB2_2_4I2R9Mass.Encloses (∑ a, CB2_2_4I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R9P CB2_2_4I2R9Value CB2_2_4I2R9P_sound) (by decide +kernel)
def CB2_2_4I2R9MassTerm : Ball := .exact 0
lemma CB2_2_4I2R9MassTerm_sound : CB2_2_4I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R9Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R9Mass_sound)
def CB2_2_4I2R9H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R9H_sound : CB2_2_4I2R9H.Encloses (homogeneousEntropy CB2_2_4I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R9Value CB2_2_4I2R9MassTerm_sound CB2_2_4I2R9Entropy_sound) (by decide +kernel)
def CB2_2_4I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 10 a
def CB2_2_4I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 10 a
lemma CB2_2_4I2R10Raw_sound (a : Fin 6) :
    (CB2_2_4I2R10Raw a).Encloses (CB2_2_4I2R10Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 10 a
def CB2_2_4I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R10Certificates_valid :
    CB2_2_4I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R10Certificates (CB2_2_4I2R10CertificateIndex a)).input
lemma CB2_2_4I2R10P_check : ∀ a : Fin 6, contains (CB2_2_4I2R10Raw a) (CB2_2_4I2R10P a) = true := by
  decide +kernel
lemma CB2_2_4I2R10P_sound (a : Fin 6) :
    (CB2_2_4I2R10P a).Encloses (CB2_2_4I2R10Value a) :=
  contains_sound (CB2_2_4I2R10Raw_sound a) (CB2_2_4I2R10P_check a)
def CB2_2_4I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R10Certificates (CB2_2_4I2R10CertificateIndex a)).output
lemma CB2_2_4I2R10Terms_sound (a : Fin 6) :
    (CB2_2_4I2R10Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R10Certificates_valid
    (CB2_2_4I2R10CertificateIndex a) (CB2_2_4I2R10P_sound a)
def CB2_2_4I2R10Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R10Entropy_sound : CB2_2_4I2R10Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R10Value CB2_2_4I2R10Terms CB2_2_4I2R10Terms_sound) (by decide +kernel)
def CB2_2_4I2R10Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R10Mass_sound : CB2_2_4I2R10Mass.Encloses (∑ a, CB2_2_4I2R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R10P CB2_2_4I2R10Value CB2_2_4I2R10P_sound) (by decide +kernel)
def CB2_2_4I2R10MassTerm : Ball := .exact 0
lemma CB2_2_4I2R10MassTerm_sound : CB2_2_4I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R10Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R10Mass_sound)
def CB2_2_4I2R10H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R10H_sound : CB2_2_4I2R10H.Encloses (homogeneousEntropy CB2_2_4I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R10Value CB2_2_4I2R10MassTerm_sound CB2_2_4I2R10Entropy_sound) (by decide +kernel)
def CB2_2_4I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 11 a
def CB2_2_4I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 11 a
lemma CB2_2_4I2R11Raw_sound (a : Fin 6) :
    (CB2_2_4I2R11Raw a).Encloses (CB2_2_4I2R11Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 11 a
def CB2_2_4I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R11Certificates_valid :
    CB2_2_4I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R11Certificates (CB2_2_4I2R11CertificateIndex a)).input
lemma CB2_2_4I2R11P_check : ∀ a : Fin 6, contains (CB2_2_4I2R11Raw a) (CB2_2_4I2R11P a) = true := by
  decide +kernel
lemma CB2_2_4I2R11P_sound (a : Fin 6) :
    (CB2_2_4I2R11P a).Encloses (CB2_2_4I2R11Value a) :=
  contains_sound (CB2_2_4I2R11Raw_sound a) (CB2_2_4I2R11P_check a)
def CB2_2_4I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R11Certificates (CB2_2_4I2R11CertificateIndex a)).output
lemma CB2_2_4I2R11Terms_sound (a : Fin 6) :
    (CB2_2_4I2R11Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R11Certificates_valid
    (CB2_2_4I2R11CertificateIndex a) (CB2_2_4I2R11P_sound a)
def CB2_2_4I2R11Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R11Entropy_sound : CB2_2_4I2R11Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R11Value CB2_2_4I2R11Terms CB2_2_4I2R11Terms_sound) (by decide +kernel)
def CB2_2_4I2R11Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R11Mass_sound : CB2_2_4I2R11Mass.Encloses (∑ a, CB2_2_4I2R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R11P CB2_2_4I2R11Value CB2_2_4I2R11P_sound) (by decide +kernel)
def CB2_2_4I2R11MassTerm : Ball := .exact 0
lemma CB2_2_4I2R11MassTerm_sound : CB2_2_4I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R11Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R11Mass_sound)
def CB2_2_4I2R11H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R11H_sound : CB2_2_4I2R11H.Encloses (homogeneousEntropy CB2_2_4I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R11Value CB2_2_4I2R11MassTerm_sound CB2_2_4I2R11Entropy_sound) (by decide +kernel)
def CB2_2_4I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 12 a
def CB2_2_4I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 12 a
lemma CB2_2_4I2R12Raw_sound (a : Fin 6) :
    (CB2_2_4I2R12Raw a).Encloses (CB2_2_4I2R12Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 12 a
def CB2_2_4I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R12Certificates_valid :
    CB2_2_4I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R12Certificates (CB2_2_4I2R12CertificateIndex a)).input
lemma CB2_2_4I2R12P_check : ∀ a : Fin 6, contains (CB2_2_4I2R12Raw a) (CB2_2_4I2R12P a) = true := by
  decide +kernel
lemma CB2_2_4I2R12P_sound (a : Fin 6) :
    (CB2_2_4I2R12P a).Encloses (CB2_2_4I2R12Value a) :=
  contains_sound (CB2_2_4I2R12Raw_sound a) (CB2_2_4I2R12P_check a)
def CB2_2_4I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R12Certificates (CB2_2_4I2R12CertificateIndex a)).output
lemma CB2_2_4I2R12Terms_sound (a : Fin 6) :
    (CB2_2_4I2R12Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R12Certificates_valid
    (CB2_2_4I2R12CertificateIndex a) (CB2_2_4I2R12P_sound a)
def CB2_2_4I2R12Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R12Entropy_sound : CB2_2_4I2R12Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R12Value CB2_2_4I2R12Terms CB2_2_4I2R12Terms_sound) (by decide +kernel)
def CB2_2_4I2R12Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R12Mass_sound : CB2_2_4I2R12Mass.Encloses (∑ a, CB2_2_4I2R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R12P CB2_2_4I2R12Value CB2_2_4I2R12P_sound) (by decide +kernel)
def CB2_2_4I2R12MassTerm : Ball := .exact 0
lemma CB2_2_4I2R12MassTerm_sound : CB2_2_4I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R12Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R12Mass_sound)
def CB2_2_4I2R12H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R12H_sound : CB2_2_4I2R12H.Encloses (homogeneousEntropy CB2_2_4I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R12Value CB2_2_4I2R12MassTerm_sound CB2_2_4I2R12Entropy_sound) (by decide +kernel)
def CB2_2_4I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 13 a
def CB2_2_4I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 13 a
lemma CB2_2_4I2R13Raw_sound (a : Fin 6) :
    (CB2_2_4I2R13Raw a).Encloses (CB2_2_4I2R13Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 13 a
def CB2_2_4I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R13Certificates_valid :
    CB2_2_4I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R13Certificates (CB2_2_4I2R13CertificateIndex a)).input
lemma CB2_2_4I2R13P_check : ∀ a : Fin 6, contains (CB2_2_4I2R13Raw a) (CB2_2_4I2R13P a) = true := by
  decide +kernel
lemma CB2_2_4I2R13P_sound (a : Fin 6) :
    (CB2_2_4I2R13P a).Encloses (CB2_2_4I2R13Value a) :=
  contains_sound (CB2_2_4I2R13Raw_sound a) (CB2_2_4I2R13P_check a)
def CB2_2_4I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R13Certificates (CB2_2_4I2R13CertificateIndex a)).output
lemma CB2_2_4I2R13Terms_sound (a : Fin 6) :
    (CB2_2_4I2R13Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R13Certificates_valid
    (CB2_2_4I2R13CertificateIndex a) (CB2_2_4I2R13P_sound a)
def CB2_2_4I2R13Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R13Entropy_sound : CB2_2_4I2R13Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R13Value CB2_2_4I2R13Terms CB2_2_4I2R13Terms_sound) (by decide +kernel)
def CB2_2_4I2R13Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R13Mass_sound : CB2_2_4I2R13Mass.Encloses (∑ a, CB2_2_4I2R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R13P CB2_2_4I2R13Value CB2_2_4I2R13P_sound) (by decide +kernel)
def CB2_2_4I2R13MassTerm : Ball := .exact 0
lemma CB2_2_4I2R13MassTerm_sound : CB2_2_4I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R13Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R13Mass_sound)
def CB2_2_4I2R13H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R13H_sound : CB2_2_4I2R13H.Encloses (homogeneousEntropy CB2_2_4I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R13Value CB2_2_4I2R13MassTerm_sound CB2_2_4I2R13Entropy_sound) (by decide +kernel)
def CB2_2_4I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 14 a
def CB2_2_4I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 14 a
lemma CB2_2_4I2R14Raw_sound (a : Fin 6) :
    (CB2_2_4I2R14Raw a).Encloses (CB2_2_4I2R14Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 14 a
def CB2_2_4I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R14Certificates_valid :
    CB2_2_4I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R14Certificates (CB2_2_4I2R14CertificateIndex a)).input
lemma CB2_2_4I2R14P_check : ∀ a : Fin 6, contains (CB2_2_4I2R14Raw a) (CB2_2_4I2R14P a) = true := by
  decide +kernel
lemma CB2_2_4I2R14P_sound (a : Fin 6) :
    (CB2_2_4I2R14P a).Encloses (CB2_2_4I2R14Value a) :=
  contains_sound (CB2_2_4I2R14Raw_sound a) (CB2_2_4I2R14P_check a)
def CB2_2_4I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R14Certificates (CB2_2_4I2R14CertificateIndex a)).output
lemma CB2_2_4I2R14Terms_sound (a : Fin 6) :
    (CB2_2_4I2R14Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R14Certificates_valid
    (CB2_2_4I2R14CertificateIndex a) (CB2_2_4I2R14P_sound a)
def CB2_2_4I2R14Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R14Entropy_sound : CB2_2_4I2R14Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R14Value CB2_2_4I2R14Terms CB2_2_4I2R14Terms_sound) (by decide +kernel)
def CB2_2_4I2R14Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R14Mass_sound : CB2_2_4I2R14Mass.Encloses (∑ a, CB2_2_4I2R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R14P CB2_2_4I2R14Value CB2_2_4I2R14P_sound) (by decide +kernel)
def CB2_2_4I2R14MassTerm : Ball := .exact 0
lemma CB2_2_4I2R14MassTerm_sound : CB2_2_4I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R14Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R14Mass_sound)
def CB2_2_4I2R14H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R14H_sound : CB2_2_4I2R14H.Encloses (homogeneousEntropy CB2_2_4I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R14Value CB2_2_4I2R14MassTerm_sound CB2_2_4I2R14Entropy_sound) (by decide +kernel)
def CB2_2_4I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 15 a
def CB2_2_4I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 15 a
lemma CB2_2_4I2R15Raw_sound (a : Fin 6) :
    (CB2_2_4I2R15Raw a).Encloses (CB2_2_4I2R15Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 15 a
def CB2_2_4I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R15Certificates_valid :
    CB2_2_4I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R15Certificates (CB2_2_4I2R15CertificateIndex a)).input
lemma CB2_2_4I2R15P_check : ∀ a : Fin 6, contains (CB2_2_4I2R15Raw a) (CB2_2_4I2R15P a) = true := by
  decide +kernel
lemma CB2_2_4I2R15P_sound (a : Fin 6) :
    (CB2_2_4I2R15P a).Encloses (CB2_2_4I2R15Value a) :=
  contains_sound (CB2_2_4I2R15Raw_sound a) (CB2_2_4I2R15P_check a)
def CB2_2_4I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R15Certificates (CB2_2_4I2R15CertificateIndex a)).output
lemma CB2_2_4I2R15Terms_sound (a : Fin 6) :
    (CB2_2_4I2R15Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R15Certificates_valid
    (CB2_2_4I2R15CertificateIndex a) (CB2_2_4I2R15P_sound a)
def CB2_2_4I2R15Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R15Entropy_sound : CB2_2_4I2R15Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R15Value CB2_2_4I2R15Terms CB2_2_4I2R15Terms_sound) (by decide +kernel)
def CB2_2_4I2R15Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R15Mass_sound : CB2_2_4I2R15Mass.Encloses (∑ a, CB2_2_4I2R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R15P CB2_2_4I2R15Value CB2_2_4I2R15P_sound) (by decide +kernel)
def CB2_2_4I2R15MassTerm : Ball := .exact 0
lemma CB2_2_4I2R15MassTerm_sound : CB2_2_4I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R15Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R15Mass_sound)
def CB2_2_4I2R15H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R15H_sound : CB2_2_4I2R15H.Encloses (homogeneousEntropy CB2_2_4I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R15Value CB2_2_4I2R15MassTerm_sound CB2_2_4I2R15Entropy_sound) (by decide +kernel)
def CB2_2_4I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) 16 a
def CB2_2_4I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) 16 a
lemma CB2_2_4I2R16Raw_sound (a : Fin 6) :
    (CB2_2_4I2R16Raw a).Encloses (CB2_2_4I2R16Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 16 a
def CB2_2_4I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I2R16Certificates_valid :
    CB2_2_4I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R16Certificates (CB2_2_4I2R16CertificateIndex a)).input
lemma CB2_2_4I2R16P_check : ∀ a : Fin 6, contains (CB2_2_4I2R16Raw a) (CB2_2_4I2R16P a) = true := by
  decide +kernel
lemma CB2_2_4I2R16P_sound (a : Fin 6) :
    (CB2_2_4I2R16P a).Encloses (CB2_2_4I2R16Value a) :=
  contains_sound (CB2_2_4I2R16Raw_sound a) (CB2_2_4I2R16P_check a)
def CB2_2_4I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I2R16Certificates (CB2_2_4I2R16CertificateIndex a)).output
lemma CB2_2_4I2R16Terms_sound (a : Fin 6) :
    (CB2_2_4I2R16Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I2R16Certificates_valid
    (CB2_2_4I2R16CertificateIndex a) (CB2_2_4I2R16P_sound a)
def CB2_2_4I2R16Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R16Entropy_sound : CB2_2_4I2R16Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2R16Value CB2_2_4I2R16Terms CB2_2_4I2R16Terms_sound) (by decide +kernel)
def CB2_2_4I2R16Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R16Mass_sound : CB2_2_4I2R16Mass.Encloses (∑ a, CB2_2_4I2R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I2R16P CB2_2_4I2R16Value CB2_2_4I2R16P_sound) (by decide +kernel)
def CB2_2_4I2R16MassTerm : Ball := .exact 0
lemma CB2_2_4I2R16MassTerm_sound : CB2_2_4I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2R16Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I2R16Mass_sound)
def CB2_2_4I2R16H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2R16H_sound : CB2_2_4I2R16H.Encloses (homogeneousEntropy CB2_2_4I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2R16Value CB2_2_4I2R16MassTerm_sound CB2_2_4I2R16Entropy_sound) (by decide +kernel)
def CB2_2_4I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_2_4I2R0H
  | 1 => CB2_2_4I2R1H
  | 2 => CB2_2_4I2R2H
  | 3 => CB2_2_4I2R3H
  | 4 => CB2_2_4I2R4H
  | 5 => CB2_2_4I2R5H
  | 6 => CB2_2_4I2R6H
  | 7 => CB2_2_4I2R7H
  | 8 => CB2_2_4I2R8H
  | 9 => CB2_2_4I2R9H
  | 10 => CB2_2_4I2R10H
  | 11 => CB2_2_4I2R11H
  | 12 => CB2_2_4I2R12H
  | 13 => CB2_2_4I2R13H
  | 14 => CB2_2_4I2R14H
  | 15 => CB2_2_4I2R15H
  | 16 => CB2_2_4I2R16H
  | _ => (.exact 0)
lemma CB2_2_4I2ResidualEntropies_sound (k : Fin 17) :
    (CB2_2_4I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB2_2_4I2R0H_sound
  · exact CB2_2_4I2R1H_sound
  · exact CB2_2_4I2R2H_sound
  · exact CB2_2_4I2R3H_sound
  · exact CB2_2_4I2R4H_sound
  · exact CB2_2_4I2R5H_sound
  · exact CB2_2_4I2R6H_sound
  · exact CB2_2_4I2R7H_sound
  · exact CB2_2_4I2R8H_sound
  · exact CB2_2_4I2R9H_sound
  · exact CB2_2_4I2R10H_sound
  · exact CB2_2_4I2R11H_sound
  · exact CB2_2_4I2R12H_sound
  · exact CB2_2_4I2R13H_sound
  · exact CB2_2_4I2R14H_sound
  · exact CB2_2_4I2R15H_sound
  · exact CB2_2_4I2R16H_sound
def CB2_2_4I2S0_0_4Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 0 0 4) ((stageBPriority (shape 2 2 4)) 2) a : ℝ)
def CB2_2_4I2S0_0_4E_5Log : Ball := .exact 0
lemma CB2_2_4I2S0_0_4E_5Log_sound : CB2_2_4I2S0_0_4E_5Log.Encloses (Real.log (CB2_2_4I2S0_0_4Value (5 : Fin 6))) := by
  exact log_exact_one_ball ((B2_2_4Little_sound (shape 0 0 4) ((stageBPriority (shape 2 2 4)) 2)) (5 : Fin 6))
def CB2_2_4I2S0_0_4E_5 : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S0_0_4E_5_sound : CB2_2_4I2S0_0_4E_5.Encloses (Foundation.entropyTerm (CB2_2_4I2S0_0_4Value (5 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_2_4Little_sound (shape 0 0 4) ((stageBPriority (shape 2 2 4)) 2)) (5 : Fin 6)) CB2_2_4I2S0_0_4E_5Log_sound) (by decide +kernel)
def CB2_2_4I2S0_0_4Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB2_2_4I2S0_0_4Terms_sound (a : Fin 6) :
    (CB2_2_4I2S0_0_4Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2S0_0_4Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 0 4) ((stageBPriority (shape 2 2 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 0 4) ((stageBPriority (shape 2 2 4)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 0 4) ((stageBPriority (shape 2 2 4)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 0 4) ((stageBPriority (shape 2 2 4)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 0 4) ((stageBPriority (shape 2 2 4)) 2)) (4 : Fin 6)))
  · exact CB2_2_4I2S0_0_4E_5_sound
def CB2_2_4I2S0_0_4Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S0_0_4Entropy_sound : CB2_2_4I2S0_0_4Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2S0_0_4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2S0_0_4Value CB2_2_4I2S0_0_4Terms CB2_2_4I2S0_0_4Terms_sound) (by decide +kernel)
def CB2_2_4I2S0_0_4Mass : Ball := ⟨1, 0⟩
lemma CB2_2_4I2S0_0_4Mass_sound : CB2_2_4I2S0_0_4Mass.Encloses (∑ a, CB2_2_4I2S0_0_4Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_2_4Little (shape 0 0 4) ((stageBPriority (shape 2 2 4)) 2)) CB2_2_4I2S0_0_4Value (B2_2_4Little_sound (shape 0 0 4) ((stageBPriority (shape 2 2 4)) 2))) (by decide +kernel)
def CB2_2_4I2S0_0_4MassTermLog : Ball := .exact 0
lemma CB2_2_4I2S0_0_4MassTermLog_sound : CB2_2_4I2S0_0_4MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I2S0_0_4Value a))) := by
  exact log_exact_one_ball (CB2_2_4I2S0_0_4Mass_sound)
def CB2_2_4I2S0_0_4MassTerm : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S0_0_4MassTerm_sound : CB2_2_4I2S0_0_4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2S0_0_4Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I2S0_0_4Mass_sound) CB2_2_4I2S0_0_4MassTermLog_sound) (by decide +kernel)
def CB2_2_4I2S0_0_4H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S0_0_4H_sound : CB2_2_4I2S0_0_4H.Encloses (homogeneousEntropy CB2_2_4I2S0_0_4Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2S0_0_4Value CB2_2_4I2S0_0_4MassTerm_sound CB2_2_4I2S0_0_4Entropy_sound) (by decide +kernel)
def CB2_2_4I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 0 1 3) ((stageBPriority (shape 2 2 4)) 2) a : ℝ)
def CB2_2_4I2S0_1_3E_4Log : Ball := .exact 0
lemma CB2_2_4I2S0_1_3E_4Log_sound : CB2_2_4I2S0_1_3E_4Log.Encloses (Real.log (CB2_2_4I2S0_1_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B2_2_4Little_sound (shape 0 1 3) ((stageBPriority (shape 2 2 4)) 2)) (4 : Fin 6))
def CB2_2_4I2S0_1_3E_4 : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S0_1_3E_4_sound : CB2_2_4I2S0_1_3E_4.Encloses (Foundation.entropyTerm (CB2_2_4I2S0_1_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_2_4Little_sound (shape 0 1 3) ((stageBPriority (shape 2 2 4)) 2)) (4 : Fin 6)) CB2_2_4I2S0_1_3E_4Log_sound) (by decide +kernel)
def CB2_2_4I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB2_2_4I2S0_1_3Terms_sound (a : Fin 6) :
    (CB2_2_4I2S0_1_3Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2S0_1_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 1 3) ((stageBPriority (shape 2 2 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 1 3) ((stageBPriority (shape 2 2 4)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 1 3) ((stageBPriority (shape 2 2 4)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 1 3) ((stageBPriority (shape 2 2 4)) 2)) (3 : Fin 6)))
  · exact CB2_2_4I2S0_1_3E_4_sound
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 1 3) ((stageBPriority (shape 2 2 4)) 2)) (5 : Fin 6)))
def CB2_2_4I2S0_1_3Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S0_1_3Entropy_sound : CB2_2_4I2S0_1_3Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2S0_1_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2S0_1_3Value CB2_2_4I2S0_1_3Terms CB2_2_4I2S0_1_3Terms_sound) (by decide +kernel)
def CB2_2_4I2S0_1_3Mass : Ball := ⟨1, 0⟩
lemma CB2_2_4I2S0_1_3Mass_sound : CB2_2_4I2S0_1_3Mass.Encloses (∑ a, CB2_2_4I2S0_1_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_2_4Little (shape 0 1 3) ((stageBPriority (shape 2 2 4)) 2)) CB2_2_4I2S0_1_3Value (B2_2_4Little_sound (shape 0 1 3) ((stageBPriority (shape 2 2 4)) 2))) (by decide +kernel)
def CB2_2_4I2S0_1_3MassTermLog : Ball := .exact 0
lemma CB2_2_4I2S0_1_3MassTermLog_sound : CB2_2_4I2S0_1_3MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I2S0_1_3Value a))) := by
  exact log_exact_one_ball (CB2_2_4I2S0_1_3Mass_sound)
def CB2_2_4I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S0_1_3MassTerm_sound : CB2_2_4I2S0_1_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2S0_1_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I2S0_1_3Mass_sound) CB2_2_4I2S0_1_3MassTermLog_sound) (by decide +kernel)
def CB2_2_4I2S0_1_3H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S0_1_3H_sound : CB2_2_4I2S0_1_3H.Encloses (homogeneousEntropy CB2_2_4I2S0_1_3Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2S0_1_3Value CB2_2_4I2S0_1_3MassTerm_sound CB2_2_4I2S0_1_3Entropy_sound) (by decide +kernel)
def CB2_2_4I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2) a : ℝ)
def CB2_2_4I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 448219, 250000⟩
def CB2_2_4I2S0_2_2E_2Log : Ball := ⟨(-2186522923289837780427151140763 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I2S0_2_2E_2Log_sound : CB2_2_4I2S0_2_2E_2Log.Encloses (Real.log (CB2_2_4I2S0_2_2Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_2_4Little_sound (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2)) (2 : Fin 6)) (w := CB2_2_4I2S0_2_2E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I2S0_2_2E_2 : Ball := ⟨(9800411181540478001052772571617 / 100000000000000000000000000000000), (18982813031 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I2S0_2_2E_2_sound : CB2_2_4I2S0_2_2E_2.Encloses (Foundation.entropyTerm (CB2_2_4I2S0_2_2Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_2_4Little_sound (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2)) (2 : Fin 6)) CB2_2_4I2S0_2_2E_2Log_sound) (by decide +kernel)
def CB2_2_4I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 51781, 31250⟩
def CB2_2_4I2S0_2_2E_3Log : Ball := ⟨(-226758481180942422019326103547823 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma CB2_2_4I2S0_2_2E_3Log_sound : CB2_2_4I2S0_2_2E_3Log.Encloses (Real.log (CB2_2_4I2S0_2_2Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_2_4Little_sound (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2)) (3 : Fin 6)) (w := CB2_2_4I2S0_2_2E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I2S0_2_2E_3 : Ball := ⟨(1174178091403037955458272496781 / 5000000000000000000000000000000), (5482526631 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I2S0_2_2E_3_sound : CB2_2_4I2S0_2_2E_3.Encloses (Foundation.entropyTerm (CB2_2_4I2S0_2_2Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_2_4Little_sound (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2)) (3 : Fin 6)) CB2_2_4I2S0_2_2E_3Log_sound) (by decide +kernel)
def CB2_2_4I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9800411181540478001052772571617 / 100000000000000000000000000000000), (18982813031 / 50000000000000000000000000000000)⟩
  | 3 => ⟨(1174178091403037955458272496781 / 5000000000000000000000000000000), (5482526631 / 50000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB2_2_4I2S0_2_2Terms_sound (a : Fin 6) :
    (CB2_2_4I2S0_2_2Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2S0_2_2Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2)) (1 : Fin 6)))
  · exact CB2_2_4I2S0_2_2E_2_sound
  · exact CB2_2_4I2S0_2_2E_3_sound
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2)) (5 : Fin 6)))
def CB2_2_4I2S0_2_2Entropy : Ball := ⟨(33283973009601237110218222507237 / 100000000000000000000000000000000), (12232669831 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I2S0_2_2Entropy_sound : CB2_2_4I2S0_2_2Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2S0_2_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2S0_2_2Value CB2_2_4I2S0_2_2Terms CB2_2_4I2S0_2_2Terms_sound) (by decide +kernel)
def CB2_2_4I2S0_2_2Mass : Ball := ⟨1, 0⟩
lemma CB2_2_4I2S0_2_2Mass_sound : CB2_2_4I2S0_2_2Mass.Encloses (∑ a, CB2_2_4I2S0_2_2Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_2_4Little (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2)) CB2_2_4I2S0_2_2Value (B2_2_4Little_sound (shape 0 2 2) ((stageBPriority (shape 2 2 4)) 2))) (by decide +kernel)
def CB2_2_4I2S0_2_2MassTermLog : Ball := .exact 0
lemma CB2_2_4I2S0_2_2MassTermLog_sound : CB2_2_4I2S0_2_2MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I2S0_2_2Value a))) := by
  exact log_exact_one_ball (CB2_2_4I2S0_2_2Mass_sound)
def CB2_2_4I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S0_2_2MassTerm_sound : CB2_2_4I2S0_2_2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2S0_2_2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I2S0_2_2Mass_sound) CB2_2_4I2S0_2_2MassTermLog_sound) (by decide +kernel)
def CB2_2_4I2S0_2_2H : Ball := ⟨(33283973009601237110218222507237 / 100000000000000000000000000000000), (12232669831 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I2S0_2_2H_sound : CB2_2_4I2S0_2_2H.Encloses (homogeneousEntropy CB2_2_4I2S0_2_2Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2S0_2_2Value CB2_2_4I2S0_2_2MassTerm_sound CB2_2_4I2S0_2_2Entropy_sound) (by decide +kernel)
def CB2_2_4I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 1 0 3) ((stageBPriority (shape 2 2 4)) 2) a : ℝ)
def CB2_2_4I2S1_0_3E_4Log : Ball := .exact 0
lemma CB2_2_4I2S1_0_3E_4Log_sound : CB2_2_4I2S1_0_3E_4Log.Encloses (Real.log (CB2_2_4I2S1_0_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B2_2_4Little_sound (shape 1 0 3) ((stageBPriority (shape 2 2 4)) 2)) (4 : Fin 6))
def CB2_2_4I2S1_0_3E_4 : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S1_0_3E_4_sound : CB2_2_4I2S1_0_3E_4.Encloses (Foundation.entropyTerm (CB2_2_4I2S1_0_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_2_4Little_sound (shape 1 0 3) ((stageBPriority (shape 2 2 4)) 2)) (4 : Fin 6)) CB2_2_4I2S1_0_3E_4Log_sound) (by decide +kernel)
def CB2_2_4I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB2_2_4I2S1_0_3Terms_sound (a : Fin 6) :
    (CB2_2_4I2S1_0_3Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2S1_0_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 1 0 3) ((stageBPriority (shape 2 2 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 1 0 3) ((stageBPriority (shape 2 2 4)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 1 0 3) ((stageBPriority (shape 2 2 4)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 1 0 3) ((stageBPriority (shape 2 2 4)) 2)) (3 : Fin 6)))
  · exact CB2_2_4I2S1_0_3E_4_sound
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 1 0 3) ((stageBPriority (shape 2 2 4)) 2)) (5 : Fin 6)))
def CB2_2_4I2S1_0_3Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S1_0_3Entropy_sound : CB2_2_4I2S1_0_3Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2S1_0_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2S1_0_3Value CB2_2_4I2S1_0_3Terms CB2_2_4I2S1_0_3Terms_sound) (by decide +kernel)
def CB2_2_4I2S1_0_3Mass : Ball := ⟨1, 0⟩
lemma CB2_2_4I2S1_0_3Mass_sound : CB2_2_4I2S1_0_3Mass.Encloses (∑ a, CB2_2_4I2S1_0_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_2_4Little (shape 1 0 3) ((stageBPriority (shape 2 2 4)) 2)) CB2_2_4I2S1_0_3Value (B2_2_4Little_sound (shape 1 0 3) ((stageBPriority (shape 2 2 4)) 2))) (by decide +kernel)
def CB2_2_4I2S1_0_3MassTermLog : Ball := .exact 0
lemma CB2_2_4I2S1_0_3MassTermLog_sound : CB2_2_4I2S1_0_3MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I2S1_0_3Value a))) := by
  exact log_exact_one_ball (CB2_2_4I2S1_0_3Mass_sound)
def CB2_2_4I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S1_0_3MassTerm_sound : CB2_2_4I2S1_0_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2S1_0_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I2S1_0_3Mass_sound) CB2_2_4I2S1_0_3MassTermLog_sound) (by decide +kernel)
def CB2_2_4I2S1_0_3H : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S1_0_3H_sound : CB2_2_4I2S1_0_3H.Encloses (homogeneousEntropy CB2_2_4I2S1_0_3Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2S1_0_3Value CB2_2_4I2S1_0_3MassTerm_sound CB2_2_4I2S1_0_3Entropy_sound) (by decide +kernel)
def CB2_2_4I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2) a : ℝ)
def CB2_2_4I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 896423, 500000⟩
def CB2_2_4I2S2_0_2E_2Log : Ball := ⟨(-2733571979905550299613262420469 / 25000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma CB2_2_4I2S2_0_2E_2Log_sound : CB2_2_4I2S2_0_2E_2Log.Encloses (Real.log (CB2_2_4I2S2_0_2Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_2_4Little_sound (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2)) (2 : Fin 6)) (w := CB2_2_4I2S2_0_2E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I2S2_0_2E_2 : Ball := ⟨(306304599367859139528777442343 / 3125000000000000000000000000000), (37964990787 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I2S2_0_2E_2_sound : CB2_2_4I2S2_0_2E_2.Encloses (Foundation.entropyTerm (CB2_2_4I2S2_0_2Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_2_4Little_sound (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2)) (2 : Fin 6)) CB2_2_4I2S2_0_2E_2Log_sound) (by decide +kernel)
def CB2_2_4I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 103577, 62500⟩
def CB2_2_4I2S2_0_2E_3Log : Ball := ⟨(-2834299976907655511632457381399 / 1250000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I2S2_0_2E_3Log_sound : CB2_2_4I2S2_0_2E_3Log.Encloses (Real.log (CB2_2_4I2S2_0_2Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_2_4Little_sound (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2)) (3 : Fin 6)) (w := CB2_2_4I2S2_0_2E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I2S2_0_2E_3 : Ball := ⟨(23485463096653138794268403055453 / 100000000000000000000000000000000), (10966641449 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I2S2_0_2E_3_sound : CB2_2_4I2S2_0_2E_3.Encloses (Foundation.entropyTerm (CB2_2_4I2S2_0_2Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_2_4Little_sound (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2)) (3 : Fin 6)) CB2_2_4I2S2_0_2E_3Log_sound) (by decide +kernel)
def CB2_2_4I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(306304599367859139528777442343 / 3125000000000000000000000000000), (37964990787 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(23485463096653138794268403055453 / 100000000000000000000000000000000), (10966641449 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB2_2_4I2S2_0_2Terms_sound (a : Fin 6) :
    (CB2_2_4I2S2_0_2Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I2S2_0_2Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2)) (1 : Fin 6)))
  · exact CB2_2_4I2S2_0_2E_2_sound
  · exact CB2_2_4I2S2_0_2E_3_sound
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2)) (5 : Fin 6)))
def CB2_2_4I2S2_0_2Entropy : Ball := ⟨(33287210276424631259189281210429 / 100000000000000000000000000000000), (12232908059 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I2S2_0_2Entropy_sound : CB2_2_4I2S2_0_2Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I2S2_0_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I2S2_0_2Value CB2_2_4I2S2_0_2Terms CB2_2_4I2S2_0_2Terms_sound) (by decide +kernel)
def CB2_2_4I2S2_0_2Mass : Ball := ⟨1, 0⟩
lemma CB2_2_4I2S2_0_2Mass_sound : CB2_2_4I2S2_0_2Mass.Encloses (∑ a, CB2_2_4I2S2_0_2Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_2_4Little (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2)) CB2_2_4I2S2_0_2Value (B2_2_4Little_sound (shape 2 0 2) ((stageBPriority (shape 2 2 4)) 2))) (by decide +kernel)
def CB2_2_4I2S2_0_2MassTermLog : Ball := .exact 0
lemma CB2_2_4I2S2_0_2MassTermLog_sound : CB2_2_4I2S2_0_2MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I2S2_0_2Value a))) := by
  exact log_exact_one_ball (CB2_2_4I2S2_0_2Mass_sound)
def CB2_2_4I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
lemma CB2_2_4I2S2_0_2MassTerm_sound : CB2_2_4I2S2_0_2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I2S2_0_2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I2S2_0_2Mass_sound) CB2_2_4I2S2_0_2MassTermLog_sound) (by decide +kernel)
def CB2_2_4I2S2_0_2H : Ball := ⟨(33287210276424631259189281210429 / 100000000000000000000000000000000), (12232908059 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I2S2_0_2H_sound : CB2_2_4I2S2_0_2H.Encloses (homogeneousEntropy CB2_2_4I2S2_0_2Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I2S2_0_2Value CB2_2_4I2S2_0_2MassTerm_sound CB2_2_4I2S2_0_2Entropy_sound) (by decide +kernel)
def CB2_2_4I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => CB2_2_4I2S0_0_4H
  | 0, 1, 3 => CB2_2_4I2S0_1_3H
  | 0, 2, 2 => CB2_2_4I2S0_2_2H
  | 1, 0, 3 => CB2_2_4I2S1_0_3H
  | 2, 0, 2 => CB2_2_4I2S2_0_2H
  | _, _, _ => (.exact 0)
lemma CB2_2_4I2Singles_sound (u : Shape) (hu : u ∈ below (shape 2 2 4))
    (hd : designated (stageBPriority (shape 2 2 4)) 2 u) :
    (CB2_2_4I2Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) u)) := by
  rw [B2_2_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CB2_2_4I2S0_0_4H_sound
  · exact CB2_2_4I2S0_1_3H_sound
  · exact CB2_2_4I2S0_2_2H_sound
  · exact CB2_2_4I2S1_0_3H_sound
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 2 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 2 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact CB2_2_4I2S2_0_2H_sound
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 2 (shape 2 1 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 2 (shape 2 2 0) by decide +kernel) hd |>.elim
def CB2_2_4I2Singleton : Ball := ⟨(9756358821863553579066193634899 / 100000000000000000000000000000000), (179277989 / 1250000000000000000000000000000)⟩
lemma CB2_2_4I2Singleton_sound : CB2_2_4I2Singleton.Encloses
    (singletonEntropy (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2
    CB2_2_4I2Singles (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) CB2_2_4I2Singles_sound) (by decide +kernel)
def CB2_2_4I2Group : Ball := ⟨(6311542467878183543153118224789 / 50000000000000000000000000000000), (78237986549 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I2Group_sound : CB2_2_4I2Group.Encloses
    (groupedEntropy (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB2_2_4I2Singleton_sound
    (finSumBall_sound 17 CB2_2_4I2ResidualEntropies _ CB2_2_4I2ResidualEntropies_sound)) (by decide +kernel)

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
def CB2_2_4I2H : Ball := ⟨(11443550796086660514496159952987 / 20000000000000000000000000000000), (58913177607 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I2_sound : CB2_2_4I2H.Encloses (stageBCapacity (shape 2 2 4) 2) := by
  have hb := contains_sound (Ball.add_sound CB2_2_4I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB2_2_4I2Group_sound)))
    (show contains (.add CB2_2_4I2PairH (.neg (.mul (.exact 2) CB2_2_4I2Group))) CB2_2_4I2H = true by decide +kernel)
  unfold CB2_2_4I2PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
