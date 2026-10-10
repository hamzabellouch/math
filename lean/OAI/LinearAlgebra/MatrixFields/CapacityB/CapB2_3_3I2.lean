import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB2_3_3

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_3_3I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 2 3 3)) (shape 2 3 3) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) a
def CB2_3_3I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) a
lemma CB2_3_3I2PairRaw_sound (a : PairSlot) :
    (CB2_3_3I2PairRaw a).Encloses (CB2_3_3I2PairValue a) := by
  exact pairLawBall_sound_on (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) (fun u _ a => B2_3_3Little_sound (complement (shape 2 3 3) u) ((stageBPriority (shape 2 3 3)) 2) a) a
def CB2_3_3I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(163911127094417036878035098501 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(710416976898713047679469856213 / 12500000000000000000000000000000), (2221410029 / 100000000000000000000000000000000)⟩ ⟨(-108353988757806318051603335024857 / 25000000000000000000000000000000), (33881317969 / 20000000000000000000000000000000)⟩ ⟨-7, 163911127094417036878035098501, 97656250000000000000000000000⟩,
   .log ⟨(46643247536423404746233613795319 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩ ⟨(4446512544749424295078479601311 / 12500000000000000000000000000000), (29631275637 / 100000000000000000000000000000000)⟩ ⟨(-38132100825759801047955625284901 / 50000000000000000000000000000000), (15881867781 / 25000000000000000000000000000000)⟩ ⟨-2, 46643247536423404746233613795319, 25000000000000000000000000000000⟩,
   .log ⟨(2045463446821258958742105416673 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1591184750829993068331186632661 / 20000000000000000000000000000000), (1516003073 / 50000000000000000000000000000000)⟩ ⟨(-388954579780627427050574663024177 / 100000000000000000000000000000000), (148230765927 / 100000000000000000000000000000000)⟩ ⟨-6, 2045463446821258958742105416673, 1562500000000000000000000000000⟩]
lemma CB2_3_3I2PairCertificates_valid :
    CB2_3_3I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CB2_3_3I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2PairCertificates (CB2_3_3I2PairCertificateIndex a)).input
lemma CB2_3_3I2PairP_check : ∀ a : PairSlot, contains (CB2_3_3I2PairRaw a) (CB2_3_3I2PairP a) = true := by
  decide +kernel
lemma CB2_3_3I2PairP_sound (a : PairSlot) :
    (CB2_3_3I2PairP a).Encloses (CB2_3_3I2PairValue a) :=
  contains_sound (CB2_3_3I2PairRaw_sound a) (CB2_3_3I2PairP_check a)
def CB2_3_3I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2PairCertificates (CB2_3_3I2PairCertificateIndex a)).output
lemma CB2_3_3I2PairTerms_sound (a : PairSlot) :
    (CB2_3_3I2PairTerms a).Encloses (Foundation.entropyTerm (CB2_3_3I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2PairCertificates_valid
    (CB2_3_3I2PairCertificateIndex a) (CB2_3_3I2PairP_sound a)
def CB2_3_3I2PairEntropy : Ball := ⟨(49211359927335064083719528823497 / 50000000000000000000000000000000), (8721172953 / 12500000000000000000000000000000)⟩
lemma CB2_3_3I2PairEntropy_sound : CB2_3_3I2PairEntropy.Encloses (Foundation.finiteEntropy CB2_3_3I2PairValue) := by
  exact contains_sound (entropyPair_enclosed CB2_3_3I2PairValue CB2_3_3I2PairTerms CB2_3_3I2PairTerms_sound) (by decide +kernel)
def CB2_3_3I2PairMass : Ball := ⟨1, (43 / 50000000000000000000000000000000)⟩
lemma CB2_3_3I2PairMass_sound : CB2_3_3I2PairMass.Encloses (∑ a, CB2_3_3I2PairValue a) := by
  exact contains_sound (pairSumBall_sound CB2_3_3I2PairP CB2_3_3I2PairValue CB2_3_3I2PairP_sound) (by decide +kernel)
def CB2_3_3I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_3_3I2PairMassTermLog : Ball := ⟨0, (2646977971 / 12500000000000000000000000000000)⟩
lemma CB2_3_3I2PairMassTermLog_sound : CB2_3_3I2PairMassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_3_3I2PairMass_sound) (w := CB2_3_3I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_3_3I2PairMassTerm : Ball := ⟨0, (21175823769 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2PairMassTerm_sound : CB2_3_3I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I2PairMass_sound) CB2_3_3I2PairMassTermLog_sound) (by decide +kernel)
def CB2_3_3I2PairH : Ball := ⟨(49211359927335064083719528823497 / 50000000000000000000000000000000), (90945207393 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2PairH_sound : CB2_3_3I2PairH.Encloses (homogeneousEntropy CB2_3_3I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2PairValue CB2_3_3I2PairMassTerm_sound CB2_3_3I2PairEntropy_sound) (by decide +kernel)

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
def CB2_3_3I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 0 a
def CB2_3_3I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 0 a
lemma CB2_3_3I2R0Raw_sound (a : Fin 6) :
    (CB2_3_3I2R0Raw a).Encloses (CB2_3_3I2R0Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 0 a
def CB2_3_3I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(163911127094417036878035098501 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(710416976898713047679469856213 / 12500000000000000000000000000000), (2221410029 / 100000000000000000000000000000000)⟩ ⟨(-108353988757806318051603335024857 / 25000000000000000000000000000000), (33881317969 / 20000000000000000000000000000000)⟩ ⟨-7, 163911127094417036878035098501, 97656250000000000000000000000⟩]
lemma CB2_3_3I2R0Certificates_valid :
    CB2_3_3I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB2_3_3I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R0Certificates (CB2_3_3I2R0CertificateIndex a)).input
lemma CB2_3_3I2R0P_check : ∀ a : Fin 6, contains (CB2_3_3I2R0Raw a) (CB2_3_3I2R0P a) = true := by
  decide +kernel
lemma CB2_3_3I2R0P_sound (a : Fin 6) :
    (CB2_3_3I2R0P a).Encloses (CB2_3_3I2R0Value a) :=
  contains_sound (CB2_3_3I2R0Raw_sound a) (CB2_3_3I2R0P_check a)
def CB2_3_3I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R0Certificates (CB2_3_3I2R0CertificateIndex a)).output
lemma CB2_3_3I2R0Terms_sound (a : Fin 6) :
    (CB2_3_3I2R0Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R0Certificates_valid
    (CB2_3_3I2R0CertificateIndex a) (CB2_3_3I2R0P_sound a)
def CB2_3_3I2R0Entropy : Ball := ⟨(710416976898713047679469856213 / 12500000000000000000000000000000), (2221410029 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2R0Entropy_sound : CB2_3_3I2R0Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R0Value CB2_3_3I2R0Terms CB2_3_3I2R0Terms_sound) (by decide +kernel)
def CB2_3_3I2R0Mass : Ball := ⟨(163911127094417036878035098501 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma CB2_3_3I2R0Mass_sound : CB2_3_3I2R0Mass.Encloses (∑ a, CB2_3_3I2R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R0P CB2_3_3I2R0Value CB2_3_3I2R0P_sound) (by decide +kernel)
def CB2_3_3I2R0MassTermLogWitness : LogWitness := ⟨-7, 163911127094417036878035098501, 97656250000000000000000000000⟩
def CB2_3_3I2R0MassTermLog : Ball := ⟨(-108353988757806318051603335024857 / 25000000000000000000000000000000), (33881317969 / 20000000000000000000000000000000)⟩
lemma CB2_3_3I2R0MassTermLog_sound : CB2_3_3I2R0MassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_3_3I2R0Mass_sound) (w := CB2_3_3I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_3_3I2R0MassTerm : Ball := ⟨(710416976898713047679469856213 / 12500000000000000000000000000000), (2221410029 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2R0MassTerm_sound : CB2_3_3I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I2R0Mass_sound) CB2_3_3I2R0MassTermLog_sound) (by decide +kernel)
def CB2_3_3I2R0H : Ball := ⟨0, (2221410029 / 50000000000000000000000000000000)⟩
lemma CB2_3_3I2R0H_sound : CB2_3_3I2R0H.Encloses (homogeneousEntropy CB2_3_3I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R0Value CB2_3_3I2R0MassTerm_sound CB2_3_3I2R0Entropy_sound) (by decide +kernel)
def CB2_3_3I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 1 a
def CB2_3_3I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 1 a
lemma CB2_3_3I2R1Raw_sound (a : Fin 6) :
    (CB2_3_3I2R1Raw a).Encloses (CB2_3_3I2R1Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 1 a
def CB2_3_3I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(23763436341818321284544175804257 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩ ⟨(35354047389686535436129562195663 / 100000000000000000000000000000000), (30192620343 / 100000000000000000000000000000000)⟩ ⟨(-74387489421029854998168788216519 / 100000000000000000000000000000000), (31763735559 / 50000000000000000000000000000000)⟩ ⟨-2, 23763436341818321284544175804257, 12500000000000000000000000000000⟩]
lemma CB2_3_3I2R1Certificates_valid :
    CB2_3_3I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_3_3I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R1Certificates (CB2_3_3I2R1CertificateIndex a)).input
lemma CB2_3_3I2R1P_check : ∀ a : Fin 6, contains (CB2_3_3I2R1Raw a) (CB2_3_3I2R1P a) = true := by
  decide +kernel
lemma CB2_3_3I2R1P_sound (a : Fin 6) :
    (CB2_3_3I2R1P a).Encloses (CB2_3_3I2R1Value a) :=
  contains_sound (CB2_3_3I2R1Raw_sound a) (CB2_3_3I2R1P_check a)
def CB2_3_3I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R1Certificates (CB2_3_3I2R1CertificateIndex a)).output
lemma CB2_3_3I2R1Terms_sound (a : Fin 6) :
    (CB2_3_3I2R1Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R1Certificates_valid
    (CB2_3_3I2R1CertificateIndex a) (CB2_3_3I2R1P_sound a)
def CB2_3_3I2R1Entropy : Ball := ⟨(35354047389686535436129562195663 / 100000000000000000000000000000000), (30192620343 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2R1Entropy_sound : CB2_3_3I2R1Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R1Value CB2_3_3I2R1Terms CB2_3_3I2R1Terms_sound) (by decide +kernel)
def CB2_3_3I2R1Mass : Ball := ⟨(23763436341818321284544175804257 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2R1Mass_sound : CB2_3_3I2R1Mass.Encloses (∑ a, CB2_3_3I2R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R1P CB2_3_3I2R1Value CB2_3_3I2R1P_sound) (by decide +kernel)
def CB2_3_3I2R1MassTermLogWitness : LogWitness := ⟨-2, 23763436341818321284544175804257, 12500000000000000000000000000000⟩
def CB2_3_3I2R1MassTermLog : Ball := ⟨(-74387489421029854998168788216519 / 100000000000000000000000000000000), (31763735559 / 50000000000000000000000000000000)⟩
lemma CB2_3_3I2R1MassTermLog_sound : CB2_3_3I2R1MassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_3_3I2R1Mass_sound) (w := CB2_3_3I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_3_3I2R1MassTerm : Ball := ⟨(35354047389686535436129562195663 / 100000000000000000000000000000000), (30192620343 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2R1MassTerm_sound : CB2_3_3I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I2R1Mass_sound) CB2_3_3I2R1MassTermLog_sound) (by decide +kernel)
def CB2_3_3I2R1H : Ball := ⟨0, (30192620343 / 50000000000000000000000000000000)⟩
lemma CB2_3_3I2R1H_sound : CB2_3_3I2R1H.Encloses (homogeneousEntropy CB2_3_3I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R1Value CB2_3_3I2R1MassTerm_sound CB2_3_3I2R1Entropy_sound) (by decide +kernel)
def CB2_3_3I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 2 a
def CB2_3_3I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 2 a
lemma CB2_3_3I2R2Raw_sound (a : Fin 6) :
    (CB2_3_3I2R2Raw a).Encloses (CB2_3_3I2R2Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 2 a
def CB2_3_3I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(31205955344773960444357789426907 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(1453649833270426393629439063227 / 4000000000000000000000000000000), (9912177139 / 50000000000000000000000000000000)⟩ ⟨(-116456123295218080574198913066799 / 100000000000000000000000000000000), (63527471093 / 100000000000000000000000000000000)⟩ ⟨-2, 31205955344773960444357789426907, 25000000000000000000000000000000⟩,
   .log ⟨(35926712876938846340860531359 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(940582898251429604961959637733 / 100000000000000000000000000000000), (334742213 / 100000000000000000000000000000000)⟩ ⟨(-654514999377513635457181126009841 / 100000000000000000000000000000000), (232934061209 / 100000000000000000000000000000000)⟩ ⟨-10, 35926712876938846340860531359, 24414062500000000000000000000⟩]
lemma CB2_3_3I2R2Certificates_valid :
    CB2_3_3I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_3_3I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R2Certificates (CB2_3_3I2R2CertificateIndex a)).input
lemma CB2_3_3I2R2P_check : ∀ a : Fin 6, contains (CB2_3_3I2R2Raw a) (CB2_3_3I2R2P a) = true := by
  decide +kernel
lemma CB2_3_3I2R2P_sound (a : Fin 6) :
    (CB2_3_3I2R2P a).Encloses (CB2_3_3I2R2Value a) :=
  contains_sound (CB2_3_3I2R2Raw_sound a) (CB2_3_3I2R2P_check a)
def CB2_3_3I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R2Certificates (CB2_3_3I2R2CertificateIndex a)).output
lemma CB2_3_3I2R2Terms_sound (a : Fin 6) :
    (CB2_3_3I2R2Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R2Certificates_valid
    (CB2_3_3I2R2CertificateIndex a) (CB2_3_3I2R2P_sound a)
def CB2_3_3I2R2Entropy : Ball := ⟨(4660228591251511180712242027301 / 12500000000000000000000000000000), (20159096491 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2R2Entropy_sound : CB2_3_3I2R2Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R2Value CB2_3_3I2R2Terms CB2_3_3I2R2Terms_sound) (by decide +kernel)
def CB2_3_3I2R2Mass : Ball := ⟨(31349662196281715829721231552343 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
lemma CB2_3_3I2R2Mass_sound : CB2_3_3I2R2Mass.Encloses (∑ a, CB2_3_3I2R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R2P CB2_3_3I2R2Value CB2_3_3I2R2P_sound) (by decide +kernel)
def CB2_3_3I2R2MassTermLogWitness : LogWitness := ⟨-2, 31349662196281715829721231552343, 25000000000000000000000000000000⟩
def CB2_3_3I2R2MassTermLog : Ball := ⟨(-115996669420543774296075561313107 / 100000000000000000000000000000000), (7940933887 / 12500000000000000000000000000000)⟩
lemma CB2_3_3I2R2MassTermLog_sound : CB2_3_3I2R2MassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_3_3I2R2Mass_sound) (w := CB2_3_3I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_3_3I2R2MassTerm : Ball := ⟨(9091141005569521211958861081541 / 25000000000000000000000000000000), (2489455951 / 12500000000000000000000000000000)⟩
lemma CB2_3_3I2R2MassTerm_sound : CB2_3_3I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I2R2Mass_sound) CB2_3_3I2R2MassTermLog_sound) (by decide +kernel)
def CB2_3_3I2R2H : Ball := ⟨(229316176933501149465622973061 / 25000000000000000000000000000000), (40074744099 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2R2H_sound : CB2_3_3I2R2H.Encloses (homogeneousEntropy CB2_3_3I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R2Value CB2_3_3I2R2MassTerm_sound CB2_3_3I2R2Entropy_sound) (by decide +kernel)
def CB2_3_3I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 3 a
def CB2_3_3I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 3 a
lemma CB2_3_3I2R3Raw_sound (a : Fin 6) :
    (CB2_3_3I2R3Raw a).Encloses (CB2_3_3I2R3Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 3 a
def CB2_3_3I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R3Certificates_valid :
    CB2_3_3I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R3Certificates (CB2_3_3I2R3CertificateIndex a)).input
lemma CB2_3_3I2R3P_check : ∀ a : Fin 6, contains (CB2_3_3I2R3Raw a) (CB2_3_3I2R3P a) = true := by
  decide +kernel
lemma CB2_3_3I2R3P_sound (a : Fin 6) :
    (CB2_3_3I2R3P a).Encloses (CB2_3_3I2R3Value a) :=
  contains_sound (CB2_3_3I2R3Raw_sound a) (CB2_3_3I2R3P_check a)
def CB2_3_3I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R3Certificates (CB2_3_3I2R3CertificateIndex a)).output
lemma CB2_3_3I2R3Terms_sound (a : Fin 6) :
    (CB2_3_3I2R3Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R3Certificates_valid
    (CB2_3_3I2R3CertificateIndex a) (CB2_3_3I2R3P_sound a)
def CB2_3_3I2R3Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R3Entropy_sound : CB2_3_3I2R3Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R3Value CB2_3_3I2R3Terms CB2_3_3I2R3Terms_sound) (by decide +kernel)
def CB2_3_3I2R3Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R3Mass_sound : CB2_3_3I2R3Mass.Encloses (∑ a, CB2_3_3I2R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R3P CB2_3_3I2R3Value CB2_3_3I2R3P_sound) (by decide +kernel)
def CB2_3_3I2R3MassTerm : Ball := .exact 0
lemma CB2_3_3I2R3MassTerm_sound : CB2_3_3I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R3Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R3Mass_sound)
def CB2_3_3I2R3H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R3H_sound : CB2_3_3I2R3H.Encloses (homogeneousEntropy CB2_3_3I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R3Value CB2_3_3I2R3MassTerm_sound CB2_3_3I2R3Entropy_sound) (by decide +kernel)
def CB2_3_3I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 4 a
def CB2_3_3I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 4 a
lemma CB2_3_3I2R4Raw_sound (a : Fin 6) :
    (CB2_3_3I2R4Raw a).Encloses (CB2_3_3I2R4Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 4 a
def CB2_3_3I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R4Certificates_valid :
    CB2_3_3I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R4Certificates (CB2_3_3I2R4CertificateIndex a)).input
lemma CB2_3_3I2R4P_check : ∀ a : Fin 6, contains (CB2_3_3I2R4Raw a) (CB2_3_3I2R4P a) = true := by
  decide +kernel
lemma CB2_3_3I2R4P_sound (a : Fin 6) :
    (CB2_3_3I2R4P a).Encloses (CB2_3_3I2R4Value a) :=
  contains_sound (CB2_3_3I2R4Raw_sound a) (CB2_3_3I2R4P_check a)
def CB2_3_3I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R4Certificates (CB2_3_3I2R4CertificateIndex a)).output
lemma CB2_3_3I2R4Terms_sound (a : Fin 6) :
    (CB2_3_3I2R4Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R4Certificates_valid
    (CB2_3_3I2R4CertificateIndex a) (CB2_3_3I2R4P_sound a)
def CB2_3_3I2R4Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R4Entropy_sound : CB2_3_3I2R4Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R4Value CB2_3_3I2R4Terms CB2_3_3I2R4Terms_sound) (by decide +kernel)
def CB2_3_3I2R4Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R4Mass_sound : CB2_3_3I2R4Mass.Encloses (∑ a, CB2_3_3I2R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R4P CB2_3_3I2R4Value CB2_3_3I2R4P_sound) (by decide +kernel)
def CB2_3_3I2R4MassTerm : Ball := .exact 0
lemma CB2_3_3I2R4MassTerm_sound : CB2_3_3I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R4Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R4Mass_sound)
def CB2_3_3I2R4H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R4H_sound : CB2_3_3I2R4H.Encloses (homogeneousEntropy CB2_3_3I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R4Value CB2_3_3I2R4MassTerm_sound CB2_3_3I2R4Entropy_sound) (by decide +kernel)
def CB2_3_3I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 5 a
def CB2_3_3I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 5 a
lemma CB2_3_3I2R5Raw_sound (a : Fin 6) :
    (CB2_3_3I2R5Raw a).Encloses (CB2_3_3I2R5Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 5 a
def CB2_3_3I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R5Certificates_valid :
    CB2_3_3I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R5Certificates (CB2_3_3I2R5CertificateIndex a)).input
lemma CB2_3_3I2R5P_check : ∀ a : Fin 6, contains (CB2_3_3I2R5Raw a) (CB2_3_3I2R5P a) = true := by
  decide +kernel
lemma CB2_3_3I2R5P_sound (a : Fin 6) :
    (CB2_3_3I2R5P a).Encloses (CB2_3_3I2R5Value a) :=
  contains_sound (CB2_3_3I2R5Raw_sound a) (CB2_3_3I2R5P_check a)
def CB2_3_3I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R5Certificates (CB2_3_3I2R5CertificateIndex a)).output
lemma CB2_3_3I2R5Terms_sound (a : Fin 6) :
    (CB2_3_3I2R5Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R5Certificates_valid
    (CB2_3_3I2R5CertificateIndex a) (CB2_3_3I2R5P_sound a)
def CB2_3_3I2R5Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R5Entropy_sound : CB2_3_3I2R5Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R5Value CB2_3_3I2R5Terms CB2_3_3I2R5Terms_sound) (by decide +kernel)
def CB2_3_3I2R5Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R5Mass_sound : CB2_3_3I2R5Mass.Encloses (∑ a, CB2_3_3I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R5P CB2_3_3I2R5Value CB2_3_3I2R5P_sound) (by decide +kernel)
def CB2_3_3I2R5MassTerm : Ball := .exact 0
lemma CB2_3_3I2R5MassTerm_sound : CB2_3_3I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R5Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R5Mass_sound)
def CB2_3_3I2R5H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R5H_sound : CB2_3_3I2R5H.Encloses (homogeneousEntropy CB2_3_3I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R5Value CB2_3_3I2R5MassTerm_sound CB2_3_3I2R5Entropy_sound) (by decide +kernel)
def CB2_3_3I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 6 a
def CB2_3_3I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 6 a
lemma CB2_3_3I2R6Raw_sound (a : Fin 6) :
    (CB2_3_3I2R6Raw a).Encloses (CB2_3_3I2R6Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 6 a
def CB2_3_3I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R6Certificates_valid :
    CB2_3_3I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R6Certificates (CB2_3_3I2R6CertificateIndex a)).input
lemma CB2_3_3I2R6P_check : ∀ a : Fin 6, contains (CB2_3_3I2R6Raw a) (CB2_3_3I2R6P a) = true := by
  decide +kernel
lemma CB2_3_3I2R6P_sound (a : Fin 6) :
    (CB2_3_3I2R6P a).Encloses (CB2_3_3I2R6Value a) :=
  contains_sound (CB2_3_3I2R6Raw_sound a) (CB2_3_3I2R6P_check a)
def CB2_3_3I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R6Certificates (CB2_3_3I2R6CertificateIndex a)).output
lemma CB2_3_3I2R6Terms_sound (a : Fin 6) :
    (CB2_3_3I2R6Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R6Certificates_valid
    (CB2_3_3I2R6CertificateIndex a) (CB2_3_3I2R6P_sound a)
def CB2_3_3I2R6Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R6Entropy_sound : CB2_3_3I2R6Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R6Value CB2_3_3I2R6Terms CB2_3_3I2R6Terms_sound) (by decide +kernel)
def CB2_3_3I2R6Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R6Mass_sound : CB2_3_3I2R6Mass.Encloses (∑ a, CB2_3_3I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R6P CB2_3_3I2R6Value CB2_3_3I2R6P_sound) (by decide +kernel)
def CB2_3_3I2R6MassTerm : Ball := .exact 0
lemma CB2_3_3I2R6MassTerm_sound : CB2_3_3I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R6Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R6Mass_sound)
def CB2_3_3I2R6H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R6H_sound : CB2_3_3I2R6H.Encloses (homogeneousEntropy CB2_3_3I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R6Value CB2_3_3I2R6MassTerm_sound CB2_3_3I2R6Entropy_sound) (by decide +kernel)
def CB2_3_3I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 7 a
def CB2_3_3I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 7 a
lemma CB2_3_3I2R7Raw_sound (a : Fin 6) :
    (CB2_3_3I2R7Raw a).Encloses (CB2_3_3I2R7Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 7 a
def CB2_3_3I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R7Certificates_valid :
    CB2_3_3I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R7Certificates (CB2_3_3I2R7CertificateIndex a)).input
lemma CB2_3_3I2R7P_check : ∀ a : Fin 6, contains (CB2_3_3I2R7Raw a) (CB2_3_3I2R7P a) = true := by
  decide +kernel
lemma CB2_3_3I2R7P_sound (a : Fin 6) :
    (CB2_3_3I2R7P a).Encloses (CB2_3_3I2R7Value a) :=
  contains_sound (CB2_3_3I2R7Raw_sound a) (CB2_3_3I2R7P_check a)
def CB2_3_3I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R7Certificates (CB2_3_3I2R7CertificateIndex a)).output
lemma CB2_3_3I2R7Terms_sound (a : Fin 6) :
    (CB2_3_3I2R7Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R7Certificates_valid
    (CB2_3_3I2R7CertificateIndex a) (CB2_3_3I2R7P_sound a)
def CB2_3_3I2R7Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R7Entropy_sound : CB2_3_3I2R7Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R7Value CB2_3_3I2R7Terms CB2_3_3I2R7Terms_sound) (by decide +kernel)
def CB2_3_3I2R7Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R7Mass_sound : CB2_3_3I2R7Mass.Encloses (∑ a, CB2_3_3I2R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R7P CB2_3_3I2R7Value CB2_3_3I2R7P_sound) (by decide +kernel)
def CB2_3_3I2R7MassTerm : Ball := .exact 0
lemma CB2_3_3I2R7MassTerm_sound : CB2_3_3I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R7Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R7Mass_sound)
def CB2_3_3I2R7H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R7H_sound : CB2_3_3I2R7H.Encloses (homogeneousEntropy CB2_3_3I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R7Value CB2_3_3I2R7MassTerm_sound CB2_3_3I2R7Entropy_sound) (by decide +kernel)
def CB2_3_3I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 8 a
def CB2_3_3I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 8 a
lemma CB2_3_3I2R8Raw_sound (a : Fin 6) :
    (CB2_3_3I2R8Raw a).Encloses (CB2_3_3I2R8Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 8 a
def CB2_3_3I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R8Certificates_valid :
    CB2_3_3I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R8Certificates (CB2_3_3I2R8CertificateIndex a)).input
lemma CB2_3_3I2R8P_check : ∀ a : Fin 6, contains (CB2_3_3I2R8Raw a) (CB2_3_3I2R8P a) = true := by
  decide +kernel
lemma CB2_3_3I2R8P_sound (a : Fin 6) :
    (CB2_3_3I2R8P a).Encloses (CB2_3_3I2R8Value a) :=
  contains_sound (CB2_3_3I2R8Raw_sound a) (CB2_3_3I2R8P_check a)
def CB2_3_3I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R8Certificates (CB2_3_3I2R8CertificateIndex a)).output
lemma CB2_3_3I2R8Terms_sound (a : Fin 6) :
    (CB2_3_3I2R8Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R8Certificates_valid
    (CB2_3_3I2R8CertificateIndex a) (CB2_3_3I2R8P_sound a)
def CB2_3_3I2R8Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R8Entropy_sound : CB2_3_3I2R8Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R8Value CB2_3_3I2R8Terms CB2_3_3I2R8Terms_sound) (by decide +kernel)
def CB2_3_3I2R8Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R8Mass_sound : CB2_3_3I2R8Mass.Encloses (∑ a, CB2_3_3I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R8P CB2_3_3I2R8Value CB2_3_3I2R8P_sound) (by decide +kernel)
def CB2_3_3I2R8MassTerm : Ball := .exact 0
lemma CB2_3_3I2R8MassTerm_sound : CB2_3_3I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R8Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R8Mass_sound)
def CB2_3_3I2R8H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R8H_sound : CB2_3_3I2R8H.Encloses (homogeneousEntropy CB2_3_3I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R8Value CB2_3_3I2R8MassTerm_sound CB2_3_3I2R8Entropy_sound) (by decide +kernel)
def CB2_3_3I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 9 a
def CB2_3_3I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 9 a
lemma CB2_3_3I2R9Raw_sound (a : Fin 6) :
    (CB2_3_3I2R9Raw a).Encloses (CB2_3_3I2R9Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 9 a
def CB2_3_3I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R9Certificates_valid :
    CB2_3_3I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R9Certificates (CB2_3_3I2R9CertificateIndex a)).input
lemma CB2_3_3I2R9P_check : ∀ a : Fin 6, contains (CB2_3_3I2R9Raw a) (CB2_3_3I2R9P a) = true := by
  decide +kernel
lemma CB2_3_3I2R9P_sound (a : Fin 6) :
    (CB2_3_3I2R9P a).Encloses (CB2_3_3I2R9Value a) :=
  contains_sound (CB2_3_3I2R9Raw_sound a) (CB2_3_3I2R9P_check a)
def CB2_3_3I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R9Certificates (CB2_3_3I2R9CertificateIndex a)).output
lemma CB2_3_3I2R9Terms_sound (a : Fin 6) :
    (CB2_3_3I2R9Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R9Certificates_valid
    (CB2_3_3I2R9CertificateIndex a) (CB2_3_3I2R9P_sound a)
def CB2_3_3I2R9Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R9Entropy_sound : CB2_3_3I2R9Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R9Value CB2_3_3I2R9Terms CB2_3_3I2R9Terms_sound) (by decide +kernel)
def CB2_3_3I2R9Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R9Mass_sound : CB2_3_3I2R9Mass.Encloses (∑ a, CB2_3_3I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R9P CB2_3_3I2R9Value CB2_3_3I2R9P_sound) (by decide +kernel)
def CB2_3_3I2R9MassTerm : Ball := .exact 0
lemma CB2_3_3I2R9MassTerm_sound : CB2_3_3I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R9Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R9Mass_sound)
def CB2_3_3I2R9H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R9H_sound : CB2_3_3I2R9H.Encloses (homogeneousEntropy CB2_3_3I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R9Value CB2_3_3I2R9MassTerm_sound CB2_3_3I2R9Entropy_sound) (by decide +kernel)
def CB2_3_3I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 10 a
def CB2_3_3I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 10 a
lemma CB2_3_3I2R10Raw_sound (a : Fin 6) :
    (CB2_3_3I2R10Raw a).Encloses (CB2_3_3I2R10Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 10 a
def CB2_3_3I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R10Certificates_valid :
    CB2_3_3I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R10Certificates (CB2_3_3I2R10CertificateIndex a)).input
lemma CB2_3_3I2R10P_check : ∀ a : Fin 6, contains (CB2_3_3I2R10Raw a) (CB2_3_3I2R10P a) = true := by
  decide +kernel
lemma CB2_3_3I2R10P_sound (a : Fin 6) :
    (CB2_3_3I2R10P a).Encloses (CB2_3_3I2R10Value a) :=
  contains_sound (CB2_3_3I2R10Raw_sound a) (CB2_3_3I2R10P_check a)
def CB2_3_3I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R10Certificates (CB2_3_3I2R10CertificateIndex a)).output
lemma CB2_3_3I2R10Terms_sound (a : Fin 6) :
    (CB2_3_3I2R10Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R10Certificates_valid
    (CB2_3_3I2R10CertificateIndex a) (CB2_3_3I2R10P_sound a)
def CB2_3_3I2R10Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R10Entropy_sound : CB2_3_3I2R10Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R10Value CB2_3_3I2R10Terms CB2_3_3I2R10Terms_sound) (by decide +kernel)
def CB2_3_3I2R10Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R10Mass_sound : CB2_3_3I2R10Mass.Encloses (∑ a, CB2_3_3I2R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R10P CB2_3_3I2R10Value CB2_3_3I2R10P_sound) (by decide +kernel)
def CB2_3_3I2R10MassTerm : Ball := .exact 0
lemma CB2_3_3I2R10MassTerm_sound : CB2_3_3I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R10Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R10Mass_sound)
def CB2_3_3I2R10H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R10H_sound : CB2_3_3I2R10H.Encloses (homogeneousEntropy CB2_3_3I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R10Value CB2_3_3I2R10MassTerm_sound CB2_3_3I2R10Entropy_sound) (by decide +kernel)
def CB2_3_3I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 11 a
def CB2_3_3I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 11 a
lemma CB2_3_3I2R11Raw_sound (a : Fin 6) :
    (CB2_3_3I2R11Raw a).Encloses (CB2_3_3I2R11Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 11 a
def CB2_3_3I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R11Certificates_valid :
    CB2_3_3I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R11Certificates (CB2_3_3I2R11CertificateIndex a)).input
lemma CB2_3_3I2R11P_check : ∀ a : Fin 6, contains (CB2_3_3I2R11Raw a) (CB2_3_3I2R11P a) = true := by
  decide +kernel
lemma CB2_3_3I2R11P_sound (a : Fin 6) :
    (CB2_3_3I2R11P a).Encloses (CB2_3_3I2R11Value a) :=
  contains_sound (CB2_3_3I2R11Raw_sound a) (CB2_3_3I2R11P_check a)
def CB2_3_3I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R11Certificates (CB2_3_3I2R11CertificateIndex a)).output
lemma CB2_3_3I2R11Terms_sound (a : Fin 6) :
    (CB2_3_3I2R11Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R11Certificates_valid
    (CB2_3_3I2R11CertificateIndex a) (CB2_3_3I2R11P_sound a)
def CB2_3_3I2R11Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R11Entropy_sound : CB2_3_3I2R11Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R11Value CB2_3_3I2R11Terms CB2_3_3I2R11Terms_sound) (by decide +kernel)
def CB2_3_3I2R11Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R11Mass_sound : CB2_3_3I2R11Mass.Encloses (∑ a, CB2_3_3I2R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R11P CB2_3_3I2R11Value CB2_3_3I2R11P_sound) (by decide +kernel)
def CB2_3_3I2R11MassTerm : Ball := .exact 0
lemma CB2_3_3I2R11MassTerm_sound : CB2_3_3I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R11Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R11Mass_sound)
def CB2_3_3I2R11H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R11H_sound : CB2_3_3I2R11H.Encloses (homogeneousEntropy CB2_3_3I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R11Value CB2_3_3I2R11MassTerm_sound CB2_3_3I2R11Entropy_sound) (by decide +kernel)
def CB2_3_3I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 12 a
def CB2_3_3I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 12 a
lemma CB2_3_3I2R12Raw_sound (a : Fin 6) :
    (CB2_3_3I2R12Raw a).Encloses (CB2_3_3I2R12Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 12 a
def CB2_3_3I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R12Certificates_valid :
    CB2_3_3I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R12Certificates (CB2_3_3I2R12CertificateIndex a)).input
lemma CB2_3_3I2R12P_check : ∀ a : Fin 6, contains (CB2_3_3I2R12Raw a) (CB2_3_3I2R12P a) = true := by
  decide +kernel
lemma CB2_3_3I2R12P_sound (a : Fin 6) :
    (CB2_3_3I2R12P a).Encloses (CB2_3_3I2R12Value a) :=
  contains_sound (CB2_3_3I2R12Raw_sound a) (CB2_3_3I2R12P_check a)
def CB2_3_3I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R12Certificates (CB2_3_3I2R12CertificateIndex a)).output
lemma CB2_3_3I2R12Terms_sound (a : Fin 6) :
    (CB2_3_3I2R12Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R12Certificates_valid
    (CB2_3_3I2R12CertificateIndex a) (CB2_3_3I2R12P_sound a)
def CB2_3_3I2R12Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R12Entropy_sound : CB2_3_3I2R12Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R12Value CB2_3_3I2R12Terms CB2_3_3I2R12Terms_sound) (by decide +kernel)
def CB2_3_3I2R12Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R12Mass_sound : CB2_3_3I2R12Mass.Encloses (∑ a, CB2_3_3I2R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R12P CB2_3_3I2R12Value CB2_3_3I2R12P_sound) (by decide +kernel)
def CB2_3_3I2R12MassTerm : Ball := .exact 0
lemma CB2_3_3I2R12MassTerm_sound : CB2_3_3I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R12Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R12Mass_sound)
def CB2_3_3I2R12H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R12H_sound : CB2_3_3I2R12H.Encloses (homogeneousEntropy CB2_3_3I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R12Value CB2_3_3I2R12MassTerm_sound CB2_3_3I2R12Entropy_sound) (by decide +kernel)
def CB2_3_3I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 13 a
def CB2_3_3I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 13 a
lemma CB2_3_3I2R13Raw_sound (a : Fin 6) :
    (CB2_3_3I2R13Raw a).Encloses (CB2_3_3I2R13Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 13 a
def CB2_3_3I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R13Certificates_valid :
    CB2_3_3I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R13Certificates (CB2_3_3I2R13CertificateIndex a)).input
lemma CB2_3_3I2R13P_check : ∀ a : Fin 6, contains (CB2_3_3I2R13Raw a) (CB2_3_3I2R13P a) = true := by
  decide +kernel
lemma CB2_3_3I2R13P_sound (a : Fin 6) :
    (CB2_3_3I2R13P a).Encloses (CB2_3_3I2R13Value a) :=
  contains_sound (CB2_3_3I2R13Raw_sound a) (CB2_3_3I2R13P_check a)
def CB2_3_3I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R13Certificates (CB2_3_3I2R13CertificateIndex a)).output
lemma CB2_3_3I2R13Terms_sound (a : Fin 6) :
    (CB2_3_3I2R13Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R13Certificates_valid
    (CB2_3_3I2R13CertificateIndex a) (CB2_3_3I2R13P_sound a)
def CB2_3_3I2R13Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R13Entropy_sound : CB2_3_3I2R13Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R13Value CB2_3_3I2R13Terms CB2_3_3I2R13Terms_sound) (by decide +kernel)
def CB2_3_3I2R13Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R13Mass_sound : CB2_3_3I2R13Mass.Encloses (∑ a, CB2_3_3I2R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R13P CB2_3_3I2R13Value CB2_3_3I2R13P_sound) (by decide +kernel)
def CB2_3_3I2R13MassTerm : Ball := .exact 0
lemma CB2_3_3I2R13MassTerm_sound : CB2_3_3I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R13Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R13Mass_sound)
def CB2_3_3I2R13H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R13H_sound : CB2_3_3I2R13H.Encloses (homogeneousEntropy CB2_3_3I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R13Value CB2_3_3I2R13MassTerm_sound CB2_3_3I2R13Entropy_sound) (by decide +kernel)
def CB2_3_3I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 14 a
def CB2_3_3I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 14 a
lemma CB2_3_3I2R14Raw_sound (a : Fin 6) :
    (CB2_3_3I2R14Raw a).Encloses (CB2_3_3I2R14Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 14 a
def CB2_3_3I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R14Certificates_valid :
    CB2_3_3I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R14Certificates (CB2_3_3I2R14CertificateIndex a)).input
lemma CB2_3_3I2R14P_check : ∀ a : Fin 6, contains (CB2_3_3I2R14Raw a) (CB2_3_3I2R14P a) = true := by
  decide +kernel
lemma CB2_3_3I2R14P_sound (a : Fin 6) :
    (CB2_3_3I2R14P a).Encloses (CB2_3_3I2R14Value a) :=
  contains_sound (CB2_3_3I2R14Raw_sound a) (CB2_3_3I2R14P_check a)
def CB2_3_3I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R14Certificates (CB2_3_3I2R14CertificateIndex a)).output
lemma CB2_3_3I2R14Terms_sound (a : Fin 6) :
    (CB2_3_3I2R14Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R14Certificates_valid
    (CB2_3_3I2R14CertificateIndex a) (CB2_3_3I2R14P_sound a)
def CB2_3_3I2R14Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R14Entropy_sound : CB2_3_3I2R14Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R14Value CB2_3_3I2R14Terms CB2_3_3I2R14Terms_sound) (by decide +kernel)
def CB2_3_3I2R14Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R14Mass_sound : CB2_3_3I2R14Mass.Encloses (∑ a, CB2_3_3I2R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R14P CB2_3_3I2R14Value CB2_3_3I2R14P_sound) (by decide +kernel)
def CB2_3_3I2R14MassTerm : Ball := .exact 0
lemma CB2_3_3I2R14MassTerm_sound : CB2_3_3I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R14Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R14Mass_sound)
def CB2_3_3I2R14H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R14H_sound : CB2_3_3I2R14H.Encloses (homogeneousEntropy CB2_3_3I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R14Value CB2_3_3I2R14MassTerm_sound CB2_3_3I2R14Entropy_sound) (by decide +kernel)
def CB2_3_3I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 15 a
def CB2_3_3I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 15 a
lemma CB2_3_3I2R15Raw_sound (a : Fin 6) :
    (CB2_3_3I2R15Raw a).Encloses (CB2_3_3I2R15Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 15 a
def CB2_3_3I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R15Certificates_valid :
    CB2_3_3I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R15Certificates (CB2_3_3I2R15CertificateIndex a)).input
lemma CB2_3_3I2R15P_check : ∀ a : Fin 6, contains (CB2_3_3I2R15Raw a) (CB2_3_3I2R15P a) = true := by
  decide +kernel
lemma CB2_3_3I2R15P_sound (a : Fin 6) :
    (CB2_3_3I2R15P a).Encloses (CB2_3_3I2R15Value a) :=
  contains_sound (CB2_3_3I2R15Raw_sound a) (CB2_3_3I2R15P_check a)
def CB2_3_3I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R15Certificates (CB2_3_3I2R15CertificateIndex a)).output
lemma CB2_3_3I2R15Terms_sound (a : Fin 6) :
    (CB2_3_3I2R15Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R15Certificates_valid
    (CB2_3_3I2R15CertificateIndex a) (CB2_3_3I2R15P_sound a)
def CB2_3_3I2R15Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R15Entropy_sound : CB2_3_3I2R15Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R15Value CB2_3_3I2R15Terms CB2_3_3I2R15Terms_sound) (by decide +kernel)
def CB2_3_3I2R15Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R15Mass_sound : CB2_3_3I2R15Mass.Encloses (∑ a, CB2_3_3I2R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R15P CB2_3_3I2R15Value CB2_3_3I2R15P_sound) (by decide +kernel)
def CB2_3_3I2R15MassTerm : Ball := .exact 0
lemma CB2_3_3I2R15MassTerm_sound : CB2_3_3I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R15Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R15Mass_sound)
def CB2_3_3I2R15H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R15H_sound : CB2_3_3I2R15H.Encloses (homogeneousEntropy CB2_3_3I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R15Value CB2_3_3I2R15MassTerm_sound CB2_3_3I2R15Entropy_sound) (by decide +kernel)
def CB2_3_3I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) 16 a
def CB2_3_3I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 2 3 3)) B2_3_3Law (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) 16 a
lemma CB2_3_3I2R16Raw_sound (a : Fin 6) :
    (CB2_3_3I2R16Raw a).Encloses (CB2_3_3I2R16Value a) := by
  exact residualBall_sound_on (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u => B2_3_3Little u ((stageBPriority (shape 2 3 3)) 2)) (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) (fun u _ a => B2_3_3Little_sound u ((stageBPriority (shape 2 3 3)) 2) a) 16 a
def CB2_3_3I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_3_3I2R16Certificates_valid :
    CB2_3_3I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R16Certificates (CB2_3_3I2R16CertificateIndex a)).input
lemma CB2_3_3I2R16P_check : ∀ a : Fin 6, contains (CB2_3_3I2R16Raw a) (CB2_3_3I2R16P a) = true := by
  decide +kernel
lemma CB2_3_3I2R16P_sound (a : Fin 6) :
    (CB2_3_3I2R16P a).Encloses (CB2_3_3I2R16Value a) :=
  contains_sound (CB2_3_3I2R16Raw_sound a) (CB2_3_3I2R16P_check a)
def CB2_3_3I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I2R16Certificates (CB2_3_3I2R16CertificateIndex a)).output
lemma CB2_3_3I2R16Terms_sound (a : Fin 6) :
    (CB2_3_3I2R16Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R16Certificates_valid
    (CB2_3_3I2R16CertificateIndex a) (CB2_3_3I2R16P_sound a)
def CB2_3_3I2R16Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R16Entropy_sound : CB2_3_3I2R16Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R16Value CB2_3_3I2R16Terms CB2_3_3I2R16Terms_sound) (by decide +kernel)
def CB2_3_3I2R16Mass : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R16Mass_sound : CB2_3_3I2R16Mass.Encloses (∑ a, CB2_3_3I2R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R16P CB2_3_3I2R16Value CB2_3_3I2R16P_sound) (by decide +kernel)
def CB2_3_3I2R16MassTerm : Ball := .exact 0
lemma CB2_3_3I2R16MassTerm_sound : CB2_3_3I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R16Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R16Mass_sound)
def CB2_3_3I2R16H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2R16H_sound : CB2_3_3I2R16H.Encloses (homogeneousEntropy CB2_3_3I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R16Value CB2_3_3I2R16MassTerm_sound CB2_3_3I2R16Entropy_sound) (by decide +kernel)
def CB2_3_3I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_3_3I2R0H
  | 1 => CB2_3_3I2R1H
  | 2 => CB2_3_3I2R2H
  | 3 => CB2_3_3I2R3H
  | 4 => CB2_3_3I2R4H
  | 5 => CB2_3_3I2R5H
  | 6 => CB2_3_3I2R6H
  | 7 => CB2_3_3I2R7H
  | 8 => CB2_3_3I2R8H
  | 9 => CB2_3_3I2R9H
  | 10 => CB2_3_3I2R10H
  | 11 => CB2_3_3I2R11H
  | 12 => CB2_3_3I2R12H
  | 13 => CB2_3_3I2R13H
  | 14 => CB2_3_3I2R14H
  | 15 => CB2_3_3I2R15H
  | 16 => CB2_3_3I2R16H
  | _ => (.exact 0)
lemma CB2_3_3I2ResidualEntropies_sound (k : Fin 17) :
    (CB2_3_3I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB2_3_3I2R0H_sound
  · exact CB2_3_3I2R1H_sound
  · exact CB2_3_3I2R2H_sound
  · exact CB2_3_3I2R3H_sound
  · exact CB2_3_3I2R4H_sound
  · exact CB2_3_3I2R5H_sound
  · exact CB2_3_3I2R6H_sound
  · exact CB2_3_3I2R7H_sound
  · exact CB2_3_3I2R8H_sound
  · exact CB2_3_3I2R9H_sound
  · exact CB2_3_3I2R10H_sound
  · exact CB2_3_3I2R11H_sound
  · exact CB2_3_3I2R12H_sound
  · exact CB2_3_3I2R13H_sound
  · exact CB2_3_3I2R14H_sound
  · exact CB2_3_3I2R15H_sound
  · exact CB2_3_3I2R16H_sound
def CB2_3_3I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 0 1 3) ((stageBPriority (shape 2 3 3)) 2) a : ℝ)
def CB2_3_3I2S0_1_3E_4Log : Ball := .exact 0
lemma CB2_3_3I2S0_1_3E_4Log_sound : CB2_3_3I2S0_1_3E_4Log.Encloses (Real.log (CB2_3_3I2S0_1_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B2_3_3Little_sound (shape 0 1 3) ((stageBPriority (shape 2 3 3)) 2)) (4 : Fin 6))
def CB2_3_3I2S0_1_3E_4 : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S0_1_3E_4_sound : CB2_3_3I2S0_1_3E_4.Encloses (Foundation.entropyTerm (CB2_3_3I2S0_1_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_3_3Little_sound (shape 0 1 3) ((stageBPriority (shape 2 3 3)) 2)) (4 : Fin 6)) CB2_3_3I2S0_1_3E_4Log_sound) (by decide +kernel)
def CB2_3_3I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB2_3_3I2S0_1_3Terms_sound (a : Fin 6) :
    (CB2_3_3I2S0_1_3Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2S0_1_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 1 3) ((stageBPriority (shape 2 3 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 1 3) ((stageBPriority (shape 2 3 3)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 1 3) ((stageBPriority (shape 2 3 3)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 1 3) ((stageBPriority (shape 2 3 3)) 2)) (3 : Fin 6)))
  · exact CB2_3_3I2S0_1_3E_4_sound
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 1 3) ((stageBPriority (shape 2 3 3)) 2)) (5 : Fin 6)))
def CB2_3_3I2S0_1_3Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S0_1_3Entropy_sound : CB2_3_3I2S0_1_3Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2S0_1_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2S0_1_3Value CB2_3_3I2S0_1_3Terms CB2_3_3I2S0_1_3Terms_sound) (by decide +kernel)
def CB2_3_3I2S0_1_3Mass : Ball := ⟨1, 0⟩
lemma CB2_3_3I2S0_1_3Mass_sound : CB2_3_3I2S0_1_3Mass.Encloses (∑ a, CB2_3_3I2S0_1_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_3_3Little (shape 0 1 3) ((stageBPriority (shape 2 3 3)) 2)) CB2_3_3I2S0_1_3Value (B2_3_3Little_sound (shape 0 1 3) ((stageBPriority (shape 2 3 3)) 2))) (by decide +kernel)
def CB2_3_3I2S0_1_3MassTermLog : Ball := .exact 0
lemma CB2_3_3I2S0_1_3MassTermLog_sound : CB2_3_3I2S0_1_3MassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I2S0_1_3Value a))) := by
  exact log_exact_one_ball (CB2_3_3I2S0_1_3Mass_sound)
def CB2_3_3I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S0_1_3MassTerm_sound : CB2_3_3I2S0_1_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2S0_1_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I2S0_1_3Mass_sound) CB2_3_3I2S0_1_3MassTermLog_sound) (by decide +kernel)
def CB2_3_3I2S0_1_3H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S0_1_3H_sound : CB2_3_3I2S0_1_3H.Encloses (homogeneousEntropy CB2_3_3I2S0_1_3Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2S0_1_3Value CB2_3_3I2S0_1_3MassTerm_sound CB2_3_3I2S0_1_3Entropy_sound) (by decide +kernel)
def CB2_3_3I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2) a : ℝ)
def CB2_3_3I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 444959, 250000⟩
def CB2_3_3I2S0_2_2E_2Log : Ball := ⟨(-5831297766604325579437218806789 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma CB2_3_3I2S0_2_2E_2Log_sound : CB2_3_3I2S0_2_2E_2Log.Encloses (Real.log (CB2_3_3I2S0_2_2Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_3_3Little_sound (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2)) (2 : Fin 6)) (w := CB2_3_3I2S0_2_2E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_3_3I2S0_2_2E_2 : Ball := ⟨(51893768458609882110016108861 / 500000000000000000000000000000), (37689493321 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2S0_2_2E_2_sound : CB2_3_3I2S0_2_2E_2.Encloses (Foundation.entropyTerm (CB2_3_3I2S0_2_2Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_3_3Little_sound (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2)) (2 : Fin 6)) CB2_3_3I2S0_2_2E_2Log_sound) (by decide +kernel)
def CB2_3_3I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 55041, 31250⟩
def CB2_3_3I2S0_2_2E_3Log : Ball := ⟨(-55163243408937486421493177388873 / 25000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma CB2_3_3I2S0_2_2E_3Log_sound : CB2_3_3I2S0_2_2E_3Log.Encloses (Real.log (CB2_3_3I2S0_2_2Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_3_3Little_sound (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2)) (3 : Fin 6)) (w := CB2_3_3I2S0_2_2E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_3_3I2S0_2_2E_3 : Ball := ⟨(3036240080471328190125405976661 / 12500000000000000000000000000000), (5827692557 / 50000000000000000000000000000000)⟩
lemma CB2_3_3I2S0_2_2E_3_sound : CB2_3_3I2S0_2_2E_3.Encloses (Foundation.entropyTerm (CB2_3_3I2S0_2_2Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_3_3Little_sound (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2)) (3 : Fin 6)) CB2_3_3I2S0_2_2E_3Log_sound) (by decide +kernel)
def CB2_3_3I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(51893768458609882110016108861 / 500000000000000000000000000000), (37689493321 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(3036240080471328190125405976661 / 12500000000000000000000000000000), (5827692557 / 50000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB2_3_3I2S0_2_2Terms_sound (a : Fin 6) :
    (CB2_3_3I2S0_2_2Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2S0_2_2Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2)) (1 : Fin 6)))
  · exact CB2_3_3I2S0_2_2E_2_sound
  · exact CB2_3_3I2S0_2_2E_3_sound
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2)) (5 : Fin 6)))
def CB2_3_3I2S0_2_2Entropy : Ball := ⟨(2166792145968287621437904349093 / 6250000000000000000000000000000), (9868975687 / 20000000000000000000000000000000)⟩
lemma CB2_3_3I2S0_2_2Entropy_sound : CB2_3_3I2S0_2_2Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2S0_2_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2S0_2_2Value CB2_3_3I2S0_2_2Terms CB2_3_3I2S0_2_2Terms_sound) (by decide +kernel)
def CB2_3_3I2S0_2_2Mass : Ball := ⟨1, 0⟩
lemma CB2_3_3I2S0_2_2Mass_sound : CB2_3_3I2S0_2_2Mass.Encloses (∑ a, CB2_3_3I2S0_2_2Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_3_3Little (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2)) CB2_3_3I2S0_2_2Value (B2_3_3Little_sound (shape 0 2 2) ((stageBPriority (shape 2 3 3)) 2))) (by decide +kernel)
def CB2_3_3I2S0_2_2MassTermLog : Ball := .exact 0
lemma CB2_3_3I2S0_2_2MassTermLog_sound : CB2_3_3I2S0_2_2MassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I2S0_2_2Value a))) := by
  exact log_exact_one_ball (CB2_3_3I2S0_2_2Mass_sound)
def CB2_3_3I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S0_2_2MassTerm_sound : CB2_3_3I2S0_2_2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2S0_2_2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I2S0_2_2Mass_sound) CB2_3_3I2S0_2_2MassTermLog_sound) (by decide +kernel)
def CB2_3_3I2S0_2_2H : Ball := ⟨(2166792145968287621437904349093 / 6250000000000000000000000000000), (9868975687 / 20000000000000000000000000000000)⟩
lemma CB2_3_3I2S0_2_2H_sound : CB2_3_3I2S0_2_2H.Encloses (homogeneousEntropy CB2_3_3I2S0_2_2Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2S0_2_2Value CB2_3_3I2S0_2_2MassTerm_sound CB2_3_3I2S0_2_2Entropy_sound) (by decide +kernel)
def CB2_3_3I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 0 3 1) ((stageBPriority (shape 2 3 3)) 2) a : ℝ)
def CB2_3_3I2S0_3_1E_1Log : Ball := .exact 0
lemma CB2_3_3I2S0_3_1E_1Log_sound : CB2_3_3I2S0_3_1E_1Log.Encloses (Real.log (CB2_3_3I2S0_3_1Value (1 : Fin 6))) := by
  exact log_exact_one_ball ((B2_3_3Little_sound (shape 0 3 1) ((stageBPriority (shape 2 3 3)) 2)) (1 : Fin 6))
def CB2_3_3I2S0_3_1E_1 : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S0_3_1E_1_sound : CB2_3_3I2S0_3_1E_1.Encloses (Foundation.entropyTerm (CB2_3_3I2S0_3_1Value (1 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_3_3Little_sound (shape 0 3 1) ((stageBPriority (shape 2 3 3)) 2)) (1 : Fin 6)) CB2_3_3I2S0_3_1E_1Log_sound) (by decide +kernel)
def CB2_3_3I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB2_3_3I2S0_3_1Terms_sound (a : Fin 6) :
    (CB2_3_3I2S0_3_1Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2S0_3_1Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 3 1) ((stageBPriority (shape 2 3 3)) 2)) (0 : Fin 6)))
  · exact CB2_3_3I2S0_3_1E_1_sound
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 3 1) ((stageBPriority (shape 2 3 3)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 3 1) ((stageBPriority (shape 2 3 3)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 3 1) ((stageBPriority (shape 2 3 3)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 0 3 1) ((stageBPriority (shape 2 3 3)) 2)) (5 : Fin 6)))
def CB2_3_3I2S0_3_1Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S0_3_1Entropy_sound : CB2_3_3I2S0_3_1Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2S0_3_1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2S0_3_1Value CB2_3_3I2S0_3_1Terms CB2_3_3I2S0_3_1Terms_sound) (by decide +kernel)
def CB2_3_3I2S0_3_1Mass : Ball := ⟨1, 0⟩
lemma CB2_3_3I2S0_3_1Mass_sound : CB2_3_3I2S0_3_1Mass.Encloses (∑ a, CB2_3_3I2S0_3_1Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_3_3Little (shape 0 3 1) ((stageBPriority (shape 2 3 3)) 2)) CB2_3_3I2S0_3_1Value (B2_3_3Little_sound (shape 0 3 1) ((stageBPriority (shape 2 3 3)) 2))) (by decide +kernel)
def CB2_3_3I2S0_3_1MassTermLog : Ball := .exact 0
lemma CB2_3_3I2S0_3_1MassTermLog_sound : CB2_3_3I2S0_3_1MassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I2S0_3_1Value a))) := by
  exact log_exact_one_ball (CB2_3_3I2S0_3_1Mass_sound)
def CB2_3_3I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S0_3_1MassTerm_sound : CB2_3_3I2S0_3_1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2S0_3_1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I2S0_3_1Mass_sound) CB2_3_3I2S0_3_1MassTermLog_sound) (by decide +kernel)
def CB2_3_3I2S0_3_1H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S0_3_1H_sound : CB2_3_3I2S0_3_1H.Encloses (homogeneousEntropy CB2_3_3I2S0_3_1Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2S0_3_1Value CB2_3_3I2S0_3_1MassTerm_sound CB2_3_3I2S0_3_1Entropy_sound) (by decide +kernel)
def CB2_3_3I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 1 0 3) ((stageBPriority (shape 2 3 3)) 2) a : ℝ)
def CB2_3_3I2S1_0_3E_4Log : Ball := .exact 0
lemma CB2_3_3I2S1_0_3E_4Log_sound : CB2_3_3I2S1_0_3E_4Log.Encloses (Real.log (CB2_3_3I2S1_0_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B2_3_3Little_sound (shape 1 0 3) ((stageBPriority (shape 2 3 3)) 2)) (4 : Fin 6))
def CB2_3_3I2S1_0_3E_4 : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S1_0_3E_4_sound : CB2_3_3I2S1_0_3E_4.Encloses (Foundation.entropyTerm (CB2_3_3I2S1_0_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_3_3Little_sound (shape 1 0 3) ((stageBPriority (shape 2 3 3)) 2)) (4 : Fin 6)) CB2_3_3I2S1_0_3E_4Log_sound) (by decide +kernel)
def CB2_3_3I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB2_3_3I2S1_0_3Terms_sound (a : Fin 6) :
    (CB2_3_3I2S1_0_3Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2S1_0_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 1 0 3) ((stageBPriority (shape 2 3 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 1 0 3) ((stageBPriority (shape 2 3 3)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 1 0 3) ((stageBPriority (shape 2 3 3)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 1 0 3) ((stageBPriority (shape 2 3 3)) 2)) (3 : Fin 6)))
  · exact CB2_3_3I2S1_0_3E_4_sound
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 1 0 3) ((stageBPriority (shape 2 3 3)) 2)) (5 : Fin 6)))
def CB2_3_3I2S1_0_3Entropy : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S1_0_3Entropy_sound : CB2_3_3I2S1_0_3Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2S1_0_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2S1_0_3Value CB2_3_3I2S1_0_3Terms CB2_3_3I2S1_0_3Terms_sound) (by decide +kernel)
def CB2_3_3I2S1_0_3Mass : Ball := ⟨1, 0⟩
lemma CB2_3_3I2S1_0_3Mass_sound : CB2_3_3I2S1_0_3Mass.Encloses (∑ a, CB2_3_3I2S1_0_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_3_3Little (shape 1 0 3) ((stageBPriority (shape 2 3 3)) 2)) CB2_3_3I2S1_0_3Value (B2_3_3Little_sound (shape 1 0 3) ((stageBPriority (shape 2 3 3)) 2))) (by decide +kernel)
def CB2_3_3I2S1_0_3MassTermLog : Ball := .exact 0
lemma CB2_3_3I2S1_0_3MassTermLog_sound : CB2_3_3I2S1_0_3MassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I2S1_0_3Value a))) := by
  exact log_exact_one_ball (CB2_3_3I2S1_0_3Mass_sound)
def CB2_3_3I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S1_0_3MassTerm_sound : CB2_3_3I2S1_0_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2S1_0_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I2S1_0_3Mass_sound) CB2_3_3I2S1_0_3MassTermLog_sound) (by decide +kernel)
def CB2_3_3I2S1_0_3H : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S1_0_3H_sound : CB2_3_3I2S1_0_3H.Encloses (homogeneousEntropy CB2_3_3I2S1_0_3Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2S1_0_3Value CB2_3_3I2S1_0_3MassTerm_sound CB2_3_3I2S1_0_3Entropy_sound) (by decide +kernel)
def CB2_3_3I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 2 3 3) (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2) a : ℝ)
def CB2_3_3I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 895909, 500000⟩
def CB2_3_3I2S2_0_2E_2Log : Ball := ⟨(-10991643366502651450018611428491 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma CB2_3_3I2S2_0_2E_2Log_sound : CB2_3_3I2S2_0_2E_2Log.Encloses (Real.log (CB2_3_3I2S2_0_2Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_3_3Little_sound (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2)) (2 : Fin 6)) (w := CB2_3_3I2S2_0_2E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_3_3I2S2_0_2E_2 : Ball := ⟨(615469513552501497370920259143 / 6250000000000000000000000000000), (37943222041 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2S2_0_2E_2_sound : CB2_3_3I2S2_0_2E_2.Encloses (Foundation.entropyTerm (CB2_3_3I2S2_0_2Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_3_3Little_sound (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2)) (2 : Fin 6)) CB2_3_3I2S2_0_2E_2Log_sound) (by decide +kernel)
def CB2_3_3I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 104091, 62500⟩
def CB2_3_3I2S2_0_2E_3Log : Ball := ⟨(-56562244060752588474630885788059 / 25000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma CB2_3_3I2S2_0_2E_3Log_sound : CB2_3_3I2S2_0_2E_3Log.Encloses (Real.log (CB2_3_3I2S2_0_2Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_3_3Little_sound (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2)) (3 : Fin 6)) (w := CB2_3_3I2S2_0_2E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_3_3I2S2_0_2E_3 : Ball := ⟨(23550482186111190747651214130259 / 100000000000000000000000000000000), (2755265829 / 25000000000000000000000000000000)⟩
lemma CB2_3_3I2S2_0_2E_3_sound : CB2_3_3I2S2_0_2E_3.Encloses (Foundation.entropyTerm (CB2_3_3I2S2_0_2Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_3_3Little_sound (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2)) (3 : Fin 6)) CB2_3_3I2S2_0_2E_3Log_sound) (by decide +kernel)
def CB2_3_3I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(615469513552501497370920259143 / 6250000000000000000000000000000), (37943222041 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(23550482186111190747651214130259 / 100000000000000000000000000000000), (2755265829 / 25000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB2_3_3I2S2_0_2Terms_sound (a : Fin 6) :
    (CB2_3_3I2S2_0_2Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2S2_0_2Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2)) (1 : Fin 6)))
  · exact CB2_3_3I2S2_0_2E_2_sound
  · exact CB2_3_3I2S2_0_2E_3_sound
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_3_3Little_sound (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2)) (5 : Fin 6)))
def CB2_3_3I2S2_0_2Entropy : Ball := ⟨(33397994402951214705585938276547 / 100000000000000000000000000000000), (48964285357 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2S2_0_2Entropy_sound : CB2_3_3I2S2_0_2Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2S2_0_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2S2_0_2Value CB2_3_3I2S2_0_2Terms CB2_3_3I2S2_0_2Terms_sound) (by decide +kernel)
def CB2_3_3I2S2_0_2Mass : Ball := ⟨1, 0⟩
lemma CB2_3_3I2S2_0_2Mass_sound : CB2_3_3I2S2_0_2Mass.Encloses (∑ a, CB2_3_3I2S2_0_2Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_3_3Little (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2)) CB2_3_3I2S2_0_2Value (B2_3_3Little_sound (shape 2 0 2) ((stageBPriority (shape 2 3 3)) 2))) (by decide +kernel)
def CB2_3_3I2S2_0_2MassTermLog : Ball := .exact 0
lemma CB2_3_3I2S2_0_2MassTermLog_sound : CB2_3_3I2S2_0_2MassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I2S2_0_2Value a))) := by
  exact log_exact_one_ball (CB2_3_3I2S2_0_2Mass_sound)
def CB2_3_3I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
lemma CB2_3_3I2S2_0_2MassTerm_sound : CB2_3_3I2S2_0_2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2S2_0_2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I2S2_0_2Mass_sound) CB2_3_3I2S2_0_2MassTermLog_sound) (by decide +kernel)
def CB2_3_3I2S2_0_2H : Ball := ⟨(33397994402951214705585938276547 / 100000000000000000000000000000000), (48964285357 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2S2_0_2H_sound : CB2_3_3I2S2_0_2H.Encloses (homogeneousEntropy CB2_3_3I2S2_0_2Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2S2_0_2Value CB2_3_3I2S2_0_2MassTerm_sound CB2_3_3I2S2_0_2Entropy_sound) (by decide +kernel)
def CB2_3_3I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => CB2_3_3I2S0_1_3H
  | 0, 2, 2 => CB2_3_3I2S0_2_2H
  | 0, 3, 1 => CB2_3_3I2S0_3_1H
  | 1, 0, 3 => CB2_3_3I2S1_0_3H
  | 2, 0, 2 => CB2_3_3I2S2_0_2H
  | _, _, _ => (.exact 0)
lemma CB2_3_3I2Singles_sound (u : Shape) (hu : u ∈ below (shape 2 3 3))
    (hd : designated (stageBPriority (shape 2 3 3)) 2 u) :
    (CB2_3_3I2Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) u)) := by
  rw [B2_3_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CB2_3_3I2S0_1_3H_sound
  · exact CB2_3_3I2S0_2_2H_sound
  · exact CB2_3_3I2S0_3_1H_sound
  · exact CB2_3_3I2S1_0_3H_sound
  · exact (show ¬ designated (stageBPriority (shape 2 3 3)) 2 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 3 3)) 2 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 3 3)) 2 (shape 1 3 0) by decide +kernel) hd |>.elim
  · exact CB2_3_3I2S2_0_2H_sound
  · exact (show ¬ designated (stageBPriority (shape 2 3 3)) 2 (shape 2 1 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 3 3)) 2 (shape 2 2 0) by decide +kernel) hd |>.elim
def CB2_3_3I2Singleton : Ball := ⟨(5996455110702665623701618784177 / 100000000000000000000000000000000), (8551510679 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2Singleton_sound : CB2_3_3I2Singleton.Encloses
    (singletonEntropy (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2
    CB2_3_3I2Singles (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) (fun u _ => B2_3_3Law_sound u) CB2_3_3I2Singles_sound) (by decide +kernel)
def CB2_3_3I2Group : Ball := ⟨(6913719818436670221564110676421 / 100000000000000000000000000000000), (56727157761 / 50000000000000000000000000000000)⟩
lemma CB2_3_3I2Group_sound : CB2_3_3I2Group.Encloses
    (groupedEntropy (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB2_3_3I2Singleton_sound
    (finSumBall_sound 17 CB2_3_3I2ResidualEntropies _ CB2_3_3I2ResidualEntropies_sound)) (by decide +kernel)

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
def CB2_3_3I2H : Ball := ⟨(10574410027224598465538854536769 / 12500000000000000000000000000000), (317853838437 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I2_sound : CB2_3_3I2H.Encloses (stageBCapacity (shape 2 3 3) 2) := by
  have hb := contains_sound (Ball.add_sound CB2_3_3I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB2_3_3I2Group_sound)))
    (show contains (.add CB2_3_3I2PairH (.neg (.mul (.exact 2) CB2_3_3I2Group))) CB2_3_3I2H = true by decide +kernel)
  unfold CB2_3_3I2PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
