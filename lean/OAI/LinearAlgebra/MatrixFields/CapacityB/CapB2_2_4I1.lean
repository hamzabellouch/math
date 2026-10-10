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
def CB2_2_4I1PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 2 2 4)) (shape 2 2 4) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) a
def CB2_2_4I1PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) a
lemma CB2_2_4I1PairRaw_sound (a : PairSlot) :
    (CB2_2_4I1PairRaw a).Encloses (CB2_2_4I1PairValue a) := by
  exact pairLawBall_sound_on (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) (fun u _ a => B2_2_4Little_sound (complement (shape 2 2 4) u) ((stageBPriority (shape 2 2 4)) 1) a) a
def CB2_2_4I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(16755339902810166110201422814999 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩ ⟨(29932630223797274595672665798407 / 100000000000000000000000000000000), (14192325117 / 100000000000000000000000000000000)⟩ ⟨(-178645317835522061933206182491937 / 100000000000000000000000000000000), (84703295107 / 100000000000000000000000000000000)⟩ ⟨-3, 16755339902810166110201422814999, 12500000000000000000000000000000⟩,
   .log ⟨(209683712169054516004063447399 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(342865048336104256220603384961 / 5000000000000000000000000000000), (497305243 / 20000000000000000000000000000000)⟩ ⟨(-204394183022948736917557347021513 / 50000000000000000000000000000000), (74115383099 / 50000000000000000000000000000000)⟩ ⟨-6, 209683712169054516004063447399, 195312500000000000000000000000⟩,
   .log ⟨(3156719039983739776176606960581 / 5000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩ ⟨(29035798632197530040660383517107 / 100000000000000000000000000000000), (6684612613 / 25000000000000000000000000000000)⟩ ⟨(-9198094054118637402943840466023 / 20000000000000000000000000000000), (8470329501 / 20000000000000000000000000000000)⟩ ⟨-1, 3156719039983739776176606960581, 2500000000000000000000000000000⟩]
lemma CB2_2_4I1PairCertificates_valid :
    CB2_2_4I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 2 => 1
  | 0, 3 => 2
  | 1, 1 => 3
  | 2, 0 => 1
  | 3, 0 => 2
  | _, _ => 0
def CB2_2_4I1PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1PairCertificates (CB2_2_4I1PairCertificateIndex a)).input
lemma CB2_2_4I1PairP_check : ∀ a : PairSlot, contains (CB2_2_4I1PairRaw a) (CB2_2_4I1PairP a) = true := by
  decide +kernel
lemma CB2_2_4I1PairP_sound (a : PairSlot) :
    (CB2_2_4I1PairP a).Encloses (CB2_2_4I1PairValue a) :=
  contains_sound (CB2_2_4I1PairRaw_sound a) (CB2_2_4I1PairP_check a)
def CB2_2_4I1PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1PairCertificates (CB2_2_4I1PairCertificateIndex a)).output
lemma CB2_2_4I1PairTerms_sound (a : PairSlot) :
    (CB2_2_4I1PairTerms a).Encloses (Foundation.entropyTerm (CB2_2_4I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1PairCertificates_valid
    (CB2_2_4I1PairCertificateIndex a) (CB2_2_4I1PairP_sound a)
def CB2_2_4I1PairEntropy : Ball := ⟨(102615661013236249480829850512361 / 100000000000000000000000000000000), (15024038279 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I1PairEntropy_sound : CB2_2_4I1PairEntropy.Encloses (Foundation.finiteEntropy CB2_2_4I1PairValue) := by
  exact contains_sound (entropyPair_enclosed CB2_2_4I1PairValue CB2_2_4I1PairTerms CB2_2_4I1PairTerms_sound) (by decide +kernel)
def CB2_2_4I1PairMass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (57 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I1PairMass_sound : CB2_2_4I1PairMass.Encloses (∑ a, CB2_2_4I1PairValue a) := by
  exact contains_sound (pairSumBall_sound CB2_2_4I1PairP CB2_2_4I1PairValue CB2_2_4I1PairP_sound) (by decide +kernel)
def CB2_2_4I1PairMassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB2_2_4I1PairMassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (2117582391 / 10000000000000000000000000000000)⟩
lemma CB2_2_4I1PairMassTermLog_sound : CB2_2_4I1PairMassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_2_4I1PairMass_sound) (w := CB2_2_4I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I1PairMassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175823911 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I1PairMassTerm_sound : CB2_2_4I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I1PairMass_sound) CB2_2_4I1PairMassTermLog_sound) (by decide +kernel)
def CB2_2_4I1PairH : Ball := ⟨(102615661013236249480829850512363 / 100000000000000000000000000000000), (81271977027 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I1PairH_sound : CB2_2_4I1PairH.Encloses (homogeneousEntropy CB2_2_4I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1PairValue CB2_2_4I1PairMassTerm_sound CB2_2_4I1PairEntropy_sound) (by decide +kernel)

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
def CB2_2_4I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 0 a
def CB2_2_4I1R0Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 0 a
lemma CB2_2_4I1R0Raw_sound (a : Fin 6) :
    (CB2_2_4I1R0Raw a).Encloses (CB2_2_4I1R0Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 0 a
def CB2_2_4I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18432809600162602238233930394191 / 100000000000000000000000000000000), (17 / 25000000000000000000000000000000)⟩ ⟨(31170581090219803908545577364083 / 100000000000000000000000000000000), (15613197227 / 100000000000000000000000000000000)⟩ ⟨(-42275949470482293361630256775271 / 25000000000000000000000000000000), (847032951 / 1000000000000000000000000000000)⟩ ⟨-3, 18432809600162602238233930394191, 12500000000000000000000000000000⟩]
lemma CB2_2_4I1R0Certificates_valid :
    CB2_2_4I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB2_2_4I1R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R0Certificates (CB2_2_4I1R0CertificateIndex a)).input
lemma CB2_2_4I1R0P_check : ∀ a : Fin 6, contains (CB2_2_4I1R0Raw a) (CB2_2_4I1R0P a) = true := by
  decide +kernel
lemma CB2_2_4I1R0P_sound (a : Fin 6) :
    (CB2_2_4I1R0P a).Encloses (CB2_2_4I1R0Value a) :=
  contains_sound (CB2_2_4I1R0Raw_sound a) (CB2_2_4I1R0P_check a)
def CB2_2_4I1R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R0Certificates (CB2_2_4I1R0CertificateIndex a)).output
lemma CB2_2_4I1R0Terms_sound (a : Fin 6) :
    (CB2_2_4I1R0Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R0Certificates_valid
    (CB2_2_4I1R0CertificateIndex a) (CB2_2_4I1R0P_sound a)
def CB2_2_4I1R0Entropy : Ball := ⟨(31170581090219803908545577364083 / 100000000000000000000000000000000), (15613197227 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I1R0Entropy_sound : CB2_2_4I1R0Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R0Value CB2_2_4I1R0Terms CB2_2_4I1R0Terms_sound) (by decide +kernel)
def CB2_2_4I1R0Mass : Ball := ⟨(18432809600162602238233930394191 / 100000000000000000000000000000000), (17 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I1R0Mass_sound : CB2_2_4I1R0Mass.Encloses (∑ a, CB2_2_4I1R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R0P CB2_2_4I1R0Value CB2_2_4I1R0P_sound) (by decide +kernel)
def CB2_2_4I1R0MassTermLogWitness : LogWitness := ⟨-3, 18432809600162602238233930394191, 12500000000000000000000000000000⟩
def CB2_2_4I1R0MassTermLog : Ball := ⟨(-42275949470482293361630256775271 / 25000000000000000000000000000000), (847032951 / 1000000000000000000000000000000)⟩
lemma CB2_2_4I1R0MassTermLog_sound : CB2_2_4I1R0MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_2_4I1R0Mass_sound) (w := CB2_2_4I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I1R0MassTerm : Ball := ⟨(31170581090219803908545577364083 / 100000000000000000000000000000000), (15613197227 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I1R0MassTerm_sound : CB2_2_4I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I1R0Mass_sound) CB2_2_4I1R0MassTermLog_sound) (by decide +kernel)
def CB2_2_4I1R0H : Ball := ⟨0, (15613197227 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I1R0H_sound : CB2_2_4I1R0H.Encloses (homogeneousEntropy CB2_2_4I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R0Value CB2_2_4I1R0MassTerm_sound CB2_2_4I1R0Entropy_sound) (by decide +kernel)
def CB2_2_4I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 1 a
def CB2_2_4I1R1Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 1 a
lemma CB2_2_4I1R1Raw_sound (a : Fin 6) :
    (CB2_2_4I1R1Raw a).Encloses (CB2_2_4I1R1Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 1 a
def CB2_2_4I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3156719039983739776176606960581 / 5000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩ ⟨(29035798632197530040660383517107 / 100000000000000000000000000000000), (6684612613 / 25000000000000000000000000000000)⟩ ⟨(-9198094054118637402943840466023 / 20000000000000000000000000000000), (8470329501 / 20000000000000000000000000000000)⟩ ⟨-1, 3156719039983739776176606960581, 2500000000000000000000000000000⟩]
lemma CB2_2_4I1R1Certificates_valid :
    CB2_2_4I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_2_4I1R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R1Certificates (CB2_2_4I1R1CertificateIndex a)).input
lemma CB2_2_4I1R1P_check : ∀ a : Fin 6, contains (CB2_2_4I1R1Raw a) (CB2_2_4I1R1P a) = true := by
  decide +kernel
lemma CB2_2_4I1R1P_sound (a : Fin 6) :
    (CB2_2_4I1R1P a).Encloses (CB2_2_4I1R1Value a) :=
  contains_sound (CB2_2_4I1R1Raw_sound a) (CB2_2_4I1R1P_check a)
def CB2_2_4I1R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R1Certificates (CB2_2_4I1R1CertificateIndex a)).output
lemma CB2_2_4I1R1Terms_sound (a : Fin 6) :
    (CB2_2_4I1R1Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R1Certificates_valid
    (CB2_2_4I1R1CertificateIndex a) (CB2_2_4I1R1P_sound a)
def CB2_2_4I1R1Entropy : Ball := ⟨(29035798632197530040660383517107 / 100000000000000000000000000000000), (6684612613 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I1R1Entropy_sound : CB2_2_4I1R1Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R1Value CB2_2_4I1R1Terms CB2_2_4I1R1Terms_sound) (by decide +kernel)
def CB2_2_4I1R1Mass : Ball := ⟨(3156719039983739776176606960581 / 5000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
lemma CB2_2_4I1R1Mass_sound : CB2_2_4I1R1Mass.Encloses (∑ a, CB2_2_4I1R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R1P CB2_2_4I1R1Value CB2_2_4I1R1P_sound) (by decide +kernel)
def CB2_2_4I1R1MassTermLogWitness : LogWitness := ⟨-1, 3156719039983739776176606960581, 2500000000000000000000000000000⟩
def CB2_2_4I1R1MassTermLog : Ball := ⟨(-9198094054118637402943840466023 / 20000000000000000000000000000000), (8470329501 / 20000000000000000000000000000000)⟩
lemma CB2_2_4I1R1MassTermLog_sound : CB2_2_4I1R1MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_2_4I1R1Mass_sound) (w := CB2_2_4I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I1R1MassTerm : Ball := ⟨(29035798632197530040660383517107 / 100000000000000000000000000000000), (6684612613 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I1R1MassTerm_sound : CB2_2_4I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I1R1Mass_sound) CB2_2_4I1R1MassTermLog_sound) (by decide +kernel)
def CB2_2_4I1R1H : Ball := ⟨0, (6684612613 / 12500000000000000000000000000000)⟩
lemma CB2_2_4I1R1H_sound : CB2_2_4I1R1H.Encloses (homogeneousEntropy CB2_2_4I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R1Value CB2_2_4I1R1MassTerm_sound CB2_2_4I1R1Entropy_sound) (by decide +kernel)
def CB2_2_4I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 2 a
def CB2_2_4I1R2Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 2 a
lemma CB2_2_4I1R2Raw_sound (a : Fin 6) :
    (CB2_2_4I1R2Raw a).Encloses (CB2_2_4I1R2Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 2 a
def CB2_2_4I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(16734578832719927516175160443997 / 100000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩ ⟨(934884054584194909694671240271 / 3125000000000000000000000000000), (7087369901 / 50000000000000000000000000000000)⟩ ⟨(-178769301849420023191302953685561 / 100000000000000000000000000000000), (10587911887 / 12500000000000000000000000000000)⟩ ⟨-3, 16734578832719927516175160443997, 12500000000000000000000000000000⟩,
   .log ⟨(1676060038035253469983027737847 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(1370589502056228119583469905787 / 20000000000000000000000000000000), (1242218333 / 50000000000000000000000000000000)⟩ ⟨(-204436218117653100334233421709421 / 50000000000000000000000000000000), (74115383099 / 50000000000000000000000000000000)⟩ ⟨-6, 1676060038035253469983027737847, 1562500000000000000000000000000⟩]
lemma CB2_2_4I1R2Certificates_valid :
    CB2_2_4I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_2_4I1R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R2Certificates (CB2_2_4I1R2CertificateIndex a)).input
lemma CB2_2_4I1R2P_check : ∀ a : Fin 6, contains (CB2_2_4I1R2Raw a) (CB2_2_4I1R2P a) = true := by
  decide +kernel
lemma CB2_2_4I1R2P_sound (a : Fin 6) :
    (CB2_2_4I1R2P a).Encloses (CB2_2_4I1R2Value a) :=
  contains_sound (CB2_2_4I1R2Raw_sound a) (CB2_2_4I1R2P_check a)
def CB2_2_4I1R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R2Certificates (CB2_2_4I1R2CertificateIndex a)).output
lemma CB2_2_4I1R2Terms_sound (a : Fin 6) :
    (CB2_2_4I1R2Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R2Certificates_valid
    (CB2_2_4I1R2CertificateIndex a) (CB2_2_4I1R2P_sound a)
def CB2_2_4I1R2Entropy : Ball := ⟨(36769237256975377708146829217607 / 100000000000000000000000000000000), (4164794117 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I1R2Entropy_sound : CB2_2_4I1R2Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R2Value CB2_2_4I1R2Terms CB2_2_4I1R2Terms_sound) (by decide +kernel)
def CB2_2_4I1R2Mass : Ball := ⟨(4602659717688795246539547045461 / 25000000000000000000000000000000), (17 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I1R2Mass_sound : CB2_2_4I1R2Mass.Encloses (∑ a, CB2_2_4I1R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R2P CB2_2_4I1R2Value CB2_2_4I1R2P_sound) (by decide +kernel)
def CB2_2_4I1R2MassTermLogWitness : LogWitness := ⟨-3, 4602659717688795246539547045461, 3125000000000000000000000000000⟩
def CB2_2_4I1R2MassTermLog : Ball := ⟨(-169224148896851114673947115933983 / 100000000000000000000000000000000), (84703295101 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I1R2MassTermLog_sound : CB2_2_4I1R2MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_2_4I1R2Mass_sound) (w := CB2_2_4I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I1R2MassTerm : Ball := ⟨(31155246935508296120647022464513 / 100000000000000000000000000000000), (15594417889 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I1R2MassTerm_sound : CB2_2_4I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I1R2Mass_sound) CB2_2_4I1R2MassTermLog_sound) (by decide +kernel)
def CB2_2_4I1R2H : Ball := ⟨(2806995160733540793749903376547 / 50000000000000000000000000000000), (32253594357 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I1R2H_sound : CB2_2_4I1R2H.Encloses (homogeneousEntropy CB2_2_4I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R2Value CB2_2_4I1R2MassTerm_sound CB2_2_4I1R2Entropy_sound) (by decide +kernel)
def CB2_2_4I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 3 a
def CB2_2_4I1R3Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 3 a
lemma CB2_2_4I1R3Raw_sound (a : Fin 6) :
    (CB2_2_4I1R3Raw a).Encloses (CB2_2_4I1R3Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 3 a
def CB2_2_4I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R3Certificates_valid :
    CB2_2_4I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R3Certificates (CB2_2_4I1R3CertificateIndex a)).input
lemma CB2_2_4I1R3P_check : ∀ a : Fin 6, contains (CB2_2_4I1R3Raw a) (CB2_2_4I1R3P a) = true := by
  decide +kernel
lemma CB2_2_4I1R3P_sound (a : Fin 6) :
    (CB2_2_4I1R3P a).Encloses (CB2_2_4I1R3Value a) :=
  contains_sound (CB2_2_4I1R3Raw_sound a) (CB2_2_4I1R3P_check a)
def CB2_2_4I1R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R3Certificates (CB2_2_4I1R3CertificateIndex a)).output
lemma CB2_2_4I1R3Terms_sound (a : Fin 6) :
    (CB2_2_4I1R3Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R3Certificates_valid
    (CB2_2_4I1R3CertificateIndex a) (CB2_2_4I1R3P_sound a)
def CB2_2_4I1R3Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R3Entropy_sound : CB2_2_4I1R3Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R3Value CB2_2_4I1R3Terms CB2_2_4I1R3Terms_sound) (by decide +kernel)
def CB2_2_4I1R3Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R3Mass_sound : CB2_2_4I1R3Mass.Encloses (∑ a, CB2_2_4I1R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R3P CB2_2_4I1R3Value CB2_2_4I1R3P_sound) (by decide +kernel)
def CB2_2_4I1R3MassTerm : Ball := .exact 0
lemma CB2_2_4I1R3MassTerm_sound : CB2_2_4I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R3Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R3Mass_sound)
def CB2_2_4I1R3H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R3H_sound : CB2_2_4I1R3H.Encloses (homogeneousEntropy CB2_2_4I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R3Value CB2_2_4I1R3MassTerm_sound CB2_2_4I1R3Entropy_sound) (by decide +kernel)
def CB2_2_4I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 4 a
def CB2_2_4I1R4Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 4 a
lemma CB2_2_4I1R4Raw_sound (a : Fin 6) :
    (CB2_2_4I1R4Raw a).Encloses (CB2_2_4I1R4Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 4 a
def CB2_2_4I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R4Certificates_valid :
    CB2_2_4I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R4Certificates (CB2_2_4I1R4CertificateIndex a)).input
lemma CB2_2_4I1R4P_check : ∀ a : Fin 6, contains (CB2_2_4I1R4Raw a) (CB2_2_4I1R4P a) = true := by
  decide +kernel
lemma CB2_2_4I1R4P_sound (a : Fin 6) :
    (CB2_2_4I1R4P a).Encloses (CB2_2_4I1R4Value a) :=
  contains_sound (CB2_2_4I1R4Raw_sound a) (CB2_2_4I1R4P_check a)
def CB2_2_4I1R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R4Certificates (CB2_2_4I1R4CertificateIndex a)).output
lemma CB2_2_4I1R4Terms_sound (a : Fin 6) :
    (CB2_2_4I1R4Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R4Certificates_valid
    (CB2_2_4I1R4CertificateIndex a) (CB2_2_4I1R4P_sound a)
def CB2_2_4I1R4Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R4Entropy_sound : CB2_2_4I1R4Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R4Value CB2_2_4I1R4Terms CB2_2_4I1R4Terms_sound) (by decide +kernel)
def CB2_2_4I1R4Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R4Mass_sound : CB2_2_4I1R4Mass.Encloses (∑ a, CB2_2_4I1R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R4P CB2_2_4I1R4Value CB2_2_4I1R4P_sound) (by decide +kernel)
def CB2_2_4I1R4MassTerm : Ball := .exact 0
lemma CB2_2_4I1R4MassTerm_sound : CB2_2_4I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R4Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R4Mass_sound)
def CB2_2_4I1R4H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R4H_sound : CB2_2_4I1R4H.Encloses (homogeneousEntropy CB2_2_4I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R4Value CB2_2_4I1R4MassTerm_sound CB2_2_4I1R4Entropy_sound) (by decide +kernel)
def CB2_2_4I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 5 a
def CB2_2_4I1R5Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 5 a
lemma CB2_2_4I1R5Raw_sound (a : Fin 6) :
    (CB2_2_4I1R5Raw a).Encloses (CB2_2_4I1R5Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 5 a
def CB2_2_4I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R5Certificates_valid :
    CB2_2_4I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R5Certificates (CB2_2_4I1R5CertificateIndex a)).input
lemma CB2_2_4I1R5P_check : ∀ a : Fin 6, contains (CB2_2_4I1R5Raw a) (CB2_2_4I1R5P a) = true := by
  decide +kernel
lemma CB2_2_4I1R5P_sound (a : Fin 6) :
    (CB2_2_4I1R5P a).Encloses (CB2_2_4I1R5Value a) :=
  contains_sound (CB2_2_4I1R5Raw_sound a) (CB2_2_4I1R5P_check a)
def CB2_2_4I1R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R5Certificates (CB2_2_4I1R5CertificateIndex a)).output
lemma CB2_2_4I1R5Terms_sound (a : Fin 6) :
    (CB2_2_4I1R5Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R5Certificates_valid
    (CB2_2_4I1R5CertificateIndex a) (CB2_2_4I1R5P_sound a)
def CB2_2_4I1R5Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R5Entropy_sound : CB2_2_4I1R5Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R5Value CB2_2_4I1R5Terms CB2_2_4I1R5Terms_sound) (by decide +kernel)
def CB2_2_4I1R5Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R5Mass_sound : CB2_2_4I1R5Mass.Encloses (∑ a, CB2_2_4I1R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R5P CB2_2_4I1R5Value CB2_2_4I1R5P_sound) (by decide +kernel)
def CB2_2_4I1R5MassTerm : Ball := .exact 0
lemma CB2_2_4I1R5MassTerm_sound : CB2_2_4I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R5Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R5Mass_sound)
def CB2_2_4I1R5H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R5H_sound : CB2_2_4I1R5H.Encloses (homogeneousEntropy CB2_2_4I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R5Value CB2_2_4I1R5MassTerm_sound CB2_2_4I1R5Entropy_sound) (by decide +kernel)
def CB2_2_4I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 6 a
def CB2_2_4I1R6Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 6 a
lemma CB2_2_4I1R6Raw_sound (a : Fin 6) :
    (CB2_2_4I1R6Raw a).Encloses (CB2_2_4I1R6Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 6 a
def CB2_2_4I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R6Certificates_valid :
    CB2_2_4I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R6Certificates (CB2_2_4I1R6CertificateIndex a)).input
lemma CB2_2_4I1R6P_check : ∀ a : Fin 6, contains (CB2_2_4I1R6Raw a) (CB2_2_4I1R6P a) = true := by
  decide +kernel
lemma CB2_2_4I1R6P_sound (a : Fin 6) :
    (CB2_2_4I1R6P a).Encloses (CB2_2_4I1R6Value a) :=
  contains_sound (CB2_2_4I1R6Raw_sound a) (CB2_2_4I1R6P_check a)
def CB2_2_4I1R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R6Certificates (CB2_2_4I1R6CertificateIndex a)).output
lemma CB2_2_4I1R6Terms_sound (a : Fin 6) :
    (CB2_2_4I1R6Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R6Certificates_valid
    (CB2_2_4I1R6CertificateIndex a) (CB2_2_4I1R6P_sound a)
def CB2_2_4I1R6Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R6Entropy_sound : CB2_2_4I1R6Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R6Value CB2_2_4I1R6Terms CB2_2_4I1R6Terms_sound) (by decide +kernel)
def CB2_2_4I1R6Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R6Mass_sound : CB2_2_4I1R6Mass.Encloses (∑ a, CB2_2_4I1R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R6P CB2_2_4I1R6Value CB2_2_4I1R6P_sound) (by decide +kernel)
def CB2_2_4I1R6MassTerm : Ball := .exact 0
lemma CB2_2_4I1R6MassTerm_sound : CB2_2_4I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R6Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R6Mass_sound)
def CB2_2_4I1R6H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R6H_sound : CB2_2_4I1R6H.Encloses (homogeneousEntropy CB2_2_4I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R6Value CB2_2_4I1R6MassTerm_sound CB2_2_4I1R6Entropy_sound) (by decide +kernel)
def CB2_2_4I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 7 a
def CB2_2_4I1R7Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 7 a
lemma CB2_2_4I1R7Raw_sound (a : Fin 6) :
    (CB2_2_4I1R7Raw a).Encloses (CB2_2_4I1R7Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 7 a
def CB2_2_4I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R7Certificates_valid :
    CB2_2_4I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R7Certificates (CB2_2_4I1R7CertificateIndex a)).input
lemma CB2_2_4I1R7P_check : ∀ a : Fin 6, contains (CB2_2_4I1R7Raw a) (CB2_2_4I1R7P a) = true := by
  decide +kernel
lemma CB2_2_4I1R7P_sound (a : Fin 6) :
    (CB2_2_4I1R7P a).Encloses (CB2_2_4I1R7Value a) :=
  contains_sound (CB2_2_4I1R7Raw_sound a) (CB2_2_4I1R7P_check a)
def CB2_2_4I1R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R7Certificates (CB2_2_4I1R7CertificateIndex a)).output
lemma CB2_2_4I1R7Terms_sound (a : Fin 6) :
    (CB2_2_4I1R7Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R7Certificates_valid
    (CB2_2_4I1R7CertificateIndex a) (CB2_2_4I1R7P_sound a)
def CB2_2_4I1R7Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R7Entropy_sound : CB2_2_4I1R7Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R7Value CB2_2_4I1R7Terms CB2_2_4I1R7Terms_sound) (by decide +kernel)
def CB2_2_4I1R7Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R7Mass_sound : CB2_2_4I1R7Mass.Encloses (∑ a, CB2_2_4I1R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R7P CB2_2_4I1R7Value CB2_2_4I1R7P_sound) (by decide +kernel)
def CB2_2_4I1R7MassTerm : Ball := .exact 0
lemma CB2_2_4I1R7MassTerm_sound : CB2_2_4I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R7Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R7Mass_sound)
def CB2_2_4I1R7H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R7H_sound : CB2_2_4I1R7H.Encloses (homogeneousEntropy CB2_2_4I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R7Value CB2_2_4I1R7MassTerm_sound CB2_2_4I1R7Entropy_sound) (by decide +kernel)
def CB2_2_4I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 8 a
def CB2_2_4I1R8Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 8 a
lemma CB2_2_4I1R8Raw_sound (a : Fin 6) :
    (CB2_2_4I1R8Raw a).Encloses (CB2_2_4I1R8Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 8 a
def CB2_2_4I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R8Certificates_valid :
    CB2_2_4I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R8Certificates (CB2_2_4I1R8CertificateIndex a)).input
lemma CB2_2_4I1R8P_check : ∀ a : Fin 6, contains (CB2_2_4I1R8Raw a) (CB2_2_4I1R8P a) = true := by
  decide +kernel
lemma CB2_2_4I1R8P_sound (a : Fin 6) :
    (CB2_2_4I1R8P a).Encloses (CB2_2_4I1R8Value a) :=
  contains_sound (CB2_2_4I1R8Raw_sound a) (CB2_2_4I1R8P_check a)
def CB2_2_4I1R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R8Certificates (CB2_2_4I1R8CertificateIndex a)).output
lemma CB2_2_4I1R8Terms_sound (a : Fin 6) :
    (CB2_2_4I1R8Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R8Certificates_valid
    (CB2_2_4I1R8CertificateIndex a) (CB2_2_4I1R8P_sound a)
def CB2_2_4I1R8Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R8Entropy_sound : CB2_2_4I1R8Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R8Value CB2_2_4I1R8Terms CB2_2_4I1R8Terms_sound) (by decide +kernel)
def CB2_2_4I1R8Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R8Mass_sound : CB2_2_4I1R8Mass.Encloses (∑ a, CB2_2_4I1R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R8P CB2_2_4I1R8Value CB2_2_4I1R8P_sound) (by decide +kernel)
def CB2_2_4I1R8MassTerm : Ball := .exact 0
lemma CB2_2_4I1R8MassTerm_sound : CB2_2_4I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R8Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R8Mass_sound)
def CB2_2_4I1R8H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R8H_sound : CB2_2_4I1R8H.Encloses (homogeneousEntropy CB2_2_4I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R8Value CB2_2_4I1R8MassTerm_sound CB2_2_4I1R8Entropy_sound) (by decide +kernel)
def CB2_2_4I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 9 a
def CB2_2_4I1R9Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 9 a
lemma CB2_2_4I1R9Raw_sound (a : Fin 6) :
    (CB2_2_4I1R9Raw a).Encloses (CB2_2_4I1R9Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 9 a
def CB2_2_4I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R9Certificates_valid :
    CB2_2_4I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R9Certificates (CB2_2_4I1R9CertificateIndex a)).input
lemma CB2_2_4I1R9P_check : ∀ a : Fin 6, contains (CB2_2_4I1R9Raw a) (CB2_2_4I1R9P a) = true := by
  decide +kernel
lemma CB2_2_4I1R9P_sound (a : Fin 6) :
    (CB2_2_4I1R9P a).Encloses (CB2_2_4I1R9Value a) :=
  contains_sound (CB2_2_4I1R9Raw_sound a) (CB2_2_4I1R9P_check a)
def CB2_2_4I1R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R9Certificates (CB2_2_4I1R9CertificateIndex a)).output
lemma CB2_2_4I1R9Terms_sound (a : Fin 6) :
    (CB2_2_4I1R9Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R9Certificates_valid
    (CB2_2_4I1R9CertificateIndex a) (CB2_2_4I1R9P_sound a)
def CB2_2_4I1R9Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R9Entropy_sound : CB2_2_4I1R9Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R9Value CB2_2_4I1R9Terms CB2_2_4I1R9Terms_sound) (by decide +kernel)
def CB2_2_4I1R9Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R9Mass_sound : CB2_2_4I1R9Mass.Encloses (∑ a, CB2_2_4I1R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R9P CB2_2_4I1R9Value CB2_2_4I1R9P_sound) (by decide +kernel)
def CB2_2_4I1R9MassTerm : Ball := .exact 0
lemma CB2_2_4I1R9MassTerm_sound : CB2_2_4I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R9Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R9Mass_sound)
def CB2_2_4I1R9H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R9H_sound : CB2_2_4I1R9H.Encloses (homogeneousEntropy CB2_2_4I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R9Value CB2_2_4I1R9MassTerm_sound CB2_2_4I1R9Entropy_sound) (by decide +kernel)
def CB2_2_4I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 10 a
def CB2_2_4I1R10Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 10 a
lemma CB2_2_4I1R10Raw_sound (a : Fin 6) :
    (CB2_2_4I1R10Raw a).Encloses (CB2_2_4I1R10Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 10 a
def CB2_2_4I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R10Certificates_valid :
    CB2_2_4I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R10Certificates (CB2_2_4I1R10CertificateIndex a)).input
lemma CB2_2_4I1R10P_check : ∀ a : Fin 6, contains (CB2_2_4I1R10Raw a) (CB2_2_4I1R10P a) = true := by
  decide +kernel
lemma CB2_2_4I1R10P_sound (a : Fin 6) :
    (CB2_2_4I1R10P a).Encloses (CB2_2_4I1R10Value a) :=
  contains_sound (CB2_2_4I1R10Raw_sound a) (CB2_2_4I1R10P_check a)
def CB2_2_4I1R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R10Certificates (CB2_2_4I1R10CertificateIndex a)).output
lemma CB2_2_4I1R10Terms_sound (a : Fin 6) :
    (CB2_2_4I1R10Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R10Certificates_valid
    (CB2_2_4I1R10CertificateIndex a) (CB2_2_4I1R10P_sound a)
def CB2_2_4I1R10Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R10Entropy_sound : CB2_2_4I1R10Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R10Value CB2_2_4I1R10Terms CB2_2_4I1R10Terms_sound) (by decide +kernel)
def CB2_2_4I1R10Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R10Mass_sound : CB2_2_4I1R10Mass.Encloses (∑ a, CB2_2_4I1R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R10P CB2_2_4I1R10Value CB2_2_4I1R10P_sound) (by decide +kernel)
def CB2_2_4I1R10MassTerm : Ball := .exact 0
lemma CB2_2_4I1R10MassTerm_sound : CB2_2_4I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R10Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R10Mass_sound)
def CB2_2_4I1R10H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R10H_sound : CB2_2_4I1R10H.Encloses (homogeneousEntropy CB2_2_4I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R10Value CB2_2_4I1R10MassTerm_sound CB2_2_4I1R10Entropy_sound) (by decide +kernel)
def CB2_2_4I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 11 a
def CB2_2_4I1R11Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 11 a
lemma CB2_2_4I1R11Raw_sound (a : Fin 6) :
    (CB2_2_4I1R11Raw a).Encloses (CB2_2_4I1R11Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 11 a
def CB2_2_4I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R11Certificates_valid :
    CB2_2_4I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R11Certificates (CB2_2_4I1R11CertificateIndex a)).input
lemma CB2_2_4I1R11P_check : ∀ a : Fin 6, contains (CB2_2_4I1R11Raw a) (CB2_2_4I1R11P a) = true := by
  decide +kernel
lemma CB2_2_4I1R11P_sound (a : Fin 6) :
    (CB2_2_4I1R11P a).Encloses (CB2_2_4I1R11Value a) :=
  contains_sound (CB2_2_4I1R11Raw_sound a) (CB2_2_4I1R11P_check a)
def CB2_2_4I1R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R11Certificates (CB2_2_4I1R11CertificateIndex a)).output
lemma CB2_2_4I1R11Terms_sound (a : Fin 6) :
    (CB2_2_4I1R11Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R11Certificates_valid
    (CB2_2_4I1R11CertificateIndex a) (CB2_2_4I1R11P_sound a)
def CB2_2_4I1R11Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R11Entropy_sound : CB2_2_4I1R11Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R11Value CB2_2_4I1R11Terms CB2_2_4I1R11Terms_sound) (by decide +kernel)
def CB2_2_4I1R11Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R11Mass_sound : CB2_2_4I1R11Mass.Encloses (∑ a, CB2_2_4I1R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R11P CB2_2_4I1R11Value CB2_2_4I1R11P_sound) (by decide +kernel)
def CB2_2_4I1R11MassTerm : Ball := .exact 0
lemma CB2_2_4I1R11MassTerm_sound : CB2_2_4I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R11Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R11Mass_sound)
def CB2_2_4I1R11H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R11H_sound : CB2_2_4I1R11H.Encloses (homogeneousEntropy CB2_2_4I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R11Value CB2_2_4I1R11MassTerm_sound CB2_2_4I1R11Entropy_sound) (by decide +kernel)
def CB2_2_4I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 12 a
def CB2_2_4I1R12Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 12 a
lemma CB2_2_4I1R12Raw_sound (a : Fin 6) :
    (CB2_2_4I1R12Raw a).Encloses (CB2_2_4I1R12Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 12 a
def CB2_2_4I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R12Certificates_valid :
    CB2_2_4I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R12Certificates (CB2_2_4I1R12CertificateIndex a)).input
lemma CB2_2_4I1R12P_check : ∀ a : Fin 6, contains (CB2_2_4I1R12Raw a) (CB2_2_4I1R12P a) = true := by
  decide +kernel
lemma CB2_2_4I1R12P_sound (a : Fin 6) :
    (CB2_2_4I1R12P a).Encloses (CB2_2_4I1R12Value a) :=
  contains_sound (CB2_2_4I1R12Raw_sound a) (CB2_2_4I1R12P_check a)
def CB2_2_4I1R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R12Certificates (CB2_2_4I1R12CertificateIndex a)).output
lemma CB2_2_4I1R12Terms_sound (a : Fin 6) :
    (CB2_2_4I1R12Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R12Certificates_valid
    (CB2_2_4I1R12CertificateIndex a) (CB2_2_4I1R12P_sound a)
def CB2_2_4I1R12Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R12Entropy_sound : CB2_2_4I1R12Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R12Value CB2_2_4I1R12Terms CB2_2_4I1R12Terms_sound) (by decide +kernel)
def CB2_2_4I1R12Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R12Mass_sound : CB2_2_4I1R12Mass.Encloses (∑ a, CB2_2_4I1R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R12P CB2_2_4I1R12Value CB2_2_4I1R12P_sound) (by decide +kernel)
def CB2_2_4I1R12MassTerm : Ball := .exact 0
lemma CB2_2_4I1R12MassTerm_sound : CB2_2_4I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R12Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R12Mass_sound)
def CB2_2_4I1R12H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R12H_sound : CB2_2_4I1R12H.Encloses (homogeneousEntropy CB2_2_4I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R12Value CB2_2_4I1R12MassTerm_sound CB2_2_4I1R12Entropy_sound) (by decide +kernel)
def CB2_2_4I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 13 a
def CB2_2_4I1R13Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 13 a
lemma CB2_2_4I1R13Raw_sound (a : Fin 6) :
    (CB2_2_4I1R13Raw a).Encloses (CB2_2_4I1R13Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 13 a
def CB2_2_4I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R13Certificates_valid :
    CB2_2_4I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R13Certificates (CB2_2_4I1R13CertificateIndex a)).input
lemma CB2_2_4I1R13P_check : ∀ a : Fin 6, contains (CB2_2_4I1R13Raw a) (CB2_2_4I1R13P a) = true := by
  decide +kernel
lemma CB2_2_4I1R13P_sound (a : Fin 6) :
    (CB2_2_4I1R13P a).Encloses (CB2_2_4I1R13Value a) :=
  contains_sound (CB2_2_4I1R13Raw_sound a) (CB2_2_4I1R13P_check a)
def CB2_2_4I1R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R13Certificates (CB2_2_4I1R13CertificateIndex a)).output
lemma CB2_2_4I1R13Terms_sound (a : Fin 6) :
    (CB2_2_4I1R13Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R13Certificates_valid
    (CB2_2_4I1R13CertificateIndex a) (CB2_2_4I1R13P_sound a)
def CB2_2_4I1R13Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R13Entropy_sound : CB2_2_4I1R13Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R13Value CB2_2_4I1R13Terms CB2_2_4I1R13Terms_sound) (by decide +kernel)
def CB2_2_4I1R13Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R13Mass_sound : CB2_2_4I1R13Mass.Encloses (∑ a, CB2_2_4I1R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R13P CB2_2_4I1R13Value CB2_2_4I1R13P_sound) (by decide +kernel)
def CB2_2_4I1R13MassTerm : Ball := .exact 0
lemma CB2_2_4I1R13MassTerm_sound : CB2_2_4I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R13Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R13Mass_sound)
def CB2_2_4I1R13H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R13H_sound : CB2_2_4I1R13H.Encloses (homogeneousEntropy CB2_2_4I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R13Value CB2_2_4I1R13MassTerm_sound CB2_2_4I1R13Entropy_sound) (by decide +kernel)
def CB2_2_4I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 14 a
def CB2_2_4I1R14Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 14 a
lemma CB2_2_4I1R14Raw_sound (a : Fin 6) :
    (CB2_2_4I1R14Raw a).Encloses (CB2_2_4I1R14Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 14 a
def CB2_2_4I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R14Certificates_valid :
    CB2_2_4I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R14Certificates (CB2_2_4I1R14CertificateIndex a)).input
lemma CB2_2_4I1R14P_check : ∀ a : Fin 6, contains (CB2_2_4I1R14Raw a) (CB2_2_4I1R14P a) = true := by
  decide +kernel
lemma CB2_2_4I1R14P_sound (a : Fin 6) :
    (CB2_2_4I1R14P a).Encloses (CB2_2_4I1R14Value a) :=
  contains_sound (CB2_2_4I1R14Raw_sound a) (CB2_2_4I1R14P_check a)
def CB2_2_4I1R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R14Certificates (CB2_2_4I1R14CertificateIndex a)).output
lemma CB2_2_4I1R14Terms_sound (a : Fin 6) :
    (CB2_2_4I1R14Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R14Certificates_valid
    (CB2_2_4I1R14CertificateIndex a) (CB2_2_4I1R14P_sound a)
def CB2_2_4I1R14Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R14Entropy_sound : CB2_2_4I1R14Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R14Value CB2_2_4I1R14Terms CB2_2_4I1R14Terms_sound) (by decide +kernel)
def CB2_2_4I1R14Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R14Mass_sound : CB2_2_4I1R14Mass.Encloses (∑ a, CB2_2_4I1R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R14P CB2_2_4I1R14Value CB2_2_4I1R14P_sound) (by decide +kernel)
def CB2_2_4I1R14MassTerm : Ball := .exact 0
lemma CB2_2_4I1R14MassTerm_sound : CB2_2_4I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R14Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R14Mass_sound)
def CB2_2_4I1R14H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R14H_sound : CB2_2_4I1R14H.Encloses (homogeneousEntropy CB2_2_4I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R14Value CB2_2_4I1R14MassTerm_sound CB2_2_4I1R14Entropy_sound) (by decide +kernel)
def CB2_2_4I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 15 a
def CB2_2_4I1R15Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 15 a
lemma CB2_2_4I1R15Raw_sound (a : Fin 6) :
    (CB2_2_4I1R15Raw a).Encloses (CB2_2_4I1R15Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 15 a
def CB2_2_4I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R15Certificates_valid :
    CB2_2_4I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R15Certificates (CB2_2_4I1R15CertificateIndex a)).input
lemma CB2_2_4I1R15P_check : ∀ a : Fin 6, contains (CB2_2_4I1R15Raw a) (CB2_2_4I1R15P a) = true := by
  decide +kernel
lemma CB2_2_4I1R15P_sound (a : Fin 6) :
    (CB2_2_4I1R15P a).Encloses (CB2_2_4I1R15Value a) :=
  contains_sound (CB2_2_4I1R15Raw_sound a) (CB2_2_4I1R15P_check a)
def CB2_2_4I1R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R15Certificates (CB2_2_4I1R15CertificateIndex a)).output
lemma CB2_2_4I1R15Terms_sound (a : Fin 6) :
    (CB2_2_4I1R15Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R15Certificates_valid
    (CB2_2_4I1R15CertificateIndex a) (CB2_2_4I1R15P_sound a)
def CB2_2_4I1R15Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R15Entropy_sound : CB2_2_4I1R15Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R15Value CB2_2_4I1R15Terms CB2_2_4I1R15Terms_sound) (by decide +kernel)
def CB2_2_4I1R15Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R15Mass_sound : CB2_2_4I1R15Mass.Encloses (∑ a, CB2_2_4I1R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R15P CB2_2_4I1R15Value CB2_2_4I1R15P_sound) (by decide +kernel)
def CB2_2_4I1R15MassTerm : Ball := .exact 0
lemma CB2_2_4I1R15MassTerm_sound : CB2_2_4I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R15Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R15Mass_sound)
def CB2_2_4I1R15H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R15H_sound : CB2_2_4I1R15H.Encloses (homogeneousEntropy CB2_2_4I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R15Value CB2_2_4I1R15MassTerm_sound CB2_2_4I1R15Entropy_sound) (by decide +kernel)
def CB2_2_4I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) 16 a
def CB2_2_4I1R16Raw (a : Fin 6) : Ball := residualBall (below (shape 2 2 4)) B2_2_4Law (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) 16 a
lemma CB2_2_4I1R16Raw_sound (a : Fin 6) :
    (CB2_2_4I1R16Raw a).Encloses (CB2_2_4I1R16Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 1)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 1) a) 16 a
def CB2_2_4I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB2_2_4I1R16Certificates_valid :
    CB2_2_4I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R16Certificates (CB2_2_4I1R16CertificateIndex a)).input
lemma CB2_2_4I1R16P_check : ∀ a : Fin 6, contains (CB2_2_4I1R16Raw a) (CB2_2_4I1R16P a) = true := by
  decide +kernel
lemma CB2_2_4I1R16P_sound (a : Fin 6) :
    (CB2_2_4I1R16P a).Encloses (CB2_2_4I1R16Value a) :=
  contains_sound (CB2_2_4I1R16Raw_sound a) (CB2_2_4I1R16P_check a)
def CB2_2_4I1R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I1R16Certificates (CB2_2_4I1R16CertificateIndex a)).output
lemma CB2_2_4I1R16Terms_sound (a : Fin 6) :
    (CB2_2_4I1R16Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I1R16Certificates_valid
    (CB2_2_4I1R16CertificateIndex a) (CB2_2_4I1R16P_sound a)
def CB2_2_4I1R16Entropy : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R16Entropy_sound : CB2_2_4I1R16Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1R16Value CB2_2_4I1R16Terms CB2_2_4I1R16Terms_sound) (by decide +kernel)
def CB2_2_4I1R16Mass : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R16Mass_sound : CB2_2_4I1R16Mass.Encloses (∑ a, CB2_2_4I1R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_2_4I1R16P CB2_2_4I1R16Value CB2_2_4I1R16P_sound) (by decide +kernel)
def CB2_2_4I1R16MassTerm : Ball := .exact 0
lemma CB2_2_4I1R16MassTerm_sound : CB2_2_4I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1R16Value a))) :=
  entropyTerm_zero_ball (CB2_2_4I1R16Mass_sound)
def CB2_2_4I1R16H : Ball := ⟨0, 0⟩
lemma CB2_2_4I1R16H_sound : CB2_2_4I1R16H.Encloses (homogeneousEntropy CB2_2_4I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1R16Value CB2_2_4I1R16MassTerm_sound CB2_2_4I1R16Entropy_sound) (by decide +kernel)
def CB2_2_4I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB2_2_4I1R0H
  | 1 => CB2_2_4I1R1H
  | 2 => CB2_2_4I1R2H
  | 3 => CB2_2_4I1R3H
  | 4 => CB2_2_4I1R4H
  | 5 => CB2_2_4I1R5H
  | 6 => CB2_2_4I1R6H
  | 7 => CB2_2_4I1R7H
  | 8 => CB2_2_4I1R8H
  | 9 => CB2_2_4I1R9H
  | 10 => CB2_2_4I1R10H
  | 11 => CB2_2_4I1R11H
  | 12 => CB2_2_4I1R12H
  | 13 => CB2_2_4I1R13H
  | 14 => CB2_2_4I1R14H
  | 15 => CB2_2_4I1R15H
  | 16 => CB2_2_4I1R16H
  | _ => (.exact 0)
lemma CB2_2_4I1ResidualEntropies_sound (k : Fin 17) :
    (CB2_2_4I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CB2_2_4I1R0H_sound
  · exact CB2_2_4I1R1H_sound
  · exact CB2_2_4I1R2H_sound
  · exact CB2_2_4I1R3H_sound
  · exact CB2_2_4I1R4H_sound
  · exact CB2_2_4I1R5H_sound
  · exact CB2_2_4I1R6H_sound
  · exact CB2_2_4I1R7H_sound
  · exact CB2_2_4I1R8H_sound
  · exact CB2_2_4I1R9H_sound
  · exact CB2_2_4I1R10H_sound
  · exact CB2_2_4I1R11H_sound
  · exact CB2_2_4I1R12H_sound
  · exact CB2_2_4I1R13H_sound
  · exact CB2_2_4I1R14H_sound
  · exact CB2_2_4I1R15H_sound
  · exact CB2_2_4I1R16H_sound
def CB2_2_4I1S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 2 2 4) (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1) a : ℝ)
def CB2_2_4I1S2_2_0E_2LogWitness : LogWitness := ⟨-1, 468209, 250000⟩
def CB2_2_4I1S2_2_0E_2Log : Ball := ⟨(-1642333024891709491091130987267 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I1S2_2_0E_2Log_sound : CB2_2_4I1S2_2_0E_2Log.Encloses (Real.log (CB2_2_4I1S2_2_0Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_2_4Little_sound (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1)) (2 : Fin 6)) (w := CB2_2_4I1S2_2_0E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I1S2_2_0E_2 : Ball := ⟨(3075820413006089636457149393669 / 50000000000000000000000000000000), (9914711231 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I1S2_2_0E_2_sound : CB2_2_4I1S2_2_0E_2.Encloses (Foundation.entropyTerm (CB2_2_4I1S2_2_0Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_2_4Little_sound (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1)) (2 : Fin 6)) CB2_2_4I1S2_2_0E_2Log_sound) (by decide +kernel)
def CB2_2_4I1S2_2_0E_3LogWitness : LogWitness := ⟨-4, 31791, 31250⟩
def CB2_2_4I1S2_2_0E_3Log : Ball := ⟨(-8610702711129322182939633075951 / 3125000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I1S2_2_0E_3Log_sound : CB2_2_4I1S2_2_0E_3Log.Encloses (Real.log (CB2_2_4I1S2_2_0Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B2_2_4Little_sound (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1)) (3 : Fin 6)) (w := CB2_2_4I1S2_2_0E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I1S2_2_0E_3 : Ball := ⟨(4379885598232196504285342001881 / 25000000000000000000000000000000), (1683001527 / 25000000000000000000000000000000)⟩
lemma CB2_2_4I1S2_2_0E_3_sound : CB2_2_4I1S2_2_0E_3.Encloses (Foundation.entropyTerm (CB2_2_4I1S2_2_0Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B2_2_4Little_sound (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1)) (3 : Fin 6)) CB2_2_4I1S2_2_0E_3Log_sound) (by decide +kernel)
def CB2_2_4I1S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(3075820413006089636457149393669 / 50000000000000000000000000000000), (9914711231 / 25000000000000000000000000000000)⟩
  | 3 => ⟨(4379885598232196504285342001881 / 25000000000000000000000000000000), (1683001527 / 25000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB2_2_4I1S2_2_0Terms_sound (a : Fin 6) :
    (CB2_2_4I1S2_2_0Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I1S2_2_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1)) (1 : Fin 6)))
  · exact CB2_2_4I1S2_2_0E_2_sound
  · exact CB2_2_4I1S2_2_0E_3_sound
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B2_2_4Little_sound (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1)) (5 : Fin 6)))
def CB2_2_4I1S2_2_0Entropy : Ball := ⟨(11835591609470482645027833397431 / 50000000000000000000000000000000), (5798856379 / 12500000000000000000000000000000)⟩
lemma CB2_2_4I1S2_2_0Entropy_sound : CB2_2_4I1S2_2_0Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I1S2_2_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_2_4I1S2_2_0Value CB2_2_4I1S2_2_0Terms CB2_2_4I1S2_2_0Terms_sound) (by decide +kernel)
def CB2_2_4I1S2_2_0Mass : Ball := ⟨1, 0⟩
lemma CB2_2_4I1S2_2_0Mass_sound : CB2_2_4I1S2_2_0Mass.Encloses (∑ a, CB2_2_4I1S2_2_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B2_2_4Little (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1)) CB2_2_4I1S2_2_0Value (B2_2_4Little_sound (shape 2 2 0) ((stageBPriority (shape 2 2 4)) 1))) (by decide +kernel)
def CB2_2_4I1S2_2_0MassTermLog : Ball := .exact 0
lemma CB2_2_4I1S2_2_0MassTermLog_sound : CB2_2_4I1S2_2_0MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I1S2_2_0Value a))) := by
  exact log_exact_one_ball (CB2_2_4I1S2_2_0Mass_sound)
def CB2_2_4I1S2_2_0MassTerm : Ball := ⟨0, 0⟩
lemma CB2_2_4I1S2_2_0MassTerm_sound : CB2_2_4I1S2_2_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I1S2_2_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I1S2_2_0Mass_sound) CB2_2_4I1S2_2_0MassTermLog_sound) (by decide +kernel)
def CB2_2_4I1S2_2_0H : Ball := ⟨(11835591609470482645027833397431 / 50000000000000000000000000000000), (5798856379 / 12500000000000000000000000000000)⟩
lemma CB2_2_4I1S2_2_0H_sound : CB2_2_4I1S2_2_0H.Encloses (homogeneousEntropy CB2_2_4I1S2_2_0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I1S2_2_0Value CB2_2_4I1S2_2_0MassTerm_sound CB2_2_4I1S2_2_0Entropy_sound) (by decide +kernel)
def CB2_2_4I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 2, 0 => CB2_2_4I1S2_2_0H
  | _, _, _ => (.exact 0)
lemma CB2_2_4I1Singles_sound (u : Shape) (hu : u ∈ below (shape 2 2 4))
    (hd : designated (stageBPriority (shape 2 2 4)) 1 u) :
    (CB2_2_4I1Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) u)) := by
  rw [B2_2_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 1 (shape 0 0 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 1 (shape 0 1 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 1 (shape 0 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 1 (shape 1 0 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 1 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 1 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 1 (shape 2 0 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 2 2 4)) 1 (shape 2 1 1) by decide +kernel) hd |>.elim
  · exact CB2_2_4I1S2_2_0H_sound
def CB2_2_4I1Singleton : Ball := ⟨(5248073979006309136194565619 / 100000000000000000000000000000000), (10285191 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I1Singleton_sound : CB2_2_4I1Singleton.Encloses
    (singletonEntropy (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1
    CB2_2_4I1Singles (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ)) (fun u _ => B2_2_4Law_sound u) CB2_2_4I1Singles_sound) (by decide +kernel)
def CB2_2_4I1Group : Ball := ⟨(5619238395446087896636001318713 / 100000000000000000000000000000000), (58483587453 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I1Group_sound : CB2_2_4I1Group.Encloses
    (groupedEntropy (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 1 (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB2_2_4I1Singleton_sound
    (finSumBall_sound 17 CB2_2_4I1ResidualEntropies _ CB2_2_4I1ResidualEntropies_sound)) (by decide +kernel)

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
def CB2_2_4I1H : Ball := ⟨(91377184222344073687557847874937 / 100000000000000000000000000000000), (315206326839 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I1_sound : CB2_2_4I1H.Encloses (stageBCapacity (shape 2 2 4) 1) := by
  have hb := contains_sound (Ball.add_sound CB2_2_4I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB2_2_4I1Group_sound)))
    (show contains (.add CB2_2_4I1PairH (.neg (.mul (.exact 2) CB2_2_4I1Group))) CB2_2_4I1H = true by decide +kernel)
  unfold CB2_2_4I1PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
