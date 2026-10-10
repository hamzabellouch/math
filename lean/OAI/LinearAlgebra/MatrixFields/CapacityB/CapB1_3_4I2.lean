import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB1_3_4

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_3_4I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 1 3 4)) (shape 1 3 4) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) a
def CB1_3_4I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) a
lemma CB1_3_4I2PairRaw_sound (a : PairSlot) :
    (CB1_3_4I2PairRaw a).Encloses (CB1_3_4I2PairValue a) := by
  exact pairLawBall_sound_on (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) (fun u _ a => B1_3_4Little_sound (complement (shape 1 3 4) u) ((stageBPriority (shape 1 3 4)) 2) a) a
def CB1_3_4I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18376602916823826473515371739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(39518182540949711406409763533 / 25000000000000000000000000000000), (54479569 / 100000000000000000000000000000000)⟩ ⟨(-860184719010731091912411428528721 / 100000000000000000000000000000000), (296461537003 / 100000000000000000000000000000000)⟩ ⟨-13, 18376602916823826473515371739, 12207031250000000000000000000⟩,
   .log ⟨(1456119070923005006600137580027 / 20000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(19074850750659438759889291329071 / 100000000000000000000000000000000), (963578779 / 12500000000000000000000000000000)⟩ ⟨(-130997877382158514633813346100449 / 50000000000000000000000000000000), (5293955931 / 5000000000000000000000000000000)⟩ ⟨-4, 1456119070923005006600137580027, 1250000000000000000000000000000⟩,
   .log ⟨(77369303606423225289931508632371 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩ ⟨(19851421976498367966321231454091 / 100000000000000000000000000000000), (1638358733 / 5000000000000000000000000000000)⟩ ⟨(-12829003914447988076865007937373 / 50000000000000000000000000000000), (42351647393 / 100000000000000000000000000000000)⟩ ⟨-1, 77369303606423225289931508632371, 50000000000000000000000000000000⟩,
   .log ⟨(4011596667753851198216770545993 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(6450609035542397540010662179793 / 50000000000000000000000000000000), (637116479 / 12500000000000000000000000000000)⟩ ⟨(-80399521310229117688306751909523 / 25000000000000000000000000000000), (127054942147 / 100000000000000000000000000000000)⟩ ⟨-5, 4011596667753851198216770545993, 3125000000000000000000000000000⟩,
   .log ⟨(4779571502687297343271865947 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(17694790791180915667743540161 / 20000000000000000000000000000000), (1518171 / 5000000000000000000000000000000)⟩ ⟨(-462771369285721572999617089651721 / 50000000000000000000000000000000), (158818682853 / 50000000000000000000000000000000)⟩ ⟨-14, 4779571502687297343271865947, 3051757812500000000000000000⟩]
lemma CB1_3_4I2PairCertificates_valid :
    CB1_3_4I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2PairCertificateIndex (a : PairSlot) : ℕ :=
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
def CB1_3_4I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2PairCertificates (CB1_3_4I2PairCertificateIndex a)).input
lemma CB1_3_4I2PairP_check : ∀ a : PairSlot, contains (CB1_3_4I2PairRaw a) (CB1_3_4I2PairP a) = true := by
  decide +kernel
lemma CB1_3_4I2PairP_sound (a : PairSlot) :
    (CB1_3_4I2PairP a).Encloses (CB1_3_4I2PairValue a) :=
  contains_sound (CB1_3_4I2PairRaw_sound a) (CB1_3_4I2PairP_check a)
def CB1_3_4I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2PairCertificates (CB1_3_4I2PairCertificateIndex a)).output
lemma CB1_3_4I2PairTerms_sound (a : PairSlot) :
    (CB1_3_4I2PairTerms a).Encloses (Foundation.entropyTerm (CB1_3_4I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2PairCertificates_valid
    (CB1_3_4I2PairCertificateIndex a) (CB1_3_4I2PairP_sound a)
def CB1_3_4I2PairEntropy : Ball := ⟨(42104089517135168957866229320237 / 50000000000000000000000000000000), (29258810673 / 50000000000000000000000000000000)⟩
lemma CB1_3_4I2PairEntropy_sound : CB1_3_4I2PairEntropy.Encloses (Foundation.finiteEntropy CB1_3_4I2PairValue) := by
  exact contains_sound (entropyPair_enclosed CB1_3_4I2PairValue CB1_3_4I2PairTerms CB1_3_4I2PairTerms_sound) (by decide +kernel)
def CB1_3_4I2PairMass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
lemma CB1_3_4I2PairMass_sound : CB1_3_4I2PairMass.Encloses (∑ a, CB1_3_4I2PairValue a) := by
  exact contains_sound (pairSumBall_sound CB1_3_4I2PairP CB1_3_4I2PairValue CB1_3_4I2PairP_sound) (by decide +kernel)
def CB1_3_4I2PairMassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def CB1_3_4I2PairMassTermLog : Ball := ⟨0, (661744491 / 1562500000000000000000000000000)⟩
lemma CB1_3_4I2PairMassTermLog_sound : CB1_3_4I2PairMassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_3_4I2PairMass_sound) (w := CB1_3_4I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_3_4I2PairMassTerm : Ball := ⟨0, (1694065897 / 4000000000000000000000000000000)⟩
lemma CB1_3_4I2PairMassTerm_sound : CB1_3_4I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I2PairMass_sound) CB1_3_4I2PairMassTermLog_sound) (by decide +kernel)
def CB1_3_4I2PairH : Ball := ⟨(42104089517135168957866229320237 / 50000000000000000000000000000000), (100869268771 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2PairH_sound : CB1_3_4I2PairH.Encloses (homogeneousEntropy CB1_3_4I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2PairValue CB1_3_4I2PairMassTerm_sound CB1_3_4I2PairEntropy_sound) (by decide +kernel)

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
def CB1_3_4I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 0 a
def CB1_3_4I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 0 a
lemma CB1_3_4I2R0Raw_sound (a : Fin 6) :
    (CB1_3_4I2R0Raw a).Encloses (CB1_3_4I2R0Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 0 a
def CB1_3_4I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18376602916823826473515371739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(39518182540949711406409763533 / 25000000000000000000000000000000), (54479569 / 100000000000000000000000000000000)⟩ ⟨(-860184719010731091912411428528721 / 100000000000000000000000000000000), (296461537003 / 100000000000000000000000000000000)⟩ ⟨-13, 18376602916823826473515371739, 12207031250000000000000000000⟩]
lemma CB1_3_4I2R0Certificates_valid :
    CB1_3_4I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB1_3_4I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R0Certificates (CB1_3_4I2R0CertificateIndex a)).input
lemma CB1_3_4I2R0P_check : ∀ a : Fin 6, contains (CB1_3_4I2R0Raw a) (CB1_3_4I2R0P a) = true := by
  decide +kernel
lemma CB1_3_4I2R0P_sound (a : Fin 6) :
    (CB1_3_4I2R0P a).Encloses (CB1_3_4I2R0Value a) :=
  contains_sound (CB1_3_4I2R0Raw_sound a) (CB1_3_4I2R0P_check a)
def CB1_3_4I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R0Certificates (CB1_3_4I2R0CertificateIndex a)).output
lemma CB1_3_4I2R0Terms_sound (a : Fin 6) :
    (CB1_3_4I2R0Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R0Certificates_valid
    (CB1_3_4I2R0CertificateIndex a) (CB1_3_4I2R0P_sound a)
def CB1_3_4I2R0Entropy : Ball := ⟨(39518182540949711406409763533 / 25000000000000000000000000000000), (54479569 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2R0Entropy_sound : CB1_3_4I2R0Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R0Value CB1_3_4I2R0Terms CB1_3_4I2R0Terms_sound) (by decide +kernel)
def CB1_3_4I2R0Mass : Ball := ⟨(18376602916823826473515371739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2R0Mass_sound : CB1_3_4I2R0Mass.Encloses (∑ a, CB1_3_4I2R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R0P CB1_3_4I2R0Value CB1_3_4I2R0P_sound) (by decide +kernel)
def CB1_3_4I2R0MassTermLogWitness : LogWitness := ⟨-13, 18376602916823826473515371739, 12207031250000000000000000000⟩
def CB1_3_4I2R0MassTermLog : Ball := ⟨(-860184719010731091912411428528721 / 100000000000000000000000000000000), (296461537003 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2R0MassTermLog_sound : CB1_3_4I2R0MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_3_4I2R0Mass_sound) (w := CB1_3_4I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_3_4I2R0MassTerm : Ball := ⟨(39518182540949711406409763533 / 25000000000000000000000000000000), (54479569 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2R0MassTerm_sound : CB1_3_4I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I2R0Mass_sound) CB1_3_4I2R0MassTermLog_sound) (by decide +kernel)
def CB1_3_4I2R0H : Ball := ⟨0, (54479569 / 50000000000000000000000000000000)⟩
lemma CB1_3_4I2R0H_sound : CB1_3_4I2R0H.Encloses (homogeneousEntropy CB1_3_4I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R0Value CB1_3_4I2R0MassTerm_sound CB1_3_4I2R0Entropy_sound) (by decide +kernel)
def CB1_3_4I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 1 a
def CB1_3_4I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 1 a
lemma CB1_3_4I2R1Raw_sound (a : Fin 6) :
    (CB1_3_4I2R1Raw a).Encloses (CB1_3_4I2R1Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 1 a
def CB1_3_4I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1492912089080617619303408645301 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(4207246008919777995755135783277 / 25000000000000000000000000000000), (9484093 / 125000000000000000000000000000)⟩ ⟨(-281814719010731091912411582144759 / 100000000000000000000000000000000), (25410988453 / 20000000000000000000000000000000)⟩ ⟨-5, 1492912089080617619303408645301, 781250000000000000000000000000⟩]
lemma CB1_3_4I2R1Certificates_valid :
    CB1_3_4I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_3_4I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R1Certificates (CB1_3_4I2R1CertificateIndex a)).input
lemma CB1_3_4I2R1P_check : ∀ a : Fin 6, contains (CB1_3_4I2R1Raw a) (CB1_3_4I2R1P a) = true := by
  decide +kernel
lemma CB1_3_4I2R1P_sound (a : Fin 6) :
    (CB1_3_4I2R1P a).Encloses (CB1_3_4I2R1Value a) :=
  contains_sound (CB1_3_4I2R1Raw_sound a) (CB1_3_4I2R1P_check a)
def CB1_3_4I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R1Certificates (CB1_3_4I2R1CertificateIndex a)).output
lemma CB1_3_4I2R1Terms_sound (a : Fin 6) :
    (CB1_3_4I2R1Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R1Certificates_valid
    (CB1_3_4I2R1CertificateIndex a) (CB1_3_4I2R1P_sound a)
def CB1_3_4I2R1Entropy : Ball := ⟨(4207246008919777995755135783277 / 25000000000000000000000000000000), (9484093 / 125000000000000000000000000000)⟩
lemma CB1_3_4I2R1Entropy_sound : CB1_3_4I2R1Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R1Value CB1_3_4I2R1Terms CB1_3_4I2R1Terms_sound) (by decide +kernel)
def CB1_3_4I2R1Mass : Ball := ⟨(1492912089080617619303408645301 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
lemma CB1_3_4I2R1Mass_sound : CB1_3_4I2R1Mass.Encloses (∑ a, CB1_3_4I2R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R1P CB1_3_4I2R1Value CB1_3_4I2R1P_sound) (by decide +kernel)
def CB1_3_4I2R1MassTermLogWitness : LogWitness := ⟨-5, 1492912089080617619303408645301, 781250000000000000000000000000⟩
def CB1_3_4I2R1MassTermLog : Ball := ⟨(-281814719010731091912411582144759 / 100000000000000000000000000000000), (25410988453 / 20000000000000000000000000000000)⟩
lemma CB1_3_4I2R1MassTermLog_sound : CB1_3_4I2R1MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_3_4I2R1Mass_sound) (w := CB1_3_4I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_3_4I2R1MassTerm : Ball := ⟨(4207246008919777995755135783277 / 25000000000000000000000000000000), (9484093 / 125000000000000000000000000000)⟩
lemma CB1_3_4I2R1MassTerm_sound : CB1_3_4I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I2R1Mass_sound) CB1_3_4I2R1MassTermLog_sound) (by decide +kernel)
def CB1_3_4I2R1H : Ball := ⟨0, (9484093 / 62500000000000000000000000000)⟩
lemma CB1_3_4I2R1H_sound : CB1_3_4I2R1H.Encloses (homogeneousEntropy CB1_3_4I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R1Value CB1_3_4I2R1MassTerm_sound CB1_3_4I2R1Entropy_sound) (by decide +kernel)
def CB1_3_4I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 2 a
def CB1_3_4I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 2 a
lemma CB1_3_4I2R2Raw_sound (a : Fin 6) :
    (CB1_3_4I2R2Raw a).Encloses (CB1_3_4I2R2Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 2 a
def CB1_3_4I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(8529923200941003897310520733773 / 20000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(36343951973647162411118151308189 / 100000000000000000000000000000000), (27094222483 / 100000000000000000000000000000000)⟩ ⟨(-42607595774880799680820971983363 / 50000000000000000000000000000000), (63527471077 / 100000000000000000000000000000000)⟩ ⟨-2, 8529923200941003897310520733773, 5000000000000000000000000000000⟩,
   .log ⟨(51412037763131653973193059261 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(194673046550446695019504475839 / 50000000000000000000000000000000), (130643079 / 100000000000000000000000000000000)⟩ ⟨(-757305312220281867581940389558343 / 100000000000000000000000000000000), (12705494307 / 5000000000000000000000000000000)⟩ ⟨-11, 51412037763131653973193059261, 48828125000000000000000000000⟩]
lemma CB1_3_4I2R2Certificates_valid :
    CB1_3_4I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB1_3_4I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R2Certificates (CB1_3_4I2R2CertificateIndex a)).input
lemma CB1_3_4I2R2P_check : ∀ a : Fin 6, contains (CB1_3_4I2R2Raw a) (CB1_3_4I2R2P a) = true := by
  decide +kernel
lemma CB1_3_4I2R2P_sound (a : Fin 6) :
    (CB1_3_4I2R2P a).Encloses (CB1_3_4I2R2Value a) :=
  contains_sound (CB1_3_4I2R2Raw_sound a) (CB1_3_4I2R2P_check a)
def CB1_3_4I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R2Certificates (CB1_3_4I2R2CertificateIndex a)).output
lemma CB1_3_4I2R2Terms_sound (a : Fin 6) :
    (CB1_3_4I2R2Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R2Certificates_valid
    (CB1_3_4I2R2CertificateIndex a) (CB1_3_4I2R2P_sound a)
def CB1_3_4I2R2Entropy : Ball := ⟨(36733298066748055801157160259867 / 100000000000000000000000000000000), (13612432781 / 50000000000000000000000000000000)⟩
lemma CB1_3_4I2R2Entropy_sound : CB1_3_4I2R2Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R2Value CB1_3_4I2R2Terms CB1_3_4I2R2Terms_sound) (by decide +kernel)
def CB1_3_4I2R2Mass : Ball := ⟨(21350514021234075570262898364063 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2R2Mass_sound : CB1_3_4I2R2Mass.Encloses (∑ a, CB1_3_4I2R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R2P CB1_3_4I2R2Value CB1_3_4I2R2P_sound) (by decide +kernel)
def CB1_3_4I2R2MassTermLogWitness : LogWitness := ⟨-2, 21350514021234075570262898364063, 12500000000000000000000000000000⟩
def CB1_3_4I2R2MassTermLog : Ball := ⟨(-85094719010731091912411638578429 / 100000000000000000000000000000000), (63527471079 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2R2MassTermLog_sound : CB1_3_4I2R2MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_3_4I2R2Mass_sound) (w := CB1_3_4I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_3_4I2R2MassTerm : Ball := ⟨(7267263965486352088861529489067 / 20000000000000000000000000000000), (6781720813 / 25000000000000000000000000000000)⟩
lemma CB1_3_4I2R2MassTerm_sound : CB1_3_4I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I2R2Mass_sound) CB1_3_4I2R2MassTermLog_sound) (by decide +kernel)
def CB1_3_4I2R2H : Ball := ⟨(99244559829073839212378203633 / 25000000000000000000000000000000), (27175874407 / 50000000000000000000000000000000)⟩
lemma CB1_3_4I2R2H_sound : CB1_3_4I2R2H.Encloses (homogeneousEntropy CB1_3_4I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R2Value CB1_3_4I2R2MassTerm_sound CB1_3_4I2R2Entropy_sound) (by decide +kernel)
def CB1_3_4I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 3 a
def CB1_3_4I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 3 a
lemma CB1_3_4I2R3Raw_sound (a : Fin 6) :
    (CB1_3_4I2R3Raw a).Encloses (CB1_3_4I2R3Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 3 a
def CB1_3_4I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R3Certificates_valid :
    CB1_3_4I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R3Certificates (CB1_3_4I2R3CertificateIndex a)).input
lemma CB1_3_4I2R3P_check : ∀ a : Fin 6, contains (CB1_3_4I2R3Raw a) (CB1_3_4I2R3P a) = true := by
  decide +kernel
lemma CB1_3_4I2R3P_sound (a : Fin 6) :
    (CB1_3_4I2R3P a).Encloses (CB1_3_4I2R3Value a) :=
  contains_sound (CB1_3_4I2R3Raw_sound a) (CB1_3_4I2R3P_check a)
def CB1_3_4I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R3Certificates (CB1_3_4I2R3CertificateIndex a)).output
lemma CB1_3_4I2R3Terms_sound (a : Fin 6) :
    (CB1_3_4I2R3Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R3Certificates_valid
    (CB1_3_4I2R3CertificateIndex a) (CB1_3_4I2R3P_sound a)
def CB1_3_4I2R3Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R3Entropy_sound : CB1_3_4I2R3Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R3Value CB1_3_4I2R3Terms CB1_3_4I2R3Terms_sound) (by decide +kernel)
def CB1_3_4I2R3Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R3Mass_sound : CB1_3_4I2R3Mass.Encloses (∑ a, CB1_3_4I2R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R3P CB1_3_4I2R3Value CB1_3_4I2R3P_sound) (by decide +kernel)
def CB1_3_4I2R3MassTerm : Ball := .exact 0
lemma CB1_3_4I2R3MassTerm_sound : CB1_3_4I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R3Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R3Mass_sound)
def CB1_3_4I2R3H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R3H_sound : CB1_3_4I2R3H.Encloses (homogeneousEntropy CB1_3_4I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R3Value CB1_3_4I2R3MassTerm_sound CB1_3_4I2R3Entropy_sound) (by decide +kernel)
def CB1_3_4I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 4 a
def CB1_3_4I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 4 a
lemma CB1_3_4I2R4Raw_sound (a : Fin 6) :
    (CB1_3_4I2R4Raw a).Encloses (CB1_3_4I2R4Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 4 a
def CB1_3_4I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R4Certificates_valid :
    CB1_3_4I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R4Certificates (CB1_3_4I2R4CertificateIndex a)).input
lemma CB1_3_4I2R4P_check : ∀ a : Fin 6, contains (CB1_3_4I2R4Raw a) (CB1_3_4I2R4P a) = true := by
  decide +kernel
lemma CB1_3_4I2R4P_sound (a : Fin 6) :
    (CB1_3_4I2R4P a).Encloses (CB1_3_4I2R4Value a) :=
  contains_sound (CB1_3_4I2R4Raw_sound a) (CB1_3_4I2R4P_check a)
def CB1_3_4I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R4Certificates (CB1_3_4I2R4CertificateIndex a)).output
lemma CB1_3_4I2R4Terms_sound (a : Fin 6) :
    (CB1_3_4I2R4Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R4Certificates_valid
    (CB1_3_4I2R4CertificateIndex a) (CB1_3_4I2R4P_sound a)
def CB1_3_4I2R4Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R4Entropy_sound : CB1_3_4I2R4Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R4Value CB1_3_4I2R4Terms CB1_3_4I2R4Terms_sound) (by decide +kernel)
def CB1_3_4I2R4Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R4Mass_sound : CB1_3_4I2R4Mass.Encloses (∑ a, CB1_3_4I2R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R4P CB1_3_4I2R4Value CB1_3_4I2R4P_sound) (by decide +kernel)
def CB1_3_4I2R4MassTerm : Ball := .exact 0
lemma CB1_3_4I2R4MassTerm_sound : CB1_3_4I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R4Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R4Mass_sound)
def CB1_3_4I2R4H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R4H_sound : CB1_3_4I2R4H.Encloses (homogeneousEntropy CB1_3_4I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R4Value CB1_3_4I2R4MassTerm_sound CB1_3_4I2R4Entropy_sound) (by decide +kernel)
def CB1_3_4I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 5 a
def CB1_3_4I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 5 a
lemma CB1_3_4I2R5Raw_sound (a : Fin 6) :
    (CB1_3_4I2R5Raw a).Encloses (CB1_3_4I2R5Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 5 a
def CB1_3_4I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R5Certificates_valid :
    CB1_3_4I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R5Certificates (CB1_3_4I2R5CertificateIndex a)).input
lemma CB1_3_4I2R5P_check : ∀ a : Fin 6, contains (CB1_3_4I2R5Raw a) (CB1_3_4I2R5P a) = true := by
  decide +kernel
lemma CB1_3_4I2R5P_sound (a : Fin 6) :
    (CB1_3_4I2R5P a).Encloses (CB1_3_4I2R5Value a) :=
  contains_sound (CB1_3_4I2R5Raw_sound a) (CB1_3_4I2R5P_check a)
def CB1_3_4I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R5Certificates (CB1_3_4I2R5CertificateIndex a)).output
lemma CB1_3_4I2R5Terms_sound (a : Fin 6) :
    (CB1_3_4I2R5Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R5Certificates_valid
    (CB1_3_4I2R5CertificateIndex a) (CB1_3_4I2R5P_sound a)
def CB1_3_4I2R5Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R5Entropy_sound : CB1_3_4I2R5Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R5Value CB1_3_4I2R5Terms CB1_3_4I2R5Terms_sound) (by decide +kernel)
def CB1_3_4I2R5Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R5Mass_sound : CB1_3_4I2R5Mass.Encloses (∑ a, CB1_3_4I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R5P CB1_3_4I2R5Value CB1_3_4I2R5P_sound) (by decide +kernel)
def CB1_3_4I2R5MassTerm : Ball := .exact 0
lemma CB1_3_4I2R5MassTerm_sound : CB1_3_4I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R5Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R5Mass_sound)
def CB1_3_4I2R5H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R5H_sound : CB1_3_4I2R5H.Encloses (homogeneousEntropy CB1_3_4I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R5Value CB1_3_4I2R5MassTerm_sound CB1_3_4I2R5Entropy_sound) (by decide +kernel)
def CB1_3_4I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 6 a
def CB1_3_4I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 6 a
lemma CB1_3_4I2R6Raw_sound (a : Fin 6) :
    (CB1_3_4I2R6Raw a).Encloses (CB1_3_4I2R6Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 6 a
def CB1_3_4I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R6Certificates_valid :
    CB1_3_4I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R6Certificates (CB1_3_4I2R6CertificateIndex a)).input
lemma CB1_3_4I2R6P_check : ∀ a : Fin 6, contains (CB1_3_4I2R6Raw a) (CB1_3_4I2R6P a) = true := by
  decide +kernel
lemma CB1_3_4I2R6P_sound (a : Fin 6) :
    (CB1_3_4I2R6P a).Encloses (CB1_3_4I2R6Value a) :=
  contains_sound (CB1_3_4I2R6Raw_sound a) (CB1_3_4I2R6P_check a)
def CB1_3_4I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R6Certificates (CB1_3_4I2R6CertificateIndex a)).output
lemma CB1_3_4I2R6Terms_sound (a : Fin 6) :
    (CB1_3_4I2R6Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R6Certificates_valid
    (CB1_3_4I2R6CertificateIndex a) (CB1_3_4I2R6P_sound a)
def CB1_3_4I2R6Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R6Entropy_sound : CB1_3_4I2R6Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R6Value CB1_3_4I2R6Terms CB1_3_4I2R6Terms_sound) (by decide +kernel)
def CB1_3_4I2R6Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R6Mass_sound : CB1_3_4I2R6Mass.Encloses (∑ a, CB1_3_4I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R6P CB1_3_4I2R6Value CB1_3_4I2R6P_sound) (by decide +kernel)
def CB1_3_4I2R6MassTerm : Ball := .exact 0
lemma CB1_3_4I2R6MassTerm_sound : CB1_3_4I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R6Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R6Mass_sound)
def CB1_3_4I2R6H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R6H_sound : CB1_3_4I2R6H.Encloses (homogeneousEntropy CB1_3_4I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R6Value CB1_3_4I2R6MassTerm_sound CB1_3_4I2R6Entropy_sound) (by decide +kernel)
def CB1_3_4I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 7 a
def CB1_3_4I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 7 a
lemma CB1_3_4I2R7Raw_sound (a : Fin 6) :
    (CB1_3_4I2R7Raw a).Encloses (CB1_3_4I2R7Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 7 a
def CB1_3_4I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R7Certificates_valid :
    CB1_3_4I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R7Certificates (CB1_3_4I2R7CertificateIndex a)).input
lemma CB1_3_4I2R7P_check : ∀ a : Fin 6, contains (CB1_3_4I2R7Raw a) (CB1_3_4I2R7P a) = true := by
  decide +kernel
lemma CB1_3_4I2R7P_sound (a : Fin 6) :
    (CB1_3_4I2R7P a).Encloses (CB1_3_4I2R7Value a) :=
  contains_sound (CB1_3_4I2R7Raw_sound a) (CB1_3_4I2R7P_check a)
def CB1_3_4I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R7Certificates (CB1_3_4I2R7CertificateIndex a)).output
lemma CB1_3_4I2R7Terms_sound (a : Fin 6) :
    (CB1_3_4I2R7Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R7Certificates_valid
    (CB1_3_4I2R7CertificateIndex a) (CB1_3_4I2R7P_sound a)
def CB1_3_4I2R7Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R7Entropy_sound : CB1_3_4I2R7Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R7Value CB1_3_4I2R7Terms CB1_3_4I2R7Terms_sound) (by decide +kernel)
def CB1_3_4I2R7Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R7Mass_sound : CB1_3_4I2R7Mass.Encloses (∑ a, CB1_3_4I2R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R7P CB1_3_4I2R7Value CB1_3_4I2R7P_sound) (by decide +kernel)
def CB1_3_4I2R7MassTerm : Ball := .exact 0
lemma CB1_3_4I2R7MassTerm_sound : CB1_3_4I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R7Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R7Mass_sound)
def CB1_3_4I2R7H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R7H_sound : CB1_3_4I2R7H.Encloses (homogeneousEntropy CB1_3_4I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R7Value CB1_3_4I2R7MassTerm_sound CB1_3_4I2R7Entropy_sound) (by decide +kernel)
def CB1_3_4I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 8 a
def CB1_3_4I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 8 a
lemma CB1_3_4I2R8Raw_sound (a : Fin 6) :
    (CB1_3_4I2R8Raw a).Encloses (CB1_3_4I2R8Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 8 a
def CB1_3_4I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R8Certificates_valid :
    CB1_3_4I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R8Certificates (CB1_3_4I2R8CertificateIndex a)).input
lemma CB1_3_4I2R8P_check : ∀ a : Fin 6, contains (CB1_3_4I2R8Raw a) (CB1_3_4I2R8P a) = true := by
  decide +kernel
lemma CB1_3_4I2R8P_sound (a : Fin 6) :
    (CB1_3_4I2R8P a).Encloses (CB1_3_4I2R8Value a) :=
  contains_sound (CB1_3_4I2R8Raw_sound a) (CB1_3_4I2R8P_check a)
def CB1_3_4I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R8Certificates (CB1_3_4I2R8CertificateIndex a)).output
lemma CB1_3_4I2R8Terms_sound (a : Fin 6) :
    (CB1_3_4I2R8Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R8Certificates_valid
    (CB1_3_4I2R8CertificateIndex a) (CB1_3_4I2R8P_sound a)
def CB1_3_4I2R8Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R8Entropy_sound : CB1_3_4I2R8Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R8Value CB1_3_4I2R8Terms CB1_3_4I2R8Terms_sound) (by decide +kernel)
def CB1_3_4I2R8Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R8Mass_sound : CB1_3_4I2R8Mass.Encloses (∑ a, CB1_3_4I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R8P CB1_3_4I2R8Value CB1_3_4I2R8P_sound) (by decide +kernel)
def CB1_3_4I2R8MassTerm : Ball := .exact 0
lemma CB1_3_4I2R8MassTerm_sound : CB1_3_4I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R8Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R8Mass_sound)
def CB1_3_4I2R8H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R8H_sound : CB1_3_4I2R8H.Encloses (homogeneousEntropy CB1_3_4I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R8Value CB1_3_4I2R8MassTerm_sound CB1_3_4I2R8Entropy_sound) (by decide +kernel)
def CB1_3_4I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 9 a
def CB1_3_4I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 9 a
lemma CB1_3_4I2R9Raw_sound (a : Fin 6) :
    (CB1_3_4I2R9Raw a).Encloses (CB1_3_4I2R9Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 9 a
def CB1_3_4I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R9Certificates_valid :
    CB1_3_4I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R9Certificates (CB1_3_4I2R9CertificateIndex a)).input
lemma CB1_3_4I2R9P_check : ∀ a : Fin 6, contains (CB1_3_4I2R9Raw a) (CB1_3_4I2R9P a) = true := by
  decide +kernel
lemma CB1_3_4I2R9P_sound (a : Fin 6) :
    (CB1_3_4I2R9P a).Encloses (CB1_3_4I2R9Value a) :=
  contains_sound (CB1_3_4I2R9Raw_sound a) (CB1_3_4I2R9P_check a)
def CB1_3_4I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R9Certificates (CB1_3_4I2R9CertificateIndex a)).output
lemma CB1_3_4I2R9Terms_sound (a : Fin 6) :
    (CB1_3_4I2R9Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R9Certificates_valid
    (CB1_3_4I2R9CertificateIndex a) (CB1_3_4I2R9P_sound a)
def CB1_3_4I2R9Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R9Entropy_sound : CB1_3_4I2R9Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R9Value CB1_3_4I2R9Terms CB1_3_4I2R9Terms_sound) (by decide +kernel)
def CB1_3_4I2R9Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R9Mass_sound : CB1_3_4I2R9Mass.Encloses (∑ a, CB1_3_4I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R9P CB1_3_4I2R9Value CB1_3_4I2R9P_sound) (by decide +kernel)
def CB1_3_4I2R9MassTerm : Ball := .exact 0
lemma CB1_3_4I2R9MassTerm_sound : CB1_3_4I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R9Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R9Mass_sound)
def CB1_3_4I2R9H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R9H_sound : CB1_3_4I2R9H.Encloses (homogeneousEntropy CB1_3_4I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R9Value CB1_3_4I2R9MassTerm_sound CB1_3_4I2R9Entropy_sound) (by decide +kernel)
def CB1_3_4I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 10 a
def CB1_3_4I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 10 a
lemma CB1_3_4I2R10Raw_sound (a : Fin 6) :
    (CB1_3_4I2R10Raw a).Encloses (CB1_3_4I2R10Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 10 a
def CB1_3_4I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R10Certificates_valid :
    CB1_3_4I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R10Certificates (CB1_3_4I2R10CertificateIndex a)).input
lemma CB1_3_4I2R10P_check : ∀ a : Fin 6, contains (CB1_3_4I2R10Raw a) (CB1_3_4I2R10P a) = true := by
  decide +kernel
lemma CB1_3_4I2R10P_sound (a : Fin 6) :
    (CB1_3_4I2R10P a).Encloses (CB1_3_4I2R10Value a) :=
  contains_sound (CB1_3_4I2R10Raw_sound a) (CB1_3_4I2R10P_check a)
def CB1_3_4I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R10Certificates (CB1_3_4I2R10CertificateIndex a)).output
lemma CB1_3_4I2R10Terms_sound (a : Fin 6) :
    (CB1_3_4I2R10Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R10Certificates_valid
    (CB1_3_4I2R10CertificateIndex a) (CB1_3_4I2R10P_sound a)
def CB1_3_4I2R10Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R10Entropy_sound : CB1_3_4I2R10Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R10Value CB1_3_4I2R10Terms CB1_3_4I2R10Terms_sound) (by decide +kernel)
def CB1_3_4I2R10Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R10Mass_sound : CB1_3_4I2R10Mass.Encloses (∑ a, CB1_3_4I2R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R10P CB1_3_4I2R10Value CB1_3_4I2R10P_sound) (by decide +kernel)
def CB1_3_4I2R10MassTerm : Ball := .exact 0
lemma CB1_3_4I2R10MassTerm_sound : CB1_3_4I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R10Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R10Mass_sound)
def CB1_3_4I2R10H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R10H_sound : CB1_3_4I2R10H.Encloses (homogeneousEntropy CB1_3_4I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R10Value CB1_3_4I2R10MassTerm_sound CB1_3_4I2R10Entropy_sound) (by decide +kernel)
def CB1_3_4I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 11 a
def CB1_3_4I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 11 a
lemma CB1_3_4I2R11Raw_sound (a : Fin 6) :
    (CB1_3_4I2R11Raw a).Encloses (CB1_3_4I2R11Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 11 a
def CB1_3_4I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R11Certificates_valid :
    CB1_3_4I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R11Certificates (CB1_3_4I2R11CertificateIndex a)).input
lemma CB1_3_4I2R11P_check : ∀ a : Fin 6, contains (CB1_3_4I2R11Raw a) (CB1_3_4I2R11P a) = true := by
  decide +kernel
lemma CB1_3_4I2R11P_sound (a : Fin 6) :
    (CB1_3_4I2R11P a).Encloses (CB1_3_4I2R11Value a) :=
  contains_sound (CB1_3_4I2R11Raw_sound a) (CB1_3_4I2R11P_check a)
def CB1_3_4I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R11Certificates (CB1_3_4I2R11CertificateIndex a)).output
lemma CB1_3_4I2R11Terms_sound (a : Fin 6) :
    (CB1_3_4I2R11Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R11Certificates_valid
    (CB1_3_4I2R11CertificateIndex a) (CB1_3_4I2R11P_sound a)
def CB1_3_4I2R11Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R11Entropy_sound : CB1_3_4I2R11Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R11Value CB1_3_4I2R11Terms CB1_3_4I2R11Terms_sound) (by decide +kernel)
def CB1_3_4I2R11Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R11Mass_sound : CB1_3_4I2R11Mass.Encloses (∑ a, CB1_3_4I2R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R11P CB1_3_4I2R11Value CB1_3_4I2R11P_sound) (by decide +kernel)
def CB1_3_4I2R11MassTerm : Ball := .exact 0
lemma CB1_3_4I2R11MassTerm_sound : CB1_3_4I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R11Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R11Mass_sound)
def CB1_3_4I2R11H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R11H_sound : CB1_3_4I2R11H.Encloses (homogeneousEntropy CB1_3_4I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R11Value CB1_3_4I2R11MassTerm_sound CB1_3_4I2R11Entropy_sound) (by decide +kernel)
def CB1_3_4I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 12 a
def CB1_3_4I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 12 a
lemma CB1_3_4I2R12Raw_sound (a : Fin 6) :
    (CB1_3_4I2R12Raw a).Encloses (CB1_3_4I2R12Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 12 a
def CB1_3_4I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R12Certificates_valid :
    CB1_3_4I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R12Certificates (CB1_3_4I2R12CertificateIndex a)).input
lemma CB1_3_4I2R12P_check : ∀ a : Fin 6, contains (CB1_3_4I2R12Raw a) (CB1_3_4I2R12P a) = true := by
  decide +kernel
lemma CB1_3_4I2R12P_sound (a : Fin 6) :
    (CB1_3_4I2R12P a).Encloses (CB1_3_4I2R12Value a) :=
  contains_sound (CB1_3_4I2R12Raw_sound a) (CB1_3_4I2R12P_check a)
def CB1_3_4I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R12Certificates (CB1_3_4I2R12CertificateIndex a)).output
lemma CB1_3_4I2R12Terms_sound (a : Fin 6) :
    (CB1_3_4I2R12Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R12Certificates_valid
    (CB1_3_4I2R12CertificateIndex a) (CB1_3_4I2R12P_sound a)
def CB1_3_4I2R12Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R12Entropy_sound : CB1_3_4I2R12Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R12Value CB1_3_4I2R12Terms CB1_3_4I2R12Terms_sound) (by decide +kernel)
def CB1_3_4I2R12Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R12Mass_sound : CB1_3_4I2R12Mass.Encloses (∑ a, CB1_3_4I2R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R12P CB1_3_4I2R12Value CB1_3_4I2R12P_sound) (by decide +kernel)
def CB1_3_4I2R12MassTerm : Ball := .exact 0
lemma CB1_3_4I2R12MassTerm_sound : CB1_3_4I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R12Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R12Mass_sound)
def CB1_3_4I2R12H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R12H_sound : CB1_3_4I2R12H.Encloses (homogeneousEntropy CB1_3_4I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R12Value CB1_3_4I2R12MassTerm_sound CB1_3_4I2R12Entropy_sound) (by decide +kernel)
def CB1_3_4I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 13 a
def CB1_3_4I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 13 a
lemma CB1_3_4I2R13Raw_sound (a : Fin 6) :
    (CB1_3_4I2R13Raw a).Encloses (CB1_3_4I2R13Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 13 a
def CB1_3_4I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R13Certificates_valid :
    CB1_3_4I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R13Certificates (CB1_3_4I2R13CertificateIndex a)).input
lemma CB1_3_4I2R13P_check : ∀ a : Fin 6, contains (CB1_3_4I2R13Raw a) (CB1_3_4I2R13P a) = true := by
  decide +kernel
lemma CB1_3_4I2R13P_sound (a : Fin 6) :
    (CB1_3_4I2R13P a).Encloses (CB1_3_4I2R13Value a) :=
  contains_sound (CB1_3_4I2R13Raw_sound a) (CB1_3_4I2R13P_check a)
def CB1_3_4I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R13Certificates (CB1_3_4I2R13CertificateIndex a)).output
lemma CB1_3_4I2R13Terms_sound (a : Fin 6) :
    (CB1_3_4I2R13Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R13Certificates_valid
    (CB1_3_4I2R13CertificateIndex a) (CB1_3_4I2R13P_sound a)
def CB1_3_4I2R13Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R13Entropy_sound : CB1_3_4I2R13Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R13Value CB1_3_4I2R13Terms CB1_3_4I2R13Terms_sound) (by decide +kernel)
def CB1_3_4I2R13Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R13Mass_sound : CB1_3_4I2R13Mass.Encloses (∑ a, CB1_3_4I2R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R13P CB1_3_4I2R13Value CB1_3_4I2R13P_sound) (by decide +kernel)
def CB1_3_4I2R13MassTerm : Ball := .exact 0
lemma CB1_3_4I2R13MassTerm_sound : CB1_3_4I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R13Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R13Mass_sound)
def CB1_3_4I2R13H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R13H_sound : CB1_3_4I2R13H.Encloses (homogeneousEntropy CB1_3_4I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R13Value CB1_3_4I2R13MassTerm_sound CB1_3_4I2R13Entropy_sound) (by decide +kernel)
def CB1_3_4I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 14 a
def CB1_3_4I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 14 a
lemma CB1_3_4I2R14Raw_sound (a : Fin 6) :
    (CB1_3_4I2R14Raw a).Encloses (CB1_3_4I2R14Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 14 a
def CB1_3_4I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R14Certificates_valid :
    CB1_3_4I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R14Certificates (CB1_3_4I2R14CertificateIndex a)).input
lemma CB1_3_4I2R14P_check : ∀ a : Fin 6, contains (CB1_3_4I2R14Raw a) (CB1_3_4I2R14P a) = true := by
  decide +kernel
lemma CB1_3_4I2R14P_sound (a : Fin 6) :
    (CB1_3_4I2R14P a).Encloses (CB1_3_4I2R14Value a) :=
  contains_sound (CB1_3_4I2R14Raw_sound a) (CB1_3_4I2R14P_check a)
def CB1_3_4I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R14Certificates (CB1_3_4I2R14CertificateIndex a)).output
lemma CB1_3_4I2R14Terms_sound (a : Fin 6) :
    (CB1_3_4I2R14Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R14Certificates_valid
    (CB1_3_4I2R14CertificateIndex a) (CB1_3_4I2R14P_sound a)
def CB1_3_4I2R14Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R14Entropy_sound : CB1_3_4I2R14Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R14Value CB1_3_4I2R14Terms CB1_3_4I2R14Terms_sound) (by decide +kernel)
def CB1_3_4I2R14Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R14Mass_sound : CB1_3_4I2R14Mass.Encloses (∑ a, CB1_3_4I2R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R14P CB1_3_4I2R14Value CB1_3_4I2R14P_sound) (by decide +kernel)
def CB1_3_4I2R14MassTerm : Ball := .exact 0
lemma CB1_3_4I2R14MassTerm_sound : CB1_3_4I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R14Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R14Mass_sound)
def CB1_3_4I2R14H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R14H_sound : CB1_3_4I2R14H.Encloses (homogeneousEntropy CB1_3_4I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R14Value CB1_3_4I2R14MassTerm_sound CB1_3_4I2R14Entropy_sound) (by decide +kernel)
def CB1_3_4I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 15 a
def CB1_3_4I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 15 a
lemma CB1_3_4I2R15Raw_sound (a : Fin 6) :
    (CB1_3_4I2R15Raw a).Encloses (CB1_3_4I2R15Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 15 a
def CB1_3_4I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R15Certificates_valid :
    CB1_3_4I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R15Certificates (CB1_3_4I2R15CertificateIndex a)).input
lemma CB1_3_4I2R15P_check : ∀ a : Fin 6, contains (CB1_3_4I2R15Raw a) (CB1_3_4I2R15P a) = true := by
  decide +kernel
lemma CB1_3_4I2R15P_sound (a : Fin 6) :
    (CB1_3_4I2R15P a).Encloses (CB1_3_4I2R15Value a) :=
  contains_sound (CB1_3_4I2R15Raw_sound a) (CB1_3_4I2R15P_check a)
def CB1_3_4I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R15Certificates (CB1_3_4I2R15CertificateIndex a)).output
lemma CB1_3_4I2R15Terms_sound (a : Fin 6) :
    (CB1_3_4I2R15Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R15Certificates_valid
    (CB1_3_4I2R15CertificateIndex a) (CB1_3_4I2R15P_sound a)
def CB1_3_4I2R15Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R15Entropy_sound : CB1_3_4I2R15Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R15Value CB1_3_4I2R15Terms CB1_3_4I2R15Terms_sound) (by decide +kernel)
def CB1_3_4I2R15Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R15Mass_sound : CB1_3_4I2R15Mass.Encloses (∑ a, CB1_3_4I2R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R15P CB1_3_4I2R15Value CB1_3_4I2R15P_sound) (by decide +kernel)
def CB1_3_4I2R15MassTerm : Ball := .exact 0
lemma CB1_3_4I2R15MassTerm_sound : CB1_3_4I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R15Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R15Mass_sound)
def CB1_3_4I2R15H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R15H_sound : CB1_3_4I2R15H.Encloses (homogeneousEntropy CB1_3_4I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R15Value CB1_3_4I2R15MassTerm_sound CB1_3_4I2R15Entropy_sound) (by decide +kernel)
def CB1_3_4I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) 16 a
def CB1_3_4I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 1 3 4)) B1_3_4Law (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) 16 a
lemma CB1_3_4I2R16Raw_sound (a : Fin 6) :
    (CB1_3_4I2R16Raw a).Encloses (CB1_3_4I2R16Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 2)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 2) a) 16 a
def CB1_3_4I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_3_4I2R16Certificates_valid :
    CB1_3_4I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_3_4I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R16Certificates (CB1_3_4I2R16CertificateIndex a)).input
lemma CB1_3_4I2R16P_check : ∀ a : Fin 6, contains (CB1_3_4I2R16Raw a) (CB1_3_4I2R16P a) = true := by
  decide +kernel
lemma CB1_3_4I2R16P_sound (a : Fin 6) :
    (CB1_3_4I2R16P a).Encloses (CB1_3_4I2R16Value a) :=
  contains_sound (CB1_3_4I2R16Raw_sound a) (CB1_3_4I2R16P_check a)
def CB1_3_4I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_3_4I2R16Certificates (CB1_3_4I2R16CertificateIndex a)).output
lemma CB1_3_4I2R16Terms_sound (a : Fin 6) :
    (CB1_3_4I2R16Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I2R16Certificates_valid
    (CB1_3_4I2R16CertificateIndex a) (CB1_3_4I2R16P_sound a)
def CB1_3_4I2R16Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R16Entropy_sound : CB1_3_4I2R16Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2R16Value CB1_3_4I2R16Terms CB1_3_4I2R16Terms_sound) (by decide +kernel)
def CB1_3_4I2R16Mass : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R16Mass_sound : CB1_3_4I2R16Mass.Encloses (∑ a, CB1_3_4I2R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I2R16P CB1_3_4I2R16Value CB1_3_4I2R16P_sound) (by decide +kernel)
def CB1_3_4I2R16MassTerm : Ball := .exact 0
lemma CB1_3_4I2R16MassTerm_sound : CB1_3_4I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2R16Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I2R16Mass_sound)
def CB1_3_4I2R16H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2R16H_sound : CB1_3_4I2R16H.Encloses (homogeneousEntropy CB1_3_4I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2R16Value CB1_3_4I2R16MassTerm_sound CB1_3_4I2R16Entropy_sound) (by decide +kernel)
def CB1_3_4I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_3_4I2R0H
  | 1 => CB1_3_4I2R1H
  | 2 => CB1_3_4I2R2H
  | 3 => CB1_3_4I2R3H
  | 4 => CB1_3_4I2R4H
  | 5 => CB1_3_4I2R5H
  | 6 => CB1_3_4I2R6H
  | 7 => CB1_3_4I2R7H
  | 8 => CB1_3_4I2R8H
  | 9 => CB1_3_4I2R9H
  | 10 => CB1_3_4I2R10H
  | 11 => CB1_3_4I2R11H
  | 12 => CB1_3_4I2R12H
  | 13 => CB1_3_4I2R13H
  | 14 => CB1_3_4I2R14H
  | 15 => CB1_3_4I2R15H
  | 16 => CB1_3_4I2R16H
  | _ => (.exact 0)
lemma CB1_3_4I2ResidualEntropies_sound (k : Fin 17) :
    (CB1_3_4I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB1_3_4I2R0H_sound
  · exact CB1_3_4I2R1H_sound
  · exact CB1_3_4I2R2H_sound
  · exact CB1_3_4I2R3H_sound
  · exact CB1_3_4I2R4H_sound
  · exact CB1_3_4I2R5H_sound
  · exact CB1_3_4I2R6H_sound
  · exact CB1_3_4I2R7H_sound
  · exact CB1_3_4I2R8H_sound
  · exact CB1_3_4I2R9H_sound
  · exact CB1_3_4I2R10H_sound
  · exact CB1_3_4I2R11H_sound
  · exact CB1_3_4I2R12H_sound
  · exact CB1_3_4I2R13H_sound
  · exact CB1_3_4I2R14H_sound
  · exact CB1_3_4I2R15H_sound
  · exact CB1_3_4I2R16H_sound
def CB1_3_4I2S0_0_4Value (a : Fin 6) : ℝ := (littleLaw (shape 1 3 4) (shape 0 0 4) ((stageBPriority (shape 1 3 4)) 2) a : ℝ)
def CB1_3_4I2S0_0_4E_5Log : Ball := .exact 0
lemma CB1_3_4I2S0_0_4E_5Log_sound : CB1_3_4I2S0_0_4E_5Log.Encloses (Real.log (CB1_3_4I2S0_0_4Value (5 : Fin 6))) := by
  exact log_exact_one_ball ((B1_3_4Little_sound (shape 0 0 4) ((stageBPriority (shape 1 3 4)) 2)) (5 : Fin 6))
def CB1_3_4I2S0_0_4E_5 : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_0_4E_5_sound : CB1_3_4I2S0_0_4E_5.Encloses (Foundation.entropyTerm (CB1_3_4I2S0_0_4Value (5 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_3_4Little_sound (shape 0 0 4) ((stageBPriority (shape 1 3 4)) 2)) (5 : Fin 6)) CB1_3_4I2S0_0_4E_5Log_sound) (by decide +kernel)
def CB1_3_4I2S0_0_4Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB1_3_4I2S0_0_4Terms_sound (a : Fin 6) :
    (CB1_3_4I2S0_0_4Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2S0_0_4Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 0 4) ((stageBPriority (shape 1 3 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 0 4) ((stageBPriority (shape 1 3 4)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 0 4) ((stageBPriority (shape 1 3 4)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 0 4) ((stageBPriority (shape 1 3 4)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 0 4) ((stageBPriority (shape 1 3 4)) 2)) (4 : Fin 6)))
  · exact CB1_3_4I2S0_0_4E_5_sound
def CB1_3_4I2S0_0_4Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_0_4Entropy_sound : CB1_3_4I2S0_0_4Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2S0_0_4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2S0_0_4Value CB1_3_4I2S0_0_4Terms CB1_3_4I2S0_0_4Terms_sound) (by decide +kernel)
def CB1_3_4I2S0_0_4Mass : Ball := ⟨1, 0⟩
lemma CB1_3_4I2S0_0_4Mass_sound : CB1_3_4I2S0_0_4Mass.Encloses (∑ a, CB1_3_4I2S0_0_4Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_3_4Little (shape 0 0 4) ((stageBPriority (shape 1 3 4)) 2)) CB1_3_4I2S0_0_4Value (B1_3_4Little_sound (shape 0 0 4) ((stageBPriority (shape 1 3 4)) 2))) (by decide +kernel)
def CB1_3_4I2S0_0_4MassTermLog : Ball := .exact 0
lemma CB1_3_4I2S0_0_4MassTermLog_sound : CB1_3_4I2S0_0_4MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I2S0_0_4Value a))) := by
  exact log_exact_one_ball (CB1_3_4I2S0_0_4Mass_sound)
def CB1_3_4I2S0_0_4MassTerm : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_0_4MassTerm_sound : CB1_3_4I2S0_0_4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2S0_0_4Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I2S0_0_4Mass_sound) CB1_3_4I2S0_0_4MassTermLog_sound) (by decide +kernel)
def CB1_3_4I2S0_0_4H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_0_4H_sound : CB1_3_4I2S0_0_4H.Encloses (homogeneousEntropy CB1_3_4I2S0_0_4Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2S0_0_4Value CB1_3_4I2S0_0_4MassTerm_sound CB1_3_4I2S0_0_4Entropy_sound) (by decide +kernel)
def CB1_3_4I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 3 4) (shape 0 1 3) ((stageBPriority (shape 1 3 4)) 2) a : ℝ)
def CB1_3_4I2S0_1_3E_4Log : Ball := .exact 0
lemma CB1_3_4I2S0_1_3E_4Log_sound : CB1_3_4I2S0_1_3E_4Log.Encloses (Real.log (CB1_3_4I2S0_1_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B1_3_4Little_sound (shape 0 1 3) ((stageBPriority (shape 1 3 4)) 2)) (4 : Fin 6))
def CB1_3_4I2S0_1_3E_4 : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_1_3E_4_sound : CB1_3_4I2S0_1_3E_4.Encloses (Foundation.entropyTerm (CB1_3_4I2S0_1_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_3_4Little_sound (shape 0 1 3) ((stageBPriority (shape 1 3 4)) 2)) (4 : Fin 6)) CB1_3_4I2S0_1_3E_4Log_sound) (by decide +kernel)
def CB1_3_4I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB1_3_4I2S0_1_3Terms_sound (a : Fin 6) :
    (CB1_3_4I2S0_1_3Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2S0_1_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 1 3) ((stageBPriority (shape 1 3 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 1 3) ((stageBPriority (shape 1 3 4)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 1 3) ((stageBPriority (shape 1 3 4)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 1 3) ((stageBPriority (shape 1 3 4)) 2)) (3 : Fin 6)))
  · exact CB1_3_4I2S0_1_3E_4_sound
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 1 3) ((stageBPriority (shape 1 3 4)) 2)) (5 : Fin 6)))
def CB1_3_4I2S0_1_3Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_1_3Entropy_sound : CB1_3_4I2S0_1_3Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2S0_1_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2S0_1_3Value CB1_3_4I2S0_1_3Terms CB1_3_4I2S0_1_3Terms_sound) (by decide +kernel)
def CB1_3_4I2S0_1_3Mass : Ball := ⟨1, 0⟩
lemma CB1_3_4I2S0_1_3Mass_sound : CB1_3_4I2S0_1_3Mass.Encloses (∑ a, CB1_3_4I2S0_1_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_3_4Little (shape 0 1 3) ((stageBPriority (shape 1 3 4)) 2)) CB1_3_4I2S0_1_3Value (B1_3_4Little_sound (shape 0 1 3) ((stageBPriority (shape 1 3 4)) 2))) (by decide +kernel)
def CB1_3_4I2S0_1_3MassTermLog : Ball := .exact 0
lemma CB1_3_4I2S0_1_3MassTermLog_sound : CB1_3_4I2S0_1_3MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I2S0_1_3Value a))) := by
  exact log_exact_one_ball (CB1_3_4I2S0_1_3Mass_sound)
def CB1_3_4I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_1_3MassTerm_sound : CB1_3_4I2S0_1_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2S0_1_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I2S0_1_3Mass_sound) CB1_3_4I2S0_1_3MassTermLog_sound) (by decide +kernel)
def CB1_3_4I2S0_1_3H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_1_3H_sound : CB1_3_4I2S0_1_3H.Encloses (homogeneousEntropy CB1_3_4I2S0_1_3Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2S0_1_3Value CB1_3_4I2S0_1_3MassTerm_sound CB1_3_4I2S0_1_3Entropy_sound) (by decide +kernel)
def CB1_3_4I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 1 3 4) (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2) a : ℝ)
def CB1_3_4I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 453517, 250000⟩
def CB1_3_4I2S0_2_2E_2Log : Ball := ⟨(-609845895945556733363202867553 / 6250000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma CB1_3_4I2S0_2_2E_2Log_sound : CB1_3_4I2S0_2_2E_2Log.Encloses (Real.log (CB1_3_4I2S0_2_2Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B1_3_4Little_sound (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2)) (2 : Fin 6)) (w := CB1_3_4I2S0_2_2E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_3_4I2S0_2_2E_2 : Ball := ⟨(8850415398129313697429749596289 / 100000000000000000000000000000000), (19207192059 / 50000000000000000000000000000000)⟩
lemma CB1_3_4I2S0_2_2E_2_sound : CB1_3_4I2S0_2_2E_2.Encloses (Foundation.entropyTerm (CB1_3_4I2S0_2_2Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_3_4Little_sound (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2)) (2 : Fin 6)) CB1_3_4I2S0_2_2E_2Log_sound) (by decide +kernel)
def CB1_3_4I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 46483, 31250⟩
def CB1_3_4I2S0_2_2E_3Log : Ball := ⟨(-59388036101788952339754245697507 / 25000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma CB1_3_4I2S0_2_2E_3Log_sound : CB1_3_4I2S0_2_2E_3Log.Encloses (Real.log (CB1_3_4I2S0_2_2Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B1_3_4Little_sound (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2)) (3 : Fin 6)) (w := CB1_3_4I2S0_2_2E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_3_4I2S0_2_2E_3 : Ball := ⟨(11042136328477823486435186411029 / 50000000000000000000000000000000), (9843158123 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2S0_2_2E_3_sound : CB1_3_4I2S0_2_2E_3.Encloses (Foundation.entropyTerm (CB1_3_4I2S0_2_2Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_3_4Little_sound (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2)) (3 : Fin 6)) CB1_3_4I2S0_2_2E_3Log_sound) (by decide +kernel)
def CB1_3_4I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(8850415398129313697429749596289 / 100000000000000000000000000000000), (19207192059 / 50000000000000000000000000000000)⟩
  | 3 => ⟨(11042136328477823486435186411029 / 50000000000000000000000000000000), (9843158123 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB1_3_4I2S0_2_2Terms_sound (a : Fin 6) :
    (CB1_3_4I2S0_2_2Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2S0_2_2Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2)) (1 : Fin 6)))
  · exact CB1_3_4I2S0_2_2E_2_sound
  · exact CB1_3_4I2S0_2_2E_3_sound
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2)) (5 : Fin 6)))
def CB1_3_4I2S0_2_2Entropy : Ball := ⟨(30934688055084960670300122418347 / 100000000000000000000000000000000), (48257542241 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2S0_2_2Entropy_sound : CB1_3_4I2S0_2_2Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2S0_2_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2S0_2_2Value CB1_3_4I2S0_2_2Terms CB1_3_4I2S0_2_2Terms_sound) (by decide +kernel)
def CB1_3_4I2S0_2_2Mass : Ball := ⟨1, 0⟩
lemma CB1_3_4I2S0_2_2Mass_sound : CB1_3_4I2S0_2_2Mass.Encloses (∑ a, CB1_3_4I2S0_2_2Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_3_4Little (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2)) CB1_3_4I2S0_2_2Value (B1_3_4Little_sound (shape 0 2 2) ((stageBPriority (shape 1 3 4)) 2))) (by decide +kernel)
def CB1_3_4I2S0_2_2MassTermLog : Ball := .exact 0
lemma CB1_3_4I2S0_2_2MassTermLog_sound : CB1_3_4I2S0_2_2MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I2S0_2_2Value a))) := by
  exact log_exact_one_ball (CB1_3_4I2S0_2_2Mass_sound)
def CB1_3_4I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_2_2MassTerm_sound : CB1_3_4I2S0_2_2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2S0_2_2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I2S0_2_2Mass_sound) CB1_3_4I2S0_2_2MassTermLog_sound) (by decide +kernel)
def CB1_3_4I2S0_2_2H : Ball := ⟨(30934688055084960670300122418347 / 100000000000000000000000000000000), (48257542241 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2S0_2_2H_sound : CB1_3_4I2S0_2_2H.Encloses (homogeneousEntropy CB1_3_4I2S0_2_2Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2S0_2_2Value CB1_3_4I2S0_2_2MassTerm_sound CB1_3_4I2S0_2_2Entropy_sound) (by decide +kernel)
def CB1_3_4I2S0_3_1Value (a : Fin 6) : ℝ := (littleLaw (shape 1 3 4) (shape 0 3 1) ((stageBPriority (shape 1 3 4)) 2) a : ℝ)
def CB1_3_4I2S0_3_1E_1Log : Ball := .exact 0
lemma CB1_3_4I2S0_3_1E_1Log_sound : CB1_3_4I2S0_3_1E_1Log.Encloses (Real.log (CB1_3_4I2S0_3_1Value (1 : Fin 6))) := by
  exact log_exact_one_ball ((B1_3_4Little_sound (shape 0 3 1) ((stageBPriority (shape 1 3 4)) 2)) (1 : Fin 6))
def CB1_3_4I2S0_3_1E_1 : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_3_1E_1_sound : CB1_3_4I2S0_3_1E_1.Encloses (Foundation.entropyTerm (CB1_3_4I2S0_3_1Value (1 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_3_4Little_sound (shape 0 3 1) ((stageBPriority (shape 1 3 4)) 2)) (1 : Fin 6)) CB1_3_4I2S0_3_1E_1Log_sound) (by decide +kernel)
def CB1_3_4I2S0_3_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB1_3_4I2S0_3_1Terms_sound (a : Fin 6) :
    (CB1_3_4I2S0_3_1Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2S0_3_1Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 3 1) ((stageBPriority (shape 1 3 4)) 2)) (0 : Fin 6)))
  · exact CB1_3_4I2S0_3_1E_1_sound
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 3 1) ((stageBPriority (shape 1 3 4)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 3 1) ((stageBPriority (shape 1 3 4)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 3 1) ((stageBPriority (shape 1 3 4)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 0 3 1) ((stageBPriority (shape 1 3 4)) 2)) (5 : Fin 6)))
def CB1_3_4I2S0_3_1Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_3_1Entropy_sound : CB1_3_4I2S0_3_1Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2S0_3_1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2S0_3_1Value CB1_3_4I2S0_3_1Terms CB1_3_4I2S0_3_1Terms_sound) (by decide +kernel)
def CB1_3_4I2S0_3_1Mass : Ball := ⟨1, 0⟩
lemma CB1_3_4I2S0_3_1Mass_sound : CB1_3_4I2S0_3_1Mass.Encloses (∑ a, CB1_3_4I2S0_3_1Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_3_4Little (shape 0 3 1) ((stageBPriority (shape 1 3 4)) 2)) CB1_3_4I2S0_3_1Value (B1_3_4Little_sound (shape 0 3 1) ((stageBPriority (shape 1 3 4)) 2))) (by decide +kernel)
def CB1_3_4I2S0_3_1MassTermLog : Ball := .exact 0
lemma CB1_3_4I2S0_3_1MassTermLog_sound : CB1_3_4I2S0_3_1MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I2S0_3_1Value a))) := by
  exact log_exact_one_ball (CB1_3_4I2S0_3_1Mass_sound)
def CB1_3_4I2S0_3_1MassTerm : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_3_1MassTerm_sound : CB1_3_4I2S0_3_1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2S0_3_1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I2S0_3_1Mass_sound) CB1_3_4I2S0_3_1MassTermLog_sound) (by decide +kernel)
def CB1_3_4I2S0_3_1H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S0_3_1H_sound : CB1_3_4I2S0_3_1H.Encloses (homogeneousEntropy CB1_3_4I2S0_3_1Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2S0_3_1Value CB1_3_4I2S0_3_1MassTerm_sound CB1_3_4I2S0_3_1Entropy_sound) (by decide +kernel)
def CB1_3_4I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 3 4) (shape 1 0 3) ((stageBPriority (shape 1 3 4)) 2) a : ℝ)
def CB1_3_4I2S1_0_3E_4Log : Ball := .exact 0
lemma CB1_3_4I2S1_0_3E_4Log_sound : CB1_3_4I2S1_0_3E_4Log.Encloses (Real.log (CB1_3_4I2S1_0_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B1_3_4Little_sound (shape 1 0 3) ((stageBPriority (shape 1 3 4)) 2)) (4 : Fin 6))
def CB1_3_4I2S1_0_3E_4 : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S1_0_3E_4_sound : CB1_3_4I2S1_0_3E_4.Encloses (Foundation.entropyTerm (CB1_3_4I2S1_0_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_3_4Little_sound (shape 1 0 3) ((stageBPriority (shape 1 3 4)) 2)) (4 : Fin 6)) CB1_3_4I2S1_0_3E_4Log_sound) (by decide +kernel)
def CB1_3_4I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB1_3_4I2S1_0_3Terms_sound (a : Fin 6) :
    (CB1_3_4I2S1_0_3Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I2S1_0_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 1 0 3) ((stageBPriority (shape 1 3 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 1 0 3) ((stageBPriority (shape 1 3 4)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 1 0 3) ((stageBPriority (shape 1 3 4)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 1 0 3) ((stageBPriority (shape 1 3 4)) 2)) (3 : Fin 6)))
  · exact CB1_3_4I2S1_0_3E_4_sound
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 1 0 3) ((stageBPriority (shape 1 3 4)) 2)) (5 : Fin 6)))
def CB1_3_4I2S1_0_3Entropy : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S1_0_3Entropy_sound : CB1_3_4I2S1_0_3Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I2S1_0_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I2S1_0_3Value CB1_3_4I2S1_0_3Terms CB1_3_4I2S1_0_3Terms_sound) (by decide +kernel)
def CB1_3_4I2S1_0_3Mass : Ball := ⟨1, 0⟩
lemma CB1_3_4I2S1_0_3Mass_sound : CB1_3_4I2S1_0_3Mass.Encloses (∑ a, CB1_3_4I2S1_0_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_3_4Little (shape 1 0 3) ((stageBPriority (shape 1 3 4)) 2)) CB1_3_4I2S1_0_3Value (B1_3_4Little_sound (shape 1 0 3) ((stageBPriority (shape 1 3 4)) 2))) (by decide +kernel)
def CB1_3_4I2S1_0_3MassTermLog : Ball := .exact 0
lemma CB1_3_4I2S1_0_3MassTermLog_sound : CB1_3_4I2S1_0_3MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I2S1_0_3Value a))) := by
  exact log_exact_one_ball (CB1_3_4I2S1_0_3Mass_sound)
def CB1_3_4I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S1_0_3MassTerm_sound : CB1_3_4I2S1_0_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I2S1_0_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I2S1_0_3Mass_sound) CB1_3_4I2S1_0_3MassTermLog_sound) (by decide +kernel)
def CB1_3_4I2S1_0_3H : Ball := ⟨0, 0⟩
lemma CB1_3_4I2S1_0_3H_sound : CB1_3_4I2S1_0_3H.Encloses (homogeneousEntropy CB1_3_4I2S1_0_3Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I2S1_0_3Value CB1_3_4I2S1_0_3MassTerm_sound CB1_3_4I2S1_0_3Entropy_sound) (by decide +kernel)
def CB1_3_4I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => CB1_3_4I2S0_0_4H
  | 0, 1, 3 => CB1_3_4I2S0_1_3H
  | 0, 2, 2 => CB1_3_4I2S0_2_2H
  | 0, 3, 1 => CB1_3_4I2S0_3_1H
  | 1, 0, 3 => CB1_3_4I2S1_0_3H
  | _, _, _ => (.exact 0)
lemma CB1_3_4I2Singles_sound (u : Shape) (hu : u ∈ below (shape 1 3 4))
    (hd : designated (stageBPriority (shape 1 3 4)) 2 u) :
    (CB1_3_4I2Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) u)) := by
  rw [B1_3_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CB1_3_4I2S0_0_4H_sound
  · exact CB1_3_4I2S0_1_3H_sound
  · exact CB1_3_4I2S0_2_2H_sound
  · exact CB1_3_4I2S0_3_1H_sound
  · exact CB1_3_4I2S1_0_3H_sound
  · exact (show ¬ designated (stageBPriority (shape 1 3 4)) 2 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 3 4)) 2 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 3 4)) 2 (shape 1 3 0) by decide +kernel) hd |>.elim
def CB1_3_4I2Singleton : Ball := ⟨(2641885964250374911539500817683 / 20000000000000000000000000000000), (20606466649 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2Singleton_sound : CB1_3_4I2Singleton.Encloses
    (singletonEntropy (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2
    CB1_3_4I2Singles (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ)) (fun u _ => B1_3_4Law_sound u) CB1_3_4I2Singles_sound) (by decide +kernel)
def CB1_3_4I2Group : Ball := ⟨(13606408060568169914547016902947 / 100000000000000000000000000000000), (90241723401 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2Group_sound : CB1_3_4I2Group.Encloses
    (groupedEntropy (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 2 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB1_3_4I2Singleton_sound
    (finSumBall_sound 17 CB1_3_4I2ResidualEntropies _ CB1_3_4I2ResidualEntropies_sound)) (by decide +kernel)

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
def CB1_3_4I2H : Ball := ⟨(2849768145656699904331921241729 / 5000000000000000000000000000000), (281352715573 / 100000000000000000000000000000000)⟩
lemma CB1_3_4I2_sound : CB1_3_4I2H.Encloses (stageBCapacity (shape 1 3 4) 2) := by
  have hb := contains_sound (Ball.add_sound CB1_3_4I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB1_3_4I2Group_sound)))
    (show contains (.add CB1_3_4I2PairH (.neg (.mul (.exact 2) CB1_3_4I2Group))) CB1_3_4I2H = true by decide +kernel)
  simp only [stageBCapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false]
  change CB1_3_4I2H.Encloses (homogeneousEntropy CB1_3_4I2PairValue - _)
  simpa only [sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
