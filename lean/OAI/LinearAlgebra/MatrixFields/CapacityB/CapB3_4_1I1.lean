import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal3_4_1

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_4_1I1PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 3 4 1)) (shape 3 4 1) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) a
def CB3_4_1I1PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) a
lemma CB3_4_1I1PairRaw_sound (a : PairSlot) :
    (CB3_4_1I1PairRaw a).Encloses (CB3_4_1I1PairValue a) := by
  exact pairLawBall_sound_on (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) (fun u _ a => B3_4_1Little_sound (complement (shape 3 4 1) u) ((stageBPriority (shape 3 4 1)) 1) a) a
def CB3_4_1I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(82952079780722940626225466023 / 6250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(1147279995329005976604244689539 / 20000000000000000000000000000000), (2248420661 / 100000000000000000000000000000000)⟩ ⟨(-17288294614820796241404340152637 / 4000000000000000000000000000000), (42351647479 / 25000000000000000000000000000000)⟩ ⟨-7, 82952079780722940626225466023, 48828125000000000000000000000⟩,
   .log ⟨(44353533976166490223624096589007 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩ ⟨(18029219162022483790732983590417 / 50000000000000000000000000000000), (28176678493 / 100000000000000000000000000000000)⟩ ⟨(-16259555932305679112321862864337 / 20000000000000000000000000000000), (31763735547 / 50000000000000000000000000000000)⟩ ⟨-2, 44353533976166490223624096589007, 25000000000000000000000000000000⟩,
   .log ⟨(34553861978735541810850367637 / 800000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(212053568871460902457636479641 / 1562500000000000000000000000000), (219511947 / 4000000000000000000000000000000)⟩ ⟨(-78552310107190677134533302510819 / 25000000000000000000000000000000), (1985233471 / 1562500000000000000000000000000)⟩ ⟨-5, 34553861978735541810850367637, 25000000000000000000000000000⟩]
lemma CB3_4_1I1PairCertificates_valid :
    CB3_4_1I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 4 => 1
  | 1, 2 => 2
  | 1, 3 => 3
  | 2, 1 => 2
  | 3, 1 => 3
  | 4, 0 => 1
  | _, _ => 0
def CB3_4_1I1PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1PairCertificates (CB3_4_1I1PairCertificateIndex a)).input
lemma CB3_4_1I1PairP_check : ∀ a : PairSlot, contains (CB3_4_1I1PairRaw a) (CB3_4_1I1PairP a) = true := by
  decide +kernel
lemma CB3_4_1I1PairP_sound (a : PairSlot) :
    (CB3_4_1I1PairP a).Encloses (CB3_4_1I1PairValue a) :=
  contains_sound (CB3_4_1I1PairRaw_sound a) (CB3_4_1I1PairP_check a)
def CB3_4_1I1PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1PairCertificates (CB3_4_1I1PairCertificateIndex a)).output
lemma CB3_4_1I1PairTerms_sound (a : PairSlot) :
    (CB3_4_1I1PairTerms a).Encloses (Foundation.entropyTerm (CB3_4_1I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1PairCertificates_valid
    (CB3_4_1I1PairCertificateIndex a) (CB3_4_1I1PairP_sound a)
def CB3_4_1I1PairEntropy : Ball := ⟨(55366266708463495221775925325553 / 50000000000000000000000000000000), (35912897829 / 50000000000000000000000000000000)⟩
lemma CB3_4_1I1PairEntropy_sound : CB3_4_1I1PairEntropy.Encloses (Foundation.finiteEntropy CB3_4_1I1PairValue) := by
  exact contains_sound (entropyPair_enclosed CB3_4_1I1PairValue CB3_4_1I1PairTerms CB3_4_1I1PairTerms_sound) (by decide +kernel)
def CB3_4_1I1PairMass : Ball := ⟨1, (7 / 12500000000000000000000000000000)⟩
lemma CB3_4_1I1PairMass_sound : CB3_4_1I1PairMass.Encloses (∑ a, CB3_4_1I1PairValue a) := by
  exact contains_sound (pairSumBall_sound CB3_4_1I1PairP CB3_4_1I1PairValue CB3_4_1I1PairP_sound) (by decide +kernel)
def CB3_4_1I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_4_1I1PairMassTermLog : Ball := ⟨0, (10587911869 / 50000000000000000000000000000000)⟩
lemma CB3_4_1I1PairMassTermLog_sound : CB3_4_1I1PairMassTermLog.Encloses (Real.log ((∑ a, CB3_4_1I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_4_1I1PairMass_sound) (w := CB3_4_1I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_4_1I1PairMassTerm : Ball := ⟨0, (21175823739 / 100000000000000000000000000000000)⟩
lemma CB3_4_1I1PairMassTerm_sound : CB3_4_1I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB3_4_1I1PairMass_sound) CB3_4_1I1PairMassTermLog_sound) (by decide +kernel)
def CB3_4_1I1PairH : Ball := ⟨(55366266708463495221775925325553 / 50000000000000000000000000000000), (93001619397 / 100000000000000000000000000000000)⟩
lemma CB3_4_1I1PairH_sound : CB3_4_1I1PairH.Encloses (homogeneousEntropy CB3_4_1I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1PairValue CB3_4_1I1PairMassTerm_sound CB3_4_1I1PairEntropy_sound) (by decide +kernel)

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
def CB3_4_1I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 0 a
def CB3_4_1I1R0Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 0 a
lemma CB3_4_1I1R0Raw_sound (a : Fin 6) :
    (CB3_4_1I1R0Raw a).Encloses (CB3_4_1I1R0Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 0 a
def CB3_4_1I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(82952079780722940626225466023 / 6250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(1147279995329005976604244689539 / 20000000000000000000000000000000), (2248420661 / 100000000000000000000000000000000)⟩ ⟨(-17288294614820796241404340152637 / 4000000000000000000000000000000), (42351647479 / 25000000000000000000000000000000)⟩ ⟨-7, 82952079780722940626225466023, 48828125000000000000000000000⟩]
lemma CB3_4_1I1R0Certificates_valid :
    CB3_4_1I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB3_4_1I1R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R0Certificates (CB3_4_1I1R0CertificateIndex a)).input
lemma CB3_4_1I1R0P_check : ∀ a : Fin 6, contains (CB3_4_1I1R0Raw a) (CB3_4_1I1R0P a) = true := by
  decide +kernel
lemma CB3_4_1I1R0P_sound (a : Fin 6) :
    (CB3_4_1I1R0P a).Encloses (CB3_4_1I1R0Value a) :=
  contains_sound (CB3_4_1I1R0Raw_sound a) (CB3_4_1I1R0P_check a)
def CB3_4_1I1R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R0Certificates (CB3_4_1I1R0CertificateIndex a)).output
lemma CB3_4_1I1R0Terms_sound (a : Fin 6) :
    (CB3_4_1I1R0Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R0Certificates_valid
    (CB3_4_1I1R0CertificateIndex a) (CB3_4_1I1R0P_sound a)
def CB3_4_1I1R0Entropy : Ball := ⟨(1147279995329005976604244689539 / 20000000000000000000000000000000), (2248420661 / 100000000000000000000000000000000)⟩
lemma CB3_4_1I1R0Entropy_sound : CB3_4_1I1R0Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R0Value CB3_4_1I1R0Terms CB3_4_1I1R0Terms_sound) (by decide +kernel)
def CB3_4_1I1R0Mass : Ball := ⟨(82952079780722940626225466023 / 6250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CB3_4_1I1R0Mass_sound : CB3_4_1I1R0Mass.Encloses (∑ a, CB3_4_1I1R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R0P CB3_4_1I1R0Value CB3_4_1I1R0P_sound) (by decide +kernel)
def CB3_4_1I1R0MassTermLogWitness : LogWitness := ⟨-7, 82952079780722940626225466023, 48828125000000000000000000000⟩
def CB3_4_1I1R0MassTermLog : Ball := ⟨(-17288294614820796241404340152637 / 4000000000000000000000000000000), (42351647479 / 25000000000000000000000000000000)⟩
lemma CB3_4_1I1R0MassTermLog_sound : CB3_4_1I1R0MassTermLog.Encloses (Real.log ((∑ a, CB3_4_1I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_4_1I1R0Mass_sound) (w := CB3_4_1I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_4_1I1R0MassTerm : Ball := ⟨(1147279995329005976604244689539 / 20000000000000000000000000000000), (2248420661 / 100000000000000000000000000000000)⟩
lemma CB3_4_1I1R0MassTerm_sound : CB3_4_1I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_4_1I1R0Mass_sound) CB3_4_1I1R0MassTermLog_sound) (by decide +kernel)
def CB3_4_1I1R0H : Ball := ⟨0, (2248420661 / 50000000000000000000000000000000)⟩
lemma CB3_4_1I1R0H_sound : CB3_4_1I1R0H.Encloses (homogeneousEntropy CB3_4_1I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R0Value CB3_4_1I1R0MassTerm_sound CB3_4_1I1R0Entropy_sound) (by decide +kernel)
def CB3_4_1I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 1 a
def CB3_4_1I1R1Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 1 a
lemma CB3_4_1I1R1Raw_sound (a : Fin 6) :
    (CB3_4_1I1R1Raw a).Encloses (CB3_4_1I1R1Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 1 a
def CB3_4_1I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3042047920219277059373774533977 / 6250000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩ ⟨(35046850851307688181754010183329 / 100000000000000000000000000000000), (15460288913 / 50000000000000000000000000000000)⟩ ⟨(-9000631464612332402682222967793 / 12500000000000000000000000000000), (15881867773 / 25000000000000000000000000000000)⟩ ⟨-2, 3042047920219277059373774533977, 1562500000000000000000000000000⟩]
lemma CB3_4_1I1R1Certificates_valid :
    CB3_4_1I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB3_4_1I1R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R1Certificates (CB3_4_1I1R1CertificateIndex a)).input
lemma CB3_4_1I1R1P_check : ∀ a : Fin 6, contains (CB3_4_1I1R1Raw a) (CB3_4_1I1R1P a) = true := by
  decide +kernel
lemma CB3_4_1I1R1P_sound (a : Fin 6) :
    (CB3_4_1I1R1P a).Encloses (CB3_4_1I1R1Value a) :=
  contains_sound (CB3_4_1I1R1Raw_sound a) (CB3_4_1I1R1P_check a)
def CB3_4_1I1R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R1Certificates (CB3_4_1I1R1CertificateIndex a)).output
lemma CB3_4_1I1R1Terms_sound (a : Fin 6) :
    (CB3_4_1I1R1Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R1Certificates_valid
    (CB3_4_1I1R1CertificateIndex a) (CB3_4_1I1R1P_sound a)
def CB3_4_1I1R1Entropy : Ball := ⟨(35046850851307688181754010183329 / 100000000000000000000000000000000), (15460288913 / 50000000000000000000000000000000)⟩
lemma CB3_4_1I1R1Entropy_sound : CB3_4_1I1R1Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R1Value CB3_4_1I1R1Terms CB3_4_1I1R1Terms_sound) (by decide +kernel)
def CB3_4_1I1R1Mass : Ball := ⟨(3042047920219277059373774533977 / 6250000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
lemma CB3_4_1I1R1Mass_sound : CB3_4_1I1R1Mass.Encloses (∑ a, CB3_4_1I1R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R1P CB3_4_1I1R1Value CB3_4_1I1R1P_sound) (by decide +kernel)
def CB3_4_1I1R1MassTermLogWitness : LogWitness := ⟨-2, 3042047920219277059373774533977, 1562500000000000000000000000000⟩
def CB3_4_1I1R1MassTermLog : Ball := ⟨(-9000631464612332402682222967793 / 12500000000000000000000000000000), (15881867773 / 25000000000000000000000000000000)⟩
lemma CB3_4_1I1R1MassTermLog_sound : CB3_4_1I1R1MassTermLog.Encloses (Real.log ((∑ a, CB3_4_1I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_4_1I1R1Mass_sound) (w := CB3_4_1I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_4_1I1R1MassTerm : Ball := ⟨(35046850851307688181754010183329 / 100000000000000000000000000000000), (15460288913 / 50000000000000000000000000000000)⟩
lemma CB3_4_1I1R1MassTerm_sound : CB3_4_1I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_4_1I1R1Mass_sound) CB3_4_1I1R1MassTermLog_sound) (by decide +kernel)
def CB3_4_1I1R1H : Ball := ⟨0, (15460288913 / 25000000000000000000000000000000)⟩
lemma CB3_4_1I1R1H_sound : CB3_4_1I1R1H.Encloses (homogeneousEntropy CB3_4_1I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R1Value CB3_4_1I1R1MassTerm_sound CB3_4_1I1R1Entropy_sound) (by decide +kernel)
def CB3_4_1I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 2 a
def CB3_4_1I1R2Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 2 a
lemma CB3_4_1I1R2Raw_sound (a : Fin 6) :
    (CB3_4_1I1R2Raw a).Encloses (CB3_4_1I1R2Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 2 a
def CB3_4_1I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(44353533976166490223624096589007 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩ ⟨(18029219162022483790732983590417 / 50000000000000000000000000000000), (28176678493 / 100000000000000000000000000000000)⟩ ⟨(-16259555932305679112321862864337 / 20000000000000000000000000000000), (31763735547 / 50000000000000000000000000000000)⟩ ⟨-2, 44353533976166490223624096589007, 25000000000000000000000000000000⟩,
   .log ⟨(34553861978735541810850367637 / 800000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(212053568871460902457636479641 / 1562500000000000000000000000000), (219511947 / 4000000000000000000000000000000)⟩ ⟨(-78552310107190677134533302510819 / 25000000000000000000000000000000), (1985233471 / 1562500000000000000000000000000)⟩ ⟨-5, 34553861978735541810850367637, 25000000000000000000000000000⟩]
lemma CB3_4_1I1R2Certificates_valid :
    CB3_4_1I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB3_4_1I1R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R2Certificates (CB3_4_1I1R2CertificateIndex a)).input
lemma CB3_4_1I1R2P_check : ∀ a : Fin 6, contains (CB3_4_1I1R2Raw a) (CB3_4_1I1R2P a) = true := by
  decide +kernel
lemma CB3_4_1I1R2P_sound (a : Fin 6) :
    (CB3_4_1I1R2P a).Encloses (CB3_4_1I1R2Value a) :=
  contains_sound (CB3_4_1I1R2Raw_sound a) (CB3_4_1I1R2P_check a)
def CB3_4_1I1R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R2Certificates (CB3_4_1I1R2CertificateIndex a)).output
lemma CB3_4_1I1R2Terms_sound (a : Fin 6) :
    (CB3_4_1I1R2Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R2Certificates_valid
    (CB3_4_1I1R2CertificateIndex a) (CB3_4_1I1R2P_sound a)
def CB3_4_1I1R2Entropy : Ball := ⟨(24814933365909232669377350938929 / 50000000000000000000000000000000), (2104029823 / 6250000000000000000000000000000)⟩
lemma CB3_4_1I1R2Entropy_sound : CB3_4_1I1R2Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R2Value CB3_4_1I1R2Terms CB3_4_1I1R2Terms_sound) (by decide +kernel)
def CB3_4_1I1R2Mass : Ball := ⟨(3042047920219277059373774533977 / 6250000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
lemma CB3_4_1I1R2Mass_sound : CB3_4_1I1R2Mass.Encloses (∑ a, CB3_4_1I1R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R2P CB3_4_1I1R2Value CB3_4_1I1R2P_sound) (by decide +kernel)
def CB3_4_1I1R2MassTermLogWitness : LogWitness := ⟨-2, 3042047920219277059373774533977, 1562500000000000000000000000000⟩
def CB3_4_1I1R2MassTermLog : Ball := ⟨(-9000631464612332402682222967793 / 12500000000000000000000000000000), (31763735547 / 50000000000000000000000000000000)⟩
lemma CB3_4_1I1R2MassTermLog_sound : CB3_4_1I1R2MassTermLog.Encloses (Real.log ((∑ a, CB3_4_1I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_4_1I1R2Mass_sound) (w := CB3_4_1I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_4_1I1R2MassTerm : Ball := ⟨(35046850851307688181754010183329 / 100000000000000000000000000000000), (30920577827 / 100000000000000000000000000000000)⟩
lemma CB3_4_1I1R2MassTerm_sound : CB3_4_1I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_4_1I1R2Mass_sound) CB3_4_1I1R2MassTermLog_sound) (by decide +kernel)
def CB3_4_1I1R2H : Ball := ⟨(14583015880510777157000691694529 / 100000000000000000000000000000000), (12917010999 / 20000000000000000000000000000000)⟩
lemma CB3_4_1I1R2H_sound : CB3_4_1I1R2H.Encloses (homogeneousEntropy CB3_4_1I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R2Value CB3_4_1I1R2MassTerm_sound CB3_4_1I1R2Entropy_sound) (by decide +kernel)
def CB3_4_1I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 3 a
def CB3_4_1I1R3Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 3 a
lemma CB3_4_1I1R3Raw_sound (a : Fin 6) :
    (CB3_4_1I1R3Raw a).Encloses (CB3_4_1I1R3Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 3 a
def CB3_4_1I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(80868831238226048857523902691 / 6250000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(5625246599010449899116012778669 / 100000000000000000000000000000000), (2191954091 / 100000000000000000000000000000000)⟩ ⟨(-434750826807998994834781262470351 / 100000000000000000000000000000000), (3388131797 / 2000000000000000000000000000000)⟩ ⟨-7, 80868831238226048857523902691, 48828125000000000000000000000⟩]
lemma CB3_4_1I1R3Certificates_valid :
    CB3_4_1I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 4 => 1
  | _ => 0
def CB3_4_1I1R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R3Certificates (CB3_4_1I1R3CertificateIndex a)).input
lemma CB3_4_1I1R3P_check : ∀ a : Fin 6, contains (CB3_4_1I1R3Raw a) (CB3_4_1I1R3P a) = true := by
  decide +kernel
lemma CB3_4_1I1R3P_sound (a : Fin 6) :
    (CB3_4_1I1R3P a).Encloses (CB3_4_1I1R3Value a) :=
  contains_sound (CB3_4_1I1R3Raw_sound a) (CB3_4_1I1R3P_check a)
def CB3_4_1I1R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R3Certificates (CB3_4_1I1R3CertificateIndex a)).output
lemma CB3_4_1I1R3Terms_sound (a : Fin 6) :
    (CB3_4_1I1R3Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R3Certificates_valid
    (CB3_4_1I1R3CertificateIndex a) (CB3_4_1I1R3P_sound a)
def CB3_4_1I1R3Entropy : Ball := ⟨(5625246599010449899116012778669 / 100000000000000000000000000000000), (2191954091 / 100000000000000000000000000000000)⟩
lemma CB3_4_1I1R3Entropy_sound : CB3_4_1I1R3Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R3Value CB3_4_1I1R3Terms CB3_4_1I1R3Terms_sound) (by decide +kernel)
def CB3_4_1I1R3Mass : Ball := ⟨(80868831238226048857523902691 / 6250000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma CB3_4_1I1R3Mass_sound : CB3_4_1I1R3Mass.Encloses (∑ a, CB3_4_1I1R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R3P CB3_4_1I1R3Value CB3_4_1I1R3P_sound) (by decide +kernel)
def CB3_4_1I1R3MassTermLogWitness : LogWitness := ⟨-7, 80868831238226048857523902691, 48828125000000000000000000000⟩
def CB3_4_1I1R3MassTermLog : Ball := ⟨(-434750826807998994834781262470351 / 100000000000000000000000000000000), (3388131797 / 2000000000000000000000000000000)⟩
lemma CB3_4_1I1R3MassTermLog_sound : CB3_4_1I1R3MassTermLog.Encloses (Real.log ((∑ a, CB3_4_1I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_4_1I1R3Mass_sound) (w := CB3_4_1I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_4_1I1R3MassTerm : Ball := ⟨(5625246599010449899116012778669 / 100000000000000000000000000000000), (2191954091 / 100000000000000000000000000000000)⟩
lemma CB3_4_1I1R3MassTerm_sound : CB3_4_1I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_4_1I1R3Mass_sound) CB3_4_1I1R3MassTermLog_sound) (by decide +kernel)
def CB3_4_1I1R3H : Ball := ⟨0, (2191954091 / 50000000000000000000000000000000)⟩
lemma CB3_4_1I1R3H_sound : CB3_4_1I1R3H.Encloses (homogeneousEntropy CB3_4_1I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R3Value CB3_4_1I1R3MassTerm_sound CB3_4_1I1R3Entropy_sound) (by decide +kernel)
def CB3_4_1I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 4 a
def CB3_4_1I1R4Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 4 a
lemma CB3_4_1I1R4Raw_sound (a : Fin 6) :
    (CB3_4_1I1R4Raw a).Encloses (CB3_4_1I1R4Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 4 a
def CB3_4_1I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R4Certificates_valid :
    CB3_4_1I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R4Certificates (CB3_4_1I1R4CertificateIndex a)).input
lemma CB3_4_1I1R4P_check : ∀ a : Fin 6, contains (CB3_4_1I1R4Raw a) (CB3_4_1I1R4P a) = true := by
  decide +kernel
lemma CB3_4_1I1R4P_sound (a : Fin 6) :
    (CB3_4_1I1R4P a).Encloses (CB3_4_1I1R4Value a) :=
  contains_sound (CB3_4_1I1R4Raw_sound a) (CB3_4_1I1R4P_check a)
def CB3_4_1I1R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R4Certificates (CB3_4_1I1R4CertificateIndex a)).output
lemma CB3_4_1I1R4Terms_sound (a : Fin 6) :
    (CB3_4_1I1R4Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R4Certificates_valid
    (CB3_4_1I1R4CertificateIndex a) (CB3_4_1I1R4P_sound a)
def CB3_4_1I1R4Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R4Entropy_sound : CB3_4_1I1R4Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R4Value CB3_4_1I1R4Terms CB3_4_1I1R4Terms_sound) (by decide +kernel)
def CB3_4_1I1R4Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R4Mass_sound : CB3_4_1I1R4Mass.Encloses (∑ a, CB3_4_1I1R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R4P CB3_4_1I1R4Value CB3_4_1I1R4P_sound) (by decide +kernel)
def CB3_4_1I1R4MassTerm : Ball := .exact 0
lemma CB3_4_1I1R4MassTerm_sound : CB3_4_1I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R4Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R4Mass_sound)
def CB3_4_1I1R4H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R4H_sound : CB3_4_1I1R4H.Encloses (homogeneousEntropy CB3_4_1I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R4Value CB3_4_1I1R4MassTerm_sound CB3_4_1I1R4Entropy_sound) (by decide +kernel)
def CB3_4_1I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 5 a
def CB3_4_1I1R5Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 5 a
lemma CB3_4_1I1R5Raw_sound (a : Fin 6) :
    (CB3_4_1I1R5Raw a).Encloses (CB3_4_1I1R5Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 5 a
def CB3_4_1I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R5Certificates_valid :
    CB3_4_1I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R5Certificates (CB3_4_1I1R5CertificateIndex a)).input
lemma CB3_4_1I1R5P_check : ∀ a : Fin 6, contains (CB3_4_1I1R5Raw a) (CB3_4_1I1R5P a) = true := by
  decide +kernel
lemma CB3_4_1I1R5P_sound (a : Fin 6) :
    (CB3_4_1I1R5P a).Encloses (CB3_4_1I1R5Value a) :=
  contains_sound (CB3_4_1I1R5Raw_sound a) (CB3_4_1I1R5P_check a)
def CB3_4_1I1R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R5Certificates (CB3_4_1I1R5CertificateIndex a)).output
lemma CB3_4_1I1R5Terms_sound (a : Fin 6) :
    (CB3_4_1I1R5Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R5Certificates_valid
    (CB3_4_1I1R5CertificateIndex a) (CB3_4_1I1R5P_sound a)
def CB3_4_1I1R5Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R5Entropy_sound : CB3_4_1I1R5Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R5Value CB3_4_1I1R5Terms CB3_4_1I1R5Terms_sound) (by decide +kernel)
def CB3_4_1I1R5Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R5Mass_sound : CB3_4_1I1R5Mass.Encloses (∑ a, CB3_4_1I1R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R5P CB3_4_1I1R5Value CB3_4_1I1R5P_sound) (by decide +kernel)
def CB3_4_1I1R5MassTerm : Ball := .exact 0
lemma CB3_4_1I1R5MassTerm_sound : CB3_4_1I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R5Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R5Mass_sound)
def CB3_4_1I1R5H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R5H_sound : CB3_4_1I1R5H.Encloses (homogeneousEntropy CB3_4_1I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R5Value CB3_4_1I1R5MassTerm_sound CB3_4_1I1R5Entropy_sound) (by decide +kernel)
def CB3_4_1I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 6 a
def CB3_4_1I1R6Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 6 a
lemma CB3_4_1I1R6Raw_sound (a : Fin 6) :
    (CB3_4_1I1R6Raw a).Encloses (CB3_4_1I1R6Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 6 a
def CB3_4_1I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R6Certificates_valid :
    CB3_4_1I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R6Certificates (CB3_4_1I1R6CertificateIndex a)).input
lemma CB3_4_1I1R6P_check : ∀ a : Fin 6, contains (CB3_4_1I1R6Raw a) (CB3_4_1I1R6P a) = true := by
  decide +kernel
lemma CB3_4_1I1R6P_sound (a : Fin 6) :
    (CB3_4_1I1R6P a).Encloses (CB3_4_1I1R6Value a) :=
  contains_sound (CB3_4_1I1R6Raw_sound a) (CB3_4_1I1R6P_check a)
def CB3_4_1I1R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R6Certificates (CB3_4_1I1R6CertificateIndex a)).output
lemma CB3_4_1I1R6Terms_sound (a : Fin 6) :
    (CB3_4_1I1R6Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R6Certificates_valid
    (CB3_4_1I1R6CertificateIndex a) (CB3_4_1I1R6P_sound a)
def CB3_4_1I1R6Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R6Entropy_sound : CB3_4_1I1R6Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R6Value CB3_4_1I1R6Terms CB3_4_1I1R6Terms_sound) (by decide +kernel)
def CB3_4_1I1R6Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R6Mass_sound : CB3_4_1I1R6Mass.Encloses (∑ a, CB3_4_1I1R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R6P CB3_4_1I1R6Value CB3_4_1I1R6P_sound) (by decide +kernel)
def CB3_4_1I1R6MassTerm : Ball := .exact 0
lemma CB3_4_1I1R6MassTerm_sound : CB3_4_1I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R6Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R6Mass_sound)
def CB3_4_1I1R6H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R6H_sound : CB3_4_1I1R6H.Encloses (homogeneousEntropy CB3_4_1I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R6Value CB3_4_1I1R6MassTerm_sound CB3_4_1I1R6Entropy_sound) (by decide +kernel)
def CB3_4_1I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 7 a
def CB3_4_1I1R7Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 7 a
lemma CB3_4_1I1R7Raw_sound (a : Fin 6) :
    (CB3_4_1I1R7Raw a).Encloses (CB3_4_1I1R7Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 7 a
def CB3_4_1I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R7Certificates_valid :
    CB3_4_1I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R7Certificates (CB3_4_1I1R7CertificateIndex a)).input
lemma CB3_4_1I1R7P_check : ∀ a : Fin 6, contains (CB3_4_1I1R7Raw a) (CB3_4_1I1R7P a) = true := by
  decide +kernel
lemma CB3_4_1I1R7P_sound (a : Fin 6) :
    (CB3_4_1I1R7P a).Encloses (CB3_4_1I1R7Value a) :=
  contains_sound (CB3_4_1I1R7Raw_sound a) (CB3_4_1I1R7P_check a)
def CB3_4_1I1R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R7Certificates (CB3_4_1I1R7CertificateIndex a)).output
lemma CB3_4_1I1R7Terms_sound (a : Fin 6) :
    (CB3_4_1I1R7Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R7Certificates_valid
    (CB3_4_1I1R7CertificateIndex a) (CB3_4_1I1R7P_sound a)
def CB3_4_1I1R7Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R7Entropy_sound : CB3_4_1I1R7Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R7Value CB3_4_1I1R7Terms CB3_4_1I1R7Terms_sound) (by decide +kernel)
def CB3_4_1I1R7Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R7Mass_sound : CB3_4_1I1R7Mass.Encloses (∑ a, CB3_4_1I1R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R7P CB3_4_1I1R7Value CB3_4_1I1R7P_sound) (by decide +kernel)
def CB3_4_1I1R7MassTerm : Ball := .exact 0
lemma CB3_4_1I1R7MassTerm_sound : CB3_4_1I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R7Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R7Mass_sound)
def CB3_4_1I1R7H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R7H_sound : CB3_4_1I1R7H.Encloses (homogeneousEntropy CB3_4_1I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R7Value CB3_4_1I1R7MassTerm_sound CB3_4_1I1R7Entropy_sound) (by decide +kernel)
def CB3_4_1I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 8 a
def CB3_4_1I1R8Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 8 a
lemma CB3_4_1I1R8Raw_sound (a : Fin 6) :
    (CB3_4_1I1R8Raw a).Encloses (CB3_4_1I1R8Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 8 a
def CB3_4_1I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R8Certificates_valid :
    CB3_4_1I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R8Certificates (CB3_4_1I1R8CertificateIndex a)).input
lemma CB3_4_1I1R8P_check : ∀ a : Fin 6, contains (CB3_4_1I1R8Raw a) (CB3_4_1I1R8P a) = true := by
  decide +kernel
lemma CB3_4_1I1R8P_sound (a : Fin 6) :
    (CB3_4_1I1R8P a).Encloses (CB3_4_1I1R8Value a) :=
  contains_sound (CB3_4_1I1R8Raw_sound a) (CB3_4_1I1R8P_check a)
def CB3_4_1I1R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R8Certificates (CB3_4_1I1R8CertificateIndex a)).output
lemma CB3_4_1I1R8Terms_sound (a : Fin 6) :
    (CB3_4_1I1R8Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R8Certificates_valid
    (CB3_4_1I1R8CertificateIndex a) (CB3_4_1I1R8P_sound a)
def CB3_4_1I1R8Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R8Entropy_sound : CB3_4_1I1R8Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R8Value CB3_4_1I1R8Terms CB3_4_1I1R8Terms_sound) (by decide +kernel)
def CB3_4_1I1R8Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R8Mass_sound : CB3_4_1I1R8Mass.Encloses (∑ a, CB3_4_1I1R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R8P CB3_4_1I1R8Value CB3_4_1I1R8P_sound) (by decide +kernel)
def CB3_4_1I1R8MassTerm : Ball := .exact 0
lemma CB3_4_1I1R8MassTerm_sound : CB3_4_1I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R8Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R8Mass_sound)
def CB3_4_1I1R8H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R8H_sound : CB3_4_1I1R8H.Encloses (homogeneousEntropy CB3_4_1I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R8Value CB3_4_1I1R8MassTerm_sound CB3_4_1I1R8Entropy_sound) (by decide +kernel)
def CB3_4_1I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 9 a
def CB3_4_1I1R9Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 9 a
lemma CB3_4_1I1R9Raw_sound (a : Fin 6) :
    (CB3_4_1I1R9Raw a).Encloses (CB3_4_1I1R9Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 9 a
def CB3_4_1I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R9Certificates_valid :
    CB3_4_1I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R9Certificates (CB3_4_1I1R9CertificateIndex a)).input
lemma CB3_4_1I1R9P_check : ∀ a : Fin 6, contains (CB3_4_1I1R9Raw a) (CB3_4_1I1R9P a) = true := by
  decide +kernel
lemma CB3_4_1I1R9P_sound (a : Fin 6) :
    (CB3_4_1I1R9P a).Encloses (CB3_4_1I1R9Value a) :=
  contains_sound (CB3_4_1I1R9Raw_sound a) (CB3_4_1I1R9P_check a)
def CB3_4_1I1R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R9Certificates (CB3_4_1I1R9CertificateIndex a)).output
lemma CB3_4_1I1R9Terms_sound (a : Fin 6) :
    (CB3_4_1I1R9Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R9Certificates_valid
    (CB3_4_1I1R9CertificateIndex a) (CB3_4_1I1R9P_sound a)
def CB3_4_1I1R9Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R9Entropy_sound : CB3_4_1I1R9Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R9Value CB3_4_1I1R9Terms CB3_4_1I1R9Terms_sound) (by decide +kernel)
def CB3_4_1I1R9Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R9Mass_sound : CB3_4_1I1R9Mass.Encloses (∑ a, CB3_4_1I1R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R9P CB3_4_1I1R9Value CB3_4_1I1R9P_sound) (by decide +kernel)
def CB3_4_1I1R9MassTerm : Ball := .exact 0
lemma CB3_4_1I1R9MassTerm_sound : CB3_4_1I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R9Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R9Mass_sound)
def CB3_4_1I1R9H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R9H_sound : CB3_4_1I1R9H.Encloses (homogeneousEntropy CB3_4_1I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R9Value CB3_4_1I1R9MassTerm_sound CB3_4_1I1R9Entropy_sound) (by decide +kernel)
def CB3_4_1I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 10 a
def CB3_4_1I1R10Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 10 a
lemma CB3_4_1I1R10Raw_sound (a : Fin 6) :
    (CB3_4_1I1R10Raw a).Encloses (CB3_4_1I1R10Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 10 a
def CB3_4_1I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R10Certificates_valid :
    CB3_4_1I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R10Certificates (CB3_4_1I1R10CertificateIndex a)).input
lemma CB3_4_1I1R10P_check : ∀ a : Fin 6, contains (CB3_4_1I1R10Raw a) (CB3_4_1I1R10P a) = true := by
  decide +kernel
lemma CB3_4_1I1R10P_sound (a : Fin 6) :
    (CB3_4_1I1R10P a).Encloses (CB3_4_1I1R10Value a) :=
  contains_sound (CB3_4_1I1R10Raw_sound a) (CB3_4_1I1R10P_check a)
def CB3_4_1I1R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R10Certificates (CB3_4_1I1R10CertificateIndex a)).output
lemma CB3_4_1I1R10Terms_sound (a : Fin 6) :
    (CB3_4_1I1R10Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R10Certificates_valid
    (CB3_4_1I1R10CertificateIndex a) (CB3_4_1I1R10P_sound a)
def CB3_4_1I1R10Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R10Entropy_sound : CB3_4_1I1R10Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R10Value CB3_4_1I1R10Terms CB3_4_1I1R10Terms_sound) (by decide +kernel)
def CB3_4_1I1R10Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R10Mass_sound : CB3_4_1I1R10Mass.Encloses (∑ a, CB3_4_1I1R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R10P CB3_4_1I1R10Value CB3_4_1I1R10P_sound) (by decide +kernel)
def CB3_4_1I1R10MassTerm : Ball := .exact 0
lemma CB3_4_1I1R10MassTerm_sound : CB3_4_1I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R10Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R10Mass_sound)
def CB3_4_1I1R10H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R10H_sound : CB3_4_1I1R10H.Encloses (homogeneousEntropy CB3_4_1I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R10Value CB3_4_1I1R10MassTerm_sound CB3_4_1I1R10Entropy_sound) (by decide +kernel)
def CB3_4_1I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 11 a
def CB3_4_1I1R11Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 11 a
lemma CB3_4_1I1R11Raw_sound (a : Fin 6) :
    (CB3_4_1I1R11Raw a).Encloses (CB3_4_1I1R11Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 11 a
def CB3_4_1I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R11Certificates_valid :
    CB3_4_1I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R11Certificates (CB3_4_1I1R11CertificateIndex a)).input
lemma CB3_4_1I1R11P_check : ∀ a : Fin 6, contains (CB3_4_1I1R11Raw a) (CB3_4_1I1R11P a) = true := by
  decide +kernel
lemma CB3_4_1I1R11P_sound (a : Fin 6) :
    (CB3_4_1I1R11P a).Encloses (CB3_4_1I1R11Value a) :=
  contains_sound (CB3_4_1I1R11Raw_sound a) (CB3_4_1I1R11P_check a)
def CB3_4_1I1R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R11Certificates (CB3_4_1I1R11CertificateIndex a)).output
lemma CB3_4_1I1R11Terms_sound (a : Fin 6) :
    (CB3_4_1I1R11Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R11Certificates_valid
    (CB3_4_1I1R11CertificateIndex a) (CB3_4_1I1R11P_sound a)
def CB3_4_1I1R11Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R11Entropy_sound : CB3_4_1I1R11Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R11Value CB3_4_1I1R11Terms CB3_4_1I1R11Terms_sound) (by decide +kernel)
def CB3_4_1I1R11Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R11Mass_sound : CB3_4_1I1R11Mass.Encloses (∑ a, CB3_4_1I1R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R11P CB3_4_1I1R11Value CB3_4_1I1R11P_sound) (by decide +kernel)
def CB3_4_1I1R11MassTerm : Ball := .exact 0
lemma CB3_4_1I1R11MassTerm_sound : CB3_4_1I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R11Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R11Mass_sound)
def CB3_4_1I1R11H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R11H_sound : CB3_4_1I1R11H.Encloses (homogeneousEntropy CB3_4_1I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R11Value CB3_4_1I1R11MassTerm_sound CB3_4_1I1R11Entropy_sound) (by decide +kernel)
def CB3_4_1I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 12 a
def CB3_4_1I1R12Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 12 a
lemma CB3_4_1I1R12Raw_sound (a : Fin 6) :
    (CB3_4_1I1R12Raw a).Encloses (CB3_4_1I1R12Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 12 a
def CB3_4_1I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R12Certificates_valid :
    CB3_4_1I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R12Certificates (CB3_4_1I1R12CertificateIndex a)).input
lemma CB3_4_1I1R12P_check : ∀ a : Fin 6, contains (CB3_4_1I1R12Raw a) (CB3_4_1I1R12P a) = true := by
  decide +kernel
lemma CB3_4_1I1R12P_sound (a : Fin 6) :
    (CB3_4_1I1R12P a).Encloses (CB3_4_1I1R12Value a) :=
  contains_sound (CB3_4_1I1R12Raw_sound a) (CB3_4_1I1R12P_check a)
def CB3_4_1I1R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R12Certificates (CB3_4_1I1R12CertificateIndex a)).output
lemma CB3_4_1I1R12Terms_sound (a : Fin 6) :
    (CB3_4_1I1R12Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R12Certificates_valid
    (CB3_4_1I1R12CertificateIndex a) (CB3_4_1I1R12P_sound a)
def CB3_4_1I1R12Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R12Entropy_sound : CB3_4_1I1R12Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R12Value CB3_4_1I1R12Terms CB3_4_1I1R12Terms_sound) (by decide +kernel)
def CB3_4_1I1R12Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R12Mass_sound : CB3_4_1I1R12Mass.Encloses (∑ a, CB3_4_1I1R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R12P CB3_4_1I1R12Value CB3_4_1I1R12P_sound) (by decide +kernel)
def CB3_4_1I1R12MassTerm : Ball := .exact 0
lemma CB3_4_1I1R12MassTerm_sound : CB3_4_1I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R12Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R12Mass_sound)
def CB3_4_1I1R12H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R12H_sound : CB3_4_1I1R12H.Encloses (homogeneousEntropy CB3_4_1I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R12Value CB3_4_1I1R12MassTerm_sound CB3_4_1I1R12Entropy_sound) (by decide +kernel)
def CB3_4_1I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 13 a
def CB3_4_1I1R13Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 13 a
lemma CB3_4_1I1R13Raw_sound (a : Fin 6) :
    (CB3_4_1I1R13Raw a).Encloses (CB3_4_1I1R13Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 13 a
def CB3_4_1I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R13Certificates_valid :
    CB3_4_1I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R13Certificates (CB3_4_1I1R13CertificateIndex a)).input
lemma CB3_4_1I1R13P_check : ∀ a : Fin 6, contains (CB3_4_1I1R13Raw a) (CB3_4_1I1R13P a) = true := by
  decide +kernel
lemma CB3_4_1I1R13P_sound (a : Fin 6) :
    (CB3_4_1I1R13P a).Encloses (CB3_4_1I1R13Value a) :=
  contains_sound (CB3_4_1I1R13Raw_sound a) (CB3_4_1I1R13P_check a)
def CB3_4_1I1R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R13Certificates (CB3_4_1I1R13CertificateIndex a)).output
lemma CB3_4_1I1R13Terms_sound (a : Fin 6) :
    (CB3_4_1I1R13Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R13Certificates_valid
    (CB3_4_1I1R13CertificateIndex a) (CB3_4_1I1R13P_sound a)
def CB3_4_1I1R13Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R13Entropy_sound : CB3_4_1I1R13Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R13Value CB3_4_1I1R13Terms CB3_4_1I1R13Terms_sound) (by decide +kernel)
def CB3_4_1I1R13Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R13Mass_sound : CB3_4_1I1R13Mass.Encloses (∑ a, CB3_4_1I1R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R13P CB3_4_1I1R13Value CB3_4_1I1R13P_sound) (by decide +kernel)
def CB3_4_1I1R13MassTerm : Ball := .exact 0
lemma CB3_4_1I1R13MassTerm_sound : CB3_4_1I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R13Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R13Mass_sound)
def CB3_4_1I1R13H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R13H_sound : CB3_4_1I1R13H.Encloses (homogeneousEntropy CB3_4_1I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R13Value CB3_4_1I1R13MassTerm_sound CB3_4_1I1R13Entropy_sound) (by decide +kernel)
def CB3_4_1I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 14 a
def CB3_4_1I1R14Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 14 a
lemma CB3_4_1I1R14Raw_sound (a : Fin 6) :
    (CB3_4_1I1R14Raw a).Encloses (CB3_4_1I1R14Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 14 a
def CB3_4_1I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R14Certificates_valid :
    CB3_4_1I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R14Certificates (CB3_4_1I1R14CertificateIndex a)).input
lemma CB3_4_1I1R14P_check : ∀ a : Fin 6, contains (CB3_4_1I1R14Raw a) (CB3_4_1I1R14P a) = true := by
  decide +kernel
lemma CB3_4_1I1R14P_sound (a : Fin 6) :
    (CB3_4_1I1R14P a).Encloses (CB3_4_1I1R14Value a) :=
  contains_sound (CB3_4_1I1R14Raw_sound a) (CB3_4_1I1R14P_check a)
def CB3_4_1I1R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R14Certificates (CB3_4_1I1R14CertificateIndex a)).output
lemma CB3_4_1I1R14Terms_sound (a : Fin 6) :
    (CB3_4_1I1R14Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R14Certificates_valid
    (CB3_4_1I1R14CertificateIndex a) (CB3_4_1I1R14P_sound a)
def CB3_4_1I1R14Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R14Entropy_sound : CB3_4_1I1R14Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R14Value CB3_4_1I1R14Terms CB3_4_1I1R14Terms_sound) (by decide +kernel)
def CB3_4_1I1R14Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R14Mass_sound : CB3_4_1I1R14Mass.Encloses (∑ a, CB3_4_1I1R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R14P CB3_4_1I1R14Value CB3_4_1I1R14P_sound) (by decide +kernel)
def CB3_4_1I1R14MassTerm : Ball := .exact 0
lemma CB3_4_1I1R14MassTerm_sound : CB3_4_1I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R14Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R14Mass_sound)
def CB3_4_1I1R14H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R14H_sound : CB3_4_1I1R14H.Encloses (homogeneousEntropy CB3_4_1I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R14Value CB3_4_1I1R14MassTerm_sound CB3_4_1I1R14Entropy_sound) (by decide +kernel)
def CB3_4_1I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 15 a
def CB3_4_1I1R15Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 15 a
lemma CB3_4_1I1R15Raw_sound (a : Fin 6) :
    (CB3_4_1I1R15Raw a).Encloses (CB3_4_1I1R15Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 15 a
def CB3_4_1I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R15Certificates_valid :
    CB3_4_1I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R15Certificates (CB3_4_1I1R15CertificateIndex a)).input
lemma CB3_4_1I1R15P_check : ∀ a : Fin 6, contains (CB3_4_1I1R15Raw a) (CB3_4_1I1R15P a) = true := by
  decide +kernel
lemma CB3_4_1I1R15P_sound (a : Fin 6) :
    (CB3_4_1I1R15P a).Encloses (CB3_4_1I1R15Value a) :=
  contains_sound (CB3_4_1I1R15Raw_sound a) (CB3_4_1I1R15P_check a)
def CB3_4_1I1R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R15Certificates (CB3_4_1I1R15CertificateIndex a)).output
lemma CB3_4_1I1R15Terms_sound (a : Fin 6) :
    (CB3_4_1I1R15Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R15Certificates_valid
    (CB3_4_1I1R15CertificateIndex a) (CB3_4_1I1R15P_sound a)
def CB3_4_1I1R15Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R15Entropy_sound : CB3_4_1I1R15Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R15Value CB3_4_1I1R15Terms CB3_4_1I1R15Terms_sound) (by decide +kernel)
def CB3_4_1I1R15Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R15Mass_sound : CB3_4_1I1R15Mass.Encloses (∑ a, CB3_4_1I1R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R15P CB3_4_1I1R15Value CB3_4_1I1R15P_sound) (by decide +kernel)
def CB3_4_1I1R15MassTerm : Ball := .exact 0
lemma CB3_4_1I1R15MassTerm_sound : CB3_4_1I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R15Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R15Mass_sound)
def CB3_4_1I1R15H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R15H_sound : CB3_4_1I1R15H.Encloses (homogeneousEntropy CB3_4_1I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R15Value CB3_4_1I1R15MassTerm_sound CB3_4_1I1R15Entropy_sound) (by decide +kernel)
def CB3_4_1I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) 16 a
def CB3_4_1I1R16Raw (a : Fin 6) : Ball := residualBall (below (shape 3 4 1)) B3_4_1Law (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) 16 a
lemma CB3_4_1I1R16Raw_sound (a : Fin 6) :
    (CB3_4_1I1R16Raw a).Encloses (CB3_4_1I1R16Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 1)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 1) a) 16 a
def CB3_4_1I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_4_1I1R16Certificates_valid :
    CB3_4_1I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_4_1I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R16Certificates (CB3_4_1I1R16CertificateIndex a)).input
lemma CB3_4_1I1R16P_check : ∀ a : Fin 6, contains (CB3_4_1I1R16Raw a) (CB3_4_1I1R16P a) = true := by
  decide +kernel
lemma CB3_4_1I1R16P_sound (a : Fin 6) :
    (CB3_4_1I1R16P a).Encloses (CB3_4_1I1R16Value a) :=
  contains_sound (CB3_4_1I1R16Raw_sound a) (CB3_4_1I1R16P_check a)
def CB3_4_1I1R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_4_1I1R16Certificates (CB3_4_1I1R16CertificateIndex a)).output
lemma CB3_4_1I1R16Terms_sound (a : Fin 6) :
    (CB3_4_1I1R16Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R16Certificates_valid
    (CB3_4_1I1R16CertificateIndex a) (CB3_4_1I1R16P_sound a)
def CB3_4_1I1R16Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R16Entropy_sound : CB3_4_1I1R16Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R16Value CB3_4_1I1R16Terms CB3_4_1I1R16Terms_sound) (by decide +kernel)
def CB3_4_1I1R16Mass : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R16Mass_sound : CB3_4_1I1R16Mass.Encloses (∑ a, CB3_4_1I1R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R16P CB3_4_1I1R16Value CB3_4_1I1R16P_sound) (by decide +kernel)
def CB3_4_1I1R16MassTerm : Ball := .exact 0
lemma CB3_4_1I1R16MassTerm_sound : CB3_4_1I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R16Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R16Mass_sound)
def CB3_4_1I1R16H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1R16H_sound : CB3_4_1I1R16H.Encloses (homogeneousEntropy CB3_4_1I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R16Value CB3_4_1I1R16MassTerm_sound CB3_4_1I1R16Entropy_sound) (by decide +kernel)
def CB3_4_1I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB3_4_1I1R0H
  | 1 => CB3_4_1I1R1H
  | 2 => CB3_4_1I1R2H
  | 3 => CB3_4_1I1R3H
  | 4 => CB3_4_1I1R4H
  | 5 => CB3_4_1I1R5H
  | 6 => CB3_4_1I1R6H
  | 7 => CB3_4_1I1R7H
  | 8 => CB3_4_1I1R8H
  | 9 => CB3_4_1I1R9H
  | 10 => CB3_4_1I1R10H
  | 11 => CB3_4_1I1R11H
  | 12 => CB3_4_1I1R12H
  | 13 => CB3_4_1I1R13H
  | 14 => CB3_4_1I1R14H
  | 15 => CB3_4_1I1R15H
  | 16 => CB3_4_1I1R16H
  | _ => (.exact 0)
lemma CB3_4_1I1ResidualEntropies_sound (k : Fin 17) :
    (CB3_4_1I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CB3_4_1I1R0H_sound
  · exact CB3_4_1I1R1H_sound
  · exact CB3_4_1I1R2H_sound
  · exact CB3_4_1I1R3H_sound
  · exact CB3_4_1I1R4H_sound
  · exact CB3_4_1I1R5H_sound
  · exact CB3_4_1I1R6H_sound
  · exact CB3_4_1I1R7H_sound
  · exact CB3_4_1I1R8H_sound
  · exact CB3_4_1I1R9H_sound
  · exact CB3_4_1I1R10H_sound
  · exact CB3_4_1I1R11H_sound
  · exact CB3_4_1I1R12H_sound
  · exact CB3_4_1I1R13H_sound
  · exact CB3_4_1I1R14H_sound
  · exact CB3_4_1I1R15H_sound
  · exact CB3_4_1I1R16H_sound
def CB3_4_1I1S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 3 4 1) (shape 3 0 1) ((stageBPriority (shape 3 4 1)) 1) a : ℝ)
def CB3_4_1I1S3_0_1E_4Log : Ball := .exact 0
lemma CB3_4_1I1S3_0_1E_4Log_sound : CB3_4_1I1S3_0_1E_4Log.Encloses (Real.log (CB3_4_1I1S3_0_1Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B3_4_1Little_sound (shape 3 0 1) ((stageBPriority (shape 3 4 1)) 1)) (4 : Fin 6))
def CB3_4_1I1S3_0_1E_4 : Ball := ⟨0, 0⟩
lemma CB3_4_1I1S3_0_1E_4_sound : CB3_4_1I1S3_0_1E_4.Encloses (Foundation.entropyTerm (CB3_4_1I1S3_0_1Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_4_1Little_sound (shape 3 0 1) ((stageBPriority (shape 3 4 1)) 1)) (4 : Fin 6)) CB3_4_1I1S3_0_1E_4Log_sound) (by decide +kernel)
def CB3_4_1I1S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB3_4_1I1S3_0_1Terms_sound (a : Fin 6) :
    (CB3_4_1I1S3_0_1Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1S3_0_1Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_4_1Little_sound (shape 3 0 1) ((stageBPriority (shape 3 4 1)) 1)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_4_1Little_sound (shape 3 0 1) ((stageBPriority (shape 3 4 1)) 1)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_4_1Little_sound (shape 3 0 1) ((stageBPriority (shape 3 4 1)) 1)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_4_1Little_sound (shape 3 0 1) ((stageBPriority (shape 3 4 1)) 1)) (3 : Fin 6)))
  · exact CB3_4_1I1S3_0_1E_4_sound
  · exact (entropyTerm_zero_ball ((B3_4_1Little_sound (shape 3 0 1) ((stageBPriority (shape 3 4 1)) 1)) (5 : Fin 6)))
def CB3_4_1I1S3_0_1Entropy : Ball := ⟨0, 0⟩
lemma CB3_4_1I1S3_0_1Entropy_sound : CB3_4_1I1S3_0_1Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1S3_0_1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1S3_0_1Value CB3_4_1I1S3_0_1Terms CB3_4_1I1S3_0_1Terms_sound) (by decide +kernel)
def CB3_4_1I1S3_0_1Mass : Ball := ⟨1, 0⟩
lemma CB3_4_1I1S3_0_1Mass_sound : CB3_4_1I1S3_0_1Mass.Encloses (∑ a, CB3_4_1I1S3_0_1Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_4_1Little (shape 3 0 1) ((stageBPriority (shape 3 4 1)) 1)) CB3_4_1I1S3_0_1Value (B3_4_1Little_sound (shape 3 0 1) ((stageBPriority (shape 3 4 1)) 1))) (by decide +kernel)
def CB3_4_1I1S3_0_1MassTermLog : Ball := .exact 0
lemma CB3_4_1I1S3_0_1MassTermLog_sound : CB3_4_1I1S3_0_1MassTermLog.Encloses (Real.log ((∑ a, CB3_4_1I1S3_0_1Value a))) := by
  exact log_exact_one_ball (CB3_4_1I1S3_0_1Mass_sound)
def CB3_4_1I1S3_0_1MassTerm : Ball := ⟨0, 0⟩
lemma CB3_4_1I1S3_0_1MassTerm_sound : CB3_4_1I1S3_0_1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1S3_0_1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_4_1I1S3_0_1Mass_sound) CB3_4_1I1S3_0_1MassTermLog_sound) (by decide +kernel)
def CB3_4_1I1S3_0_1H : Ball := ⟨0, 0⟩
lemma CB3_4_1I1S3_0_1H_sound : CB3_4_1I1S3_0_1H.Encloses (homogeneousEntropy CB3_4_1I1S3_0_1Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1S3_0_1Value CB3_4_1I1S3_0_1MassTerm_sound CB3_4_1I1S3_0_1Entropy_sound) (by decide +kernel)
def CB3_4_1I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 3, 0, 1 => CB3_4_1I1S3_0_1H
  | _, _, _ => (.exact 0)
lemma CB3_4_1I1Singles_sound (u : Shape) (hu : u ∈ below (shape 3 4 1))
    (hd : designated (stageBPriority (shape 3 4 1)) 1 u) :
    (CB3_4_1I1Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) u)) := by
  rw [B3_4_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (stageBPriority (shape 3 4 1)) 1 (shape 0 3 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 4 1)) 1 (shape 0 4 0) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 4 1)) 1 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 4 1)) 1 (shape 1 3 0) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 4 1)) 1 (shape 2 1 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 4 1)) 1 (shape 2 2 0) by decide +kernel) hd |>.elim
  · exact CB3_4_1I1S3_0_1H_sound
  · exact (show ¬ designated (stageBPriority (shape 3 4 1)) 1 (shape 3 1 0) by decide +kernel) hd |>.elim
def CB3_4_1I1Singleton : Ball := ⟨0, 0⟩
lemma CB3_4_1I1Singleton_sound : CB3_4_1I1Singleton.Encloses
    (singletonEntropy (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1
    CB3_4_1I1Singles (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) (fun u _ => B3_4_1Law_sound u) CB3_4_1I1Singles_sound) (by decide +kernel)
def CB3_4_1I1Group : Ball := ⟨(14583015880510777157000691694529 / 100000000000000000000000000000000), (135306960151 / 100000000000000000000000000000000)⟩
lemma CB3_4_1I1Group_sound : CB3_4_1I1Group.Encloses
    (groupedEntropy (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB3_4_1I1Singleton_sound
    (finSumBall_sound 17 CB3_4_1I1ResidualEntropies _ CB3_4_1I1ResidualEntropies_sound)) (by decide +kernel)

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
def CB3_4_1I1H : Ball := ⟨(2548953176747044879048452101939 / 3125000000000000000000000000000), (363615539699 / 100000000000000000000000000000000)⟩
lemma CB3_4_1I1_sound : CB3_4_1I1H.Encloses (stageBCapacity (shape 3 4 1) 1) := by
  have hb := contains_sound (Ball.add_sound CB3_4_1I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB3_4_1I1Group_sound)))
    (show contains (.add CB3_4_1I1PairH (.neg (.mul (.exact 2) CB3_4_1I1Group))) CB3_4_1I1H = true by decide +kernel)
  simp only [stageBCapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false]
  change CB3_4_1I1H.Encloses (homogeneousEntropy CB3_4_1I1PairValue - _)
  simpa only [sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
