import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA3_3_10I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_3_10I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA3_3_10I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA3_3_10I2R0Raw_sound (a : PairSlot) :
    (CA3_3_10I2R0Raw a).Encloses (CA3_3_10I2R0Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA3_3_10I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R0Certificates_valid :
    CA3_3_10I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R0Certificates (CA3_3_10I2R0CertificateIndex a)).input
lemma CA3_3_10I2R0P_check : ∀ a : PairSlot, contains (CA3_3_10I2R0Raw a) (CA3_3_10I2R0P a) = true := by
  decide +kernel
lemma CA3_3_10I2R0P_sound (a : PairSlot) :
    (CA3_3_10I2R0P a).Encloses (CA3_3_10I2R0Value a) :=
  contains_sound (CA3_3_10I2R0Raw_sound a) (CA3_3_10I2R0P_check a)
def CA3_3_10I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R0Certificates (CA3_3_10I2R0CertificateIndex a)).output
lemma CA3_3_10I2R0Terms_sound (a : PairSlot) :
    (CA3_3_10I2R0Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R0Certificates_valid
    (CA3_3_10I2R0CertificateIndex a) (CA3_3_10I2R0P_sound a)
def CA3_3_10I2R0Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R0Entropy_sound : CA3_3_10I2R0Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R0Value CA3_3_10I2R0Terms CA3_3_10I2R0Terms_sound) (by decide +kernel)
def CA3_3_10I2R0Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R0Mass_sound : CA3_3_10I2R0Mass.Encloses (∑ a, CA3_3_10I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R0P CA3_3_10I2R0Value CA3_3_10I2R0P_sound) (by decide +kernel)
def CA3_3_10I2R0MassTerm : Ball := .exact 0
lemma CA3_3_10I2R0MassTerm_sound : CA3_3_10I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R0Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R0Mass_sound)
def CA3_3_10I2R0H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R0H_sound : CA3_3_10I2R0H.Encloses (homogeneousEntropy CA3_3_10I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R0Value CA3_3_10I2R0MassTerm_sound CA3_3_10I2R0Entropy_sound) (by decide +kernel)
def CA3_3_10I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA3_3_10I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA3_3_10I2R1Raw_sound (a : PairSlot) :
    (CA3_3_10I2R1Raw a).Encloses (CA3_3_10I2R1Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA3_3_10I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R1Certificates_valid :
    CA3_3_10I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R1Certificates (CA3_3_10I2R1CertificateIndex a)).input
lemma CA3_3_10I2R1P_check : ∀ a : PairSlot, contains (CA3_3_10I2R1Raw a) (CA3_3_10I2R1P a) = true := by
  decide +kernel
lemma CA3_3_10I2R1P_sound (a : PairSlot) :
    (CA3_3_10I2R1P a).Encloses (CA3_3_10I2R1Value a) :=
  contains_sound (CA3_3_10I2R1Raw_sound a) (CA3_3_10I2R1P_check a)
def CA3_3_10I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R1Certificates (CA3_3_10I2R1CertificateIndex a)).output
lemma CA3_3_10I2R1Terms_sound (a : PairSlot) :
    (CA3_3_10I2R1Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R1Certificates_valid
    (CA3_3_10I2R1CertificateIndex a) (CA3_3_10I2R1P_sound a)
def CA3_3_10I2R1Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R1Entropy_sound : CA3_3_10I2R1Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R1Value CA3_3_10I2R1Terms CA3_3_10I2R1Terms_sound) (by decide +kernel)
def CA3_3_10I2R1Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R1Mass_sound : CA3_3_10I2R1Mass.Encloses (∑ a, CA3_3_10I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R1P CA3_3_10I2R1Value CA3_3_10I2R1P_sound) (by decide +kernel)
def CA3_3_10I2R1MassTerm : Ball := .exact 0
lemma CA3_3_10I2R1MassTerm_sound : CA3_3_10I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R1Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R1Mass_sound)
def CA3_3_10I2R1H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R1H_sound : CA3_3_10I2R1H.Encloses (homogeneousEntropy CA3_3_10I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R1Value CA3_3_10I2R1MassTerm_sound CA3_3_10I2R1Entropy_sound) (by decide +kernel)
def CA3_3_10I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA3_3_10I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA3_3_10I2R2Raw_sound (a : PairSlot) :
    (CA3_3_10I2R2Raw a).Encloses (CA3_3_10I2R2Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA3_3_10I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(204410733265658976046433123 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2536206180674890189163805149 / 50000000000000000000000000000000), (1644869 / 100000000000000000000000000000000)⟩ ⟨(-1240740219535709226456799424257063 / 100000000000000000000000000000000), (201170447291 / 50000000000000000000000000000000)⟩ ⟨-18, 204410733265658976046433123, 190734863281250000000000000⟩,
   .log ⟨(5044486655977323258061011 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(311065051000710648768908957 / 100000000000000000000000000000000), (51283 / 50000000000000000000000000000000)⟩ ⟨(-770804524361569139790725698710741 / 50000000000000000000000000000000), (508224724297 / 100000000000000000000000000000000)⟩ ⟨-23, 5044486655977323258061011, 2980232238769531250000000⟩,
   .log ⟨(292437207758310337832007369 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(16278506733108100910470138241 / 100000000000000000000000000000000), (696669 / 12500000000000000000000000000000)⟩ ⟨(-1113299286222274925386142123835681 / 100000000000000000000000000000000), (95291223671 / 25000000000000000000000000000000)⟩ ⟨-17, 292437207758310337832007369, 152587890625000000000000000⟩]
lemma CA3_3_10I2R2Certificates_valid :
    CA3_3_10I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA3_3_10I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R2Certificates (CA3_3_10I2R2CertificateIndex a)).input
lemma CA3_3_10I2R2P_check : ∀ a : PairSlot, contains (CA3_3_10I2R2Raw a) (CA3_3_10I2R2P a) = true := by
  decide +kernel
lemma CA3_3_10I2R2P_sound (a : PairSlot) :
    (CA3_3_10I2R2P a).Encloses (CA3_3_10I2R2Value a) :=
  contains_sound (CA3_3_10I2R2Raw_sound a) (CA3_3_10I2R2P_check a)
def CA3_3_10I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R2Certificates (CA3_3_10I2R2CertificateIndex a)).output
lemma CA3_3_10I2R2Terms_sound (a : PairSlot) :
    (CA3_3_10I2R2Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R2Certificates_valid
    (CA3_3_10I2R2CertificateIndex a) (CA3_3_10I2R2P_sound a)
def CA3_3_10I2R2Entropy : Ball := ⟨(27045461557809082964663176751 / 100000000000000000000000000000000), (4534111 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I2R2Entropy_sound : CA3_3_10I2R2Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R2Value CA3_3_10I2R2Terms CA3_3_10I2R2Terms_sound) (by decide +kernel)
def CA3_3_10I2R2Mass : Ball := ⟨(92807394604080247176410297 / 4000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma CA3_3_10I2R2Mass_sound : CA3_3_10I2R2Mass.Encloses (∑ a, CA3_3_10I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R2P CA3_3_10I2R2Value CA3_3_10I2R2P_sound) (by decide +kernel)
def CA3_3_10I2R2MassTermLogWitness : LogWitness := ⟨-16, 92807394604080247176410297, 61035156250000000000000000⟩
def CA3_3_10I2R2MassTermLog : Ball := ⟨(-106712785992329267025334324179899 / 10000000000000000000000000000000), (359989218111 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I2R2MassTermLog_sound : CA3_3_10I2R2MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I2R2Mass_sound) (w := CA3_3_10I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_3_10I2R2MassTerm : Ball := ⟨(6189834774306793376050655379 / 25000000000000000000000000000000), (8352469 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I2R2MassTerm_sound : CA3_3_10I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I2R2Mass_sound) CA3_3_10I2R2MassTermLog_sound) (by decide +kernel)
def CA3_3_10I2R2H : Ball := ⟨(457224492116381892092111047 / 20000000000000000000000000000000), (17420691 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I2R2H_sound : CA3_3_10I2R2H.Encloses (homogeneousEntropy CA3_3_10I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R2Value CA3_3_10I2R2MassTerm_sound CA3_3_10I2R2Entropy_sound) (by decide +kernel)
def CA3_3_10I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA3_3_10I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA3_3_10I2R3Raw_sound (a : PairSlot) :
    (CA3_3_10I2R3Raw a).Encloses (CA3_3_10I2R3Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA3_3_10I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(4934993434450625004229415309 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(18207020560625530018934037979 / 20000000000000000000000000000000), (3918847 / 12500000000000000000000000000000)⟩ ⟨(-230585673548271625940616174386427 / 25000000000000000000000000000000), (2481541917 / 781250000000000000000000000000)⟩ ⟨-14, 4934993434450625004229415309, 3051757812500000000000000000⟩,
   .log ⟨(350467867214893328574126728907 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1981424914383373820028631039891 / 100000000000000000000000000000000), (742144597 / 100000000000000000000000000000000)⟩ ⟨(-565365643968849437797224337721463 / 100000000000000000000000000000000), (105879118843 / 50000000000000000000000000000000)⟩ ⟨-9, 350467867214893328574126728907, 195312500000000000000000000000⟩,
   .log ⟨(3077117550294247173663889277 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(135077679258998791932977281509 / 100000000000000000000000000000000), (1140309 / 2500000000000000000000000000000)⟩ ⟨(-109743678175442213022326652229331 / 12500000000000000000000000000000), (296461538061 / 100000000000000000000000000000000)⟩ ⟨-13, 3077117550294247173663889277, 2441406250000000000000000000⟩]
lemma CA3_3_10I2R3Certificates_valid :
    CA3_3_10I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA3_3_10I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R3Certificates (CA3_3_10I2R3CertificateIndex a)).input
lemma CA3_3_10I2R3P_check : ∀ a : PairSlot, contains (CA3_3_10I2R3Raw a) (CA3_3_10I2R3P a) = true := by
  decide +kernel
lemma CA3_3_10I2R3P_sound (a : PairSlot) :
    (CA3_3_10I2R3P a).Encloses (CA3_3_10I2R3Value a) :=
  contains_sound (CA3_3_10I2R3Raw_sound a) (CA3_3_10I2R3P_check a)
def CA3_3_10I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R3Certificates (CA3_3_10I2R3CertificateIndex a)).output
lemma CA3_3_10I2R3Terms_sound (a : PairSlot) :
    (CA3_3_10I2R3Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R3Certificates_valid
    (CA3_3_10I2R3CertificateIndex a) (CA3_3_10I2R3P_sound a)
def CA3_3_10I2R3Entropy : Ball := ⟨(441507539289100052411255702259 / 10000000000000000000000000000000), (819107733 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I2R3Entropy_sound : CA3_3_10I2R3Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R3Value CA3_3_10I2R3Terms CA3_3_10I2R3Terms_sound) (by decide +kernel)
def CA3_3_10I2R3Mass : Ball := ⟨(37572344183526581445090500591 / 5000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
lemma CA3_3_10I2R3Mass_sound : CA3_3_10I2R3Mass.Encloses (∑ a, CA3_3_10I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R3P CA3_3_10I2R3Value CA3_3_10I2R3P_sound) (by decide +kernel)
def CA3_3_10I2R3MassTermLogWitness : LogWitness := ⟨-8, 37572344183526581445090500591, 19531250000000000000000000000⟩
def CA3_3_10I2R3MassTermLog : Ball := ⟨(-4890924938686978144743451349959 / 1000000000000000000000000000000), (95291207239 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I2R3MassTermLog_sound : CA3_3_10I2R3MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I2R3Mass_sound) (w := CA3_3_10I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_3_10I2R3MassTerm : Ball := ⟨(459408787930351963191356758269 / 12500000000000000000000000000000), (44753927 / 3125000000000000000000000000000)⟩
lemma CA3_3_10I2R3MassTerm_sound : CA3_3_10I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I2R3Mass_sound) CA3_3_10I2R3MassTermLog_sound) (by decide +kernel)
def CA3_3_10I2R3H : Ball := ⟨(369902544724092409290851478219 / 50000000000000000000000000000000), (307034113 / 10000000000000000000000000000000)⟩
lemma CA3_3_10I2R3H_sound : CA3_3_10I2R3H.Encloses (homogeneousEntropy CA3_3_10I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R3Value CA3_3_10I2R3MassTerm_sound CA3_3_10I2R3Entropy_sound) (by decide +kernel)
def CA3_3_10I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA3_3_10I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA3_3_10I2R4Raw_sound (a : PairSlot) :
    (CA3_3_10I2R4Raw a).Encloses (CA3_3_10I2R4Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA3_3_10I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(292426610747876677393628467 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(23323661743187264287437728669 / 50000000000000000000000000000000), (1585249 / 10000000000000000000000000000000)⟩ ⟨(-996987828994826628952931568601249 / 100000000000000000000000000000000), (338813200301 / 100000000000000000000000000000000)⟩ ⟨-15, 292426610747876677393628467, 190734863281250000000000000⟩,
   .log ⟨(49855739965540601932205240819 / 3125000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(6601786889331058205106748938237 / 100000000000000000000000000000000), (2364849497 / 100000000000000000000000000000000)⟩ ⟨(-413805592764625468094839034928309 / 100000000000000000000000000000000), (148230766407 / 100000000000000000000000000000000)⟩ ⟨-6, 49855739965540601932205240819, 48828125000000000000000000000⟩,
   .log ⟨(1653108759278764065063434902573 / 10000000000000000000000000000000), (7 / 10000000000000000000000000000000)⟩ ⟨(29754758852921556780326831903431 / 100000000000000000000000000000000), (14002376043 / 100000000000000000000000000000000)⟩ ⟨(-179992748123258874859358077837239 / 100000000000000000000000000000000), (16940659031 / 20000000000000000000000000000000)⟩ ⟨-3, 1653108759278764065063434902573, 1250000000000000000000000000000⟩,
   .log ⟨(96435795935249516874992395783 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(3752977569731605056105428799339 / 100000000000000000000000000000000), (735158683 / 50000000000000000000000000000000)⟩ ⟨(-19458425853878418786976991792859 / 4000000000000000000000000000000), (38116482759 / 20000000000000000000000000000000)⟩ ⟨-8, 96435795935249516874992395783, 48828125000000000000000000000⟩,
   .log ⟨(18279812938541531845270453481 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(289332182787322242821107074539 / 100000000000000000000000000000000), (50321717 / 50000000000000000000000000000000)⟩ ⟨(-395699047577899915330143175246277 / 50000000000000000000000000000000), (137642855307 / 50000000000000000000000000000000)⟩ ⟨-12, 18279812938541531845270453481, 12207031250000000000000000000⟩]
lemma CA3_3_10I2R4Certificates_valid :
    CA3_3_10I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA3_3_10I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R4Certificates (CA3_3_10I2R4CertificateIndex a)).input
lemma CA3_3_10I2R4P_check : ∀ a : PairSlot, contains (CA3_3_10I2R4Raw a) (CA3_3_10I2R4P a) = true := by
  decide +kernel
lemma CA3_3_10I2R4P_sound (a : PairSlot) :
    (CA3_3_10I2R4P a).Encloses (CA3_3_10I2R4Value a) :=
  contains_sound (CA3_3_10I2R4Raw_sound a) (CA3_3_10I2R4P_check a)
def CA3_3_10I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R4Certificates (CA3_3_10I2R4CertificateIndex a)).output
lemma CA3_3_10I2R4Terms_sound (a : PairSlot) :
    (CA3_3_10I2R4Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R4Certificates_valid
    (CA3_3_10I2R4CertificateIndex a) (CA3_3_10I2R4P_sound a)
def CA3_3_10I2R4Entropy : Ball := ⟨(25423457300403477301361022683899 / 50000000000000000000000000000000), (21805058183 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I2R4Entropy_sound : CA3_3_10I2R4Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R4Value CA3_3_10I2R4Terms CA3_3_10I2R4Terms_sound) (by decide +kernel)
def CA3_3_10I2R4Mass : Ball := ⟨(1065537248148362328083124989429 / 5000000000000000000000000000000), (103 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I2R4Mass_sound : CA3_3_10I2R4Mass.Encloses (∑ a, CA3_3_10I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R4P CA3_3_10I2R4Value CA3_3_10I2R4P_sound) (by decide +kernel)
def CA3_3_10I2R4MassTermLogWitness : LogWitness := ⟨-3, 1065537248148362328083124989429, 625000000000000000000000000000⟩
def CA3_3_10I2R4MassTermLog : Ball := ⟨(-154595878211378320822588544937459 / 100000000000000000000000000000000), (16940659043 / 20000000000000000000000000000000)⟩
lemma CA3_3_10I2R4MassTermLog_sound : CA3_3_10I2R4MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I2R4Mass_sound) (w := CA3_3_10I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_3_10I2R4MassTerm : Ball := ⟨(2059095833055392783245717986463 / 6250000000000000000000000000000), (18050903379 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I2R4MassTerm_sound : CA3_3_10I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I2R4Mass_sound) CA3_3_10I2R4MassTermLog_sound) (by decide +kernel)
def CA3_3_10I2R4H : Ball := ⟨(1790138127192067007079055758439 / 10000000000000000000000000000000), (19927980781 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I2R4H_sound : CA3_3_10I2R4H.Encloses (homogeneousEntropy CA3_3_10I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R4Value CA3_3_10I2R4MassTerm_sound CA3_3_10I2R4Entropy_sound) (by decide +kernel)
def CA3_3_10I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA3_3_10I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA3_3_10I2R5Raw_sound (a : PairSlot) :
    (CA3_3_10I2R5Raw a).Encloses (CA3_3_10I2R5Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA3_3_10I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18742924709934919642771347073 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(295724439812178383035116466057 / 100000000000000000000000000000000), (25798299 / 25000000000000000000000000000000)⟩ ⟨(-394448097600565477541093905839049 / 50000000000000000000000000000000), (137642855273 / 50000000000000000000000000000000)⟩ ⟨-12, 18742924709934919642771347073, 12207031250000000000000000000⟩,
   .log ⟨(441486378135169595035023994947 / 2000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩ ⟨(8337223535112156143260300671753 / 25000000000000000000000000000000), (18697675523 / 100000000000000000000000000000000)⟩ ⟨(-37768882339375616603467954678619 / 25000000000000000000000000000000), (16940658989 / 20000000000000000000000000000000)⟩ ⟨-3, 441486378135169595035023994947, 250000000000000000000000000000⟩,
   .log ⟨(828412602588776180169548902123 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1985462334209944676635733051203 / 50000000000000000000000000000000), (1403385561 / 100000000000000000000000000000000)⟩ ⟨(-479341412239602952867242993422541 / 100000000000000000000000000000000), (84703294973 / 50000000000000000000000000000000)⟩ ⟨-7, 828412602588776180169548902123, 781250000000000000000000000000⟩]
lemma CA3_3_10I2R5Certificates_valid :
    CA3_3_10I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA3_3_10I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R5Certificates (CA3_3_10I2R5CertificateIndex a)).input
lemma CA3_3_10I2R5P_check : ∀ a : PairSlot, contains (CA3_3_10I2R5Raw a) (CA3_3_10I2R5P a) = true := by
  decide +kernel
lemma CA3_3_10I2R5P_sound (a : PairSlot) :
    (CA3_3_10I2R5P a).Encloses (CA3_3_10I2R5Value a) :=
  contains_sound (CA3_3_10I2R5Raw_sound a) (CA3_3_10I2R5P_check a)
def CA3_3_10I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R5Certificates (CA3_3_10I2R5CertificateIndex a)).output
lemma CA3_3_10I2R5Terms_sound (a : PairSlot) :
    (CA3_3_10I2R5Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R5Certificates_valid
    (CA3_3_10I2R5CertificateIndex a) (CA3_3_10I2R5P_sound a)
def CA3_3_10I2R5Entropy : Ball := ⟨(1504621729947227692373911410219 / 2000000000000000000000000000000), (505106357 / 1250000000000000000000000000000)⟩
lemma CA3_3_10I2R5Entropy_sound : CA3_3_10I2R5Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R5Value CA3_3_10I2R5Terms CA3_3_10I2R5Terms_sound) (by decide +kernel)
def CA3_3_10I2R5Mass : Ball := ⟨(22940217358767125771206291343619 / 50000000000000000000000000000000), (13 / 12500000000000000000000000000000)⟩
lemma CA3_3_10I2R5Mass_sound : CA3_3_10I2R5Mass.Encloses (∑ a, CA3_3_10I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R5P CA3_3_10I2R5Value CA3_3_10I2R5P_sound) (by decide +kernel)
def CA3_3_10I2R5MassTermLogWitness : LogWitness := ⟨-2, 22940217358767125771206291343619, 12500000000000000000000000000000⟩
def CA3_3_10I2R5MassTermLog : Ball := ⟨(-77913141867298139311620297031129 / 100000000000000000000000000000000), (2541098851 / 4000000000000000000000000000000)⟩
lemma CA3_3_10I2R5MassTermLog_sound : CA3_3_10I2R5MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I2R5Mass_sound) (w := CA3_3_10I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_3_10I2R5MassTerm : Ball := ⟨(17873444095402784870395903805863 / 50000000000000000000000000000000), (7286670017 / 25000000000000000000000000000000)⟩
lemma CA3_3_10I2R5MassTerm_sound : CA3_3_10I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I2R5Mass_sound) CA3_3_10I2R5MassTermLog_sound) (by decide +kernel)
def CA3_3_10I2R5H : Ball := ⟨(4935524788319476859737970362403 / 12500000000000000000000000000000), (17388797157 / 25000000000000000000000000000000)⟩
lemma CA3_3_10I2R5H_sound : CA3_3_10I2R5H.Encloses (homogeneousEntropy CA3_3_10I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R5Value CA3_3_10I2R5MassTerm_sound CA3_3_10I2R5Entropy_sound) (by decide +kernel)
def CA3_3_10I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA3_3_10I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA3_3_10I2R6Raw_sound (a : PairSlot) :
    (CA3_3_10I2R6Raw a).Encloses (CA3_3_10I2R6Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA3_3_10I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2063118680918729050143193271 / 2000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(709370730087177523146601219117 / 100000000000000000000000000000000), (120142661 / 50000000000000000000000000000000)⟩ ⟨(-171917092469757258222867236687177 / 25000000000000000000000000000000), (232934062451 / 100000000000000000000000000000000)⟩ ⟨-10, 2063118680918729050143193271, 1953125000000000000000000000⟩,
   .log ⟨(1299846659318336356780689 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(26888947315604340116762773 / 25000000000000000000000000000000), (1377 / 4000000000000000000000000000000)⟩ ⟨(-165489965283784483921883535142277 / 10000000000000000000000000000000), (66176372313 / 12500000000000000000000000000000)⟩ ⟨-24, 1299846659318336356780689, 1192092895507812500000000⟩,
   .log ⟨(10816758773791506086510037431569 / 100000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩ ⟨(24057266720408668255773678513131 / 100000000000000000000000000000000), (5726344461 / 50000000000000000000000000000000)⟩ ⟨(-222407351624576166655901974402823 / 100000000000000000000000000000000), (105879118673 / 100000000000000000000000000000000)⟩ ⟨-4, 10816758773791506086510037431569, 6250000000000000000000000000000⟩]
lemma CA3_3_10I2R6Certificates_valid :
    CA3_3_10I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA3_3_10I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R6Certificates (CA3_3_10I2R6CertificateIndex a)).input
lemma CA3_3_10I2R6P_check : ∀ a : PairSlot, contains (CA3_3_10I2R6Raw a) (CA3_3_10I2R6P a) = true := by
  decide +kernel
lemma CA3_3_10I2R6P_sound (a : PairSlot) :
    (CA3_3_10I2R6P a).Encloses (CA3_3_10I2R6Value a) :=
  contains_sound (CA3_3_10I2R6Raw_sound a) (CA3_3_10I2R6P_check a)
def CA3_3_10I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R6Certificates (CA3_3_10I2R6CertificateIndex a)).output
lemma CA3_3_10I2R6Terms_sound (a : PairSlot) :
    (CA3_3_10I2R6Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R6Certificates_valid
    (CA3_3_10I2R6CertificateIndex a) (CA3_3_10I2R6P_sound a)
def CA3_3_10I2R6Entropy : Ball := ⟨(25476223292161548136787815053549 / 100000000000000000000000000000000), (372916513 / 3125000000000000000000000000000)⟩
lemma CA3_3_10I2R6Entropy_sound : CA3_3_10I2R6Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R6Value CA3_3_10I2R6Terms CA3_3_10I2R6Terms_sound) (by decide +kernel)
def CA3_3_10I2R6Mass : Ball := ⟨(11023083640349972174887924565559 / 100000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I2R6Mass_sound : CA3_3_10I2R6Mass.Encloses (∑ a, CA3_3_10I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R6P CA3_3_10I2R6Value CA3_3_10I2R6P_sound) (by decide +kernel)
def CA3_3_10I2R6MassTermLogWitness : LogWitness := ⟨-4, 11023083640349972174887924565559, 6250000000000000000000000000000⟩
def CA3_3_10I2R6MassTermLog : Ball := ⟨(-1102589299616463351266717354721 / 500000000000000000000000000000), (105879118723 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I2R6MassTermLog_sound : CA3_3_10I2R6MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I2R6Mass_sound) (w := CA3_3_10I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_3_10I2R6MassTerm : Ball := ⟨(2430786814125434203440530503883 / 10000000000000000000000000000000), (1167114389 / 10000000000000000000000000000000)⟩
lemma CA3_3_10I2R6MassTerm_sound : CA3_3_10I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I2R6Mass_sound) CA3_3_10I2R6MassTermLog_sound) (by decide +kernel)
def CA3_3_10I2R6H : Ball := ⟨(1168355150907206102382510014719 / 100000000000000000000000000000000), (11802236153 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I2R6H_sound : CA3_3_10I2R6H.Encloses (homogeneousEntropy CA3_3_10I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R6Value CA3_3_10I2R6MassTerm_sound CA3_3_10I2R6Entropy_sound) (by decide +kernel)
def CA3_3_10I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA3_3_10I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA3_3_10I2R7Raw_sound (a : PairSlot) :
    (CA3_3_10I2R7Raw a).Encloses (CA3_3_10I2R7Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA3_3_10I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R7Certificates_valid :
    CA3_3_10I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R7Certificates (CA3_3_10I2R7CertificateIndex a)).input
lemma CA3_3_10I2R7P_check : ∀ a : PairSlot, contains (CA3_3_10I2R7Raw a) (CA3_3_10I2R7P a) = true := by
  decide +kernel
lemma CA3_3_10I2R7P_sound (a : PairSlot) :
    (CA3_3_10I2R7P a).Encloses (CA3_3_10I2R7Value a) :=
  contains_sound (CA3_3_10I2R7Raw_sound a) (CA3_3_10I2R7P_check a)
def CA3_3_10I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R7Certificates (CA3_3_10I2R7CertificateIndex a)).output
lemma CA3_3_10I2R7Terms_sound (a : PairSlot) :
    (CA3_3_10I2R7Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R7Certificates_valid
    (CA3_3_10I2R7CertificateIndex a) (CA3_3_10I2R7P_sound a)
def CA3_3_10I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R7Entropy_sound : CA3_3_10I2R7Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R7Value CA3_3_10I2R7Terms CA3_3_10I2R7Terms_sound) (by decide +kernel)
def CA3_3_10I2R7Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R7Mass_sound : CA3_3_10I2R7Mass.Encloses (∑ a, CA3_3_10I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R7P CA3_3_10I2R7Value CA3_3_10I2R7P_sound) (by decide +kernel)
def CA3_3_10I2R7MassTerm : Ball := .exact 0
lemma CA3_3_10I2R7MassTerm_sound : CA3_3_10I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R7Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R7Mass_sound)
def CA3_3_10I2R7H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R7H_sound : CA3_3_10I2R7H.Encloses (homogeneousEntropy CA3_3_10I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R7Value CA3_3_10I2R7MassTerm_sound CA3_3_10I2R7Entropy_sound) (by decide +kernel)
def CA3_3_10I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA3_3_10I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA3_3_10I2R8Raw_sound (a : PairSlot) :
    (CA3_3_10I2R8Raw a).Encloses (CA3_3_10I2R8Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA3_3_10I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R8Certificates_valid :
    CA3_3_10I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R8Certificates (CA3_3_10I2R8CertificateIndex a)).input
lemma CA3_3_10I2R8P_check : ∀ a : PairSlot, contains (CA3_3_10I2R8Raw a) (CA3_3_10I2R8P a) = true := by
  decide +kernel
lemma CA3_3_10I2R8P_sound (a : PairSlot) :
    (CA3_3_10I2R8P a).Encloses (CA3_3_10I2R8Value a) :=
  contains_sound (CA3_3_10I2R8Raw_sound a) (CA3_3_10I2R8P_check a)
def CA3_3_10I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R8Certificates (CA3_3_10I2R8CertificateIndex a)).output
lemma CA3_3_10I2R8Terms_sound (a : PairSlot) :
    (CA3_3_10I2R8Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R8Certificates_valid
    (CA3_3_10I2R8CertificateIndex a) (CA3_3_10I2R8P_sound a)
def CA3_3_10I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R8Entropy_sound : CA3_3_10I2R8Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R8Value CA3_3_10I2R8Terms CA3_3_10I2R8Terms_sound) (by decide +kernel)
def CA3_3_10I2R8Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R8Mass_sound : CA3_3_10I2R8Mass.Encloses (∑ a, CA3_3_10I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R8P CA3_3_10I2R8Value CA3_3_10I2R8P_sound) (by decide +kernel)
def CA3_3_10I2R8MassTerm : Ball := .exact 0
lemma CA3_3_10I2R8MassTerm_sound : CA3_3_10I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R8Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R8Mass_sound)
def CA3_3_10I2R8H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R8H_sound : CA3_3_10I2R8H.Encloses (homogeneousEntropy CA3_3_10I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R8Value CA3_3_10I2R8MassTerm_sound CA3_3_10I2R8Entropy_sound) (by decide +kernel)
def CA3_3_10I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA3_3_10I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA3_3_10I2R9Raw_sound (a : PairSlot) :
    (CA3_3_10I2R9Raw a).Encloses (CA3_3_10I2R9Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA3_3_10I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R9Certificates_valid :
    CA3_3_10I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R9Certificates (CA3_3_10I2R9CertificateIndex a)).input
lemma CA3_3_10I2R9P_check : ∀ a : PairSlot, contains (CA3_3_10I2R9Raw a) (CA3_3_10I2R9P a) = true := by
  decide +kernel
lemma CA3_3_10I2R9P_sound (a : PairSlot) :
    (CA3_3_10I2R9P a).Encloses (CA3_3_10I2R9Value a) :=
  contains_sound (CA3_3_10I2R9Raw_sound a) (CA3_3_10I2R9P_check a)
def CA3_3_10I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R9Certificates (CA3_3_10I2R9CertificateIndex a)).output
lemma CA3_3_10I2R9Terms_sound (a : PairSlot) :
    (CA3_3_10I2R9Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R9Certificates_valid
    (CA3_3_10I2R9CertificateIndex a) (CA3_3_10I2R9P_sound a)
def CA3_3_10I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R9Entropy_sound : CA3_3_10I2R9Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R9Value CA3_3_10I2R9Terms CA3_3_10I2R9Terms_sound) (by decide +kernel)
def CA3_3_10I2R9Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R9Mass_sound : CA3_3_10I2R9Mass.Encloses (∑ a, CA3_3_10I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R9P CA3_3_10I2R9Value CA3_3_10I2R9P_sound) (by decide +kernel)
def CA3_3_10I2R9MassTerm : Ball := .exact 0
lemma CA3_3_10I2R9MassTerm_sound : CA3_3_10I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R9Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R9Mass_sound)
def CA3_3_10I2R9H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R9H_sound : CA3_3_10I2R9H.Encloses (homogeneousEntropy CA3_3_10I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R9Value CA3_3_10I2R9MassTerm_sound CA3_3_10I2R9Entropy_sound) (by decide +kernel)
def CA3_3_10I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA3_3_10I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA3_3_10I2R10Raw_sound (a : PairSlot) :
    (CA3_3_10I2R10Raw a).Encloses (CA3_3_10I2R10Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA3_3_10I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R10Certificates_valid :
    CA3_3_10I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R10Certificates (CA3_3_10I2R10CertificateIndex a)).input
lemma CA3_3_10I2R10P_check : ∀ a : PairSlot, contains (CA3_3_10I2R10Raw a) (CA3_3_10I2R10P a) = true := by
  decide +kernel
lemma CA3_3_10I2R10P_sound (a : PairSlot) :
    (CA3_3_10I2R10P a).Encloses (CA3_3_10I2R10Value a) :=
  contains_sound (CA3_3_10I2R10Raw_sound a) (CA3_3_10I2R10P_check a)
def CA3_3_10I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R10Certificates (CA3_3_10I2R10CertificateIndex a)).output
lemma CA3_3_10I2R10Terms_sound (a : PairSlot) :
    (CA3_3_10I2R10Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R10Certificates_valid
    (CA3_3_10I2R10CertificateIndex a) (CA3_3_10I2R10P_sound a)
def CA3_3_10I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R10Entropy_sound : CA3_3_10I2R10Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R10Value CA3_3_10I2R10Terms CA3_3_10I2R10Terms_sound) (by decide +kernel)
def CA3_3_10I2R10Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R10Mass_sound : CA3_3_10I2R10Mass.Encloses (∑ a, CA3_3_10I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R10P CA3_3_10I2R10Value CA3_3_10I2R10P_sound) (by decide +kernel)
def CA3_3_10I2R10MassTerm : Ball := .exact 0
lemma CA3_3_10I2R10MassTerm_sound : CA3_3_10I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R10Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R10Mass_sound)
def CA3_3_10I2R10H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R10H_sound : CA3_3_10I2R10H.Encloses (homogeneousEntropy CA3_3_10I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R10Value CA3_3_10I2R10MassTerm_sound CA3_3_10I2R10Entropy_sound) (by decide +kernel)
def CA3_3_10I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA3_3_10I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA3_3_10I2R11Raw_sound (a : PairSlot) :
    (CA3_3_10I2R11Raw a).Encloses (CA3_3_10I2R11Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA3_3_10I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R11Certificates_valid :
    CA3_3_10I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R11Certificates (CA3_3_10I2R11CertificateIndex a)).input
lemma CA3_3_10I2R11P_check : ∀ a : PairSlot, contains (CA3_3_10I2R11Raw a) (CA3_3_10I2R11P a) = true := by
  decide +kernel
lemma CA3_3_10I2R11P_sound (a : PairSlot) :
    (CA3_3_10I2R11P a).Encloses (CA3_3_10I2R11Value a) :=
  contains_sound (CA3_3_10I2R11Raw_sound a) (CA3_3_10I2R11P_check a)
def CA3_3_10I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R11Certificates (CA3_3_10I2R11CertificateIndex a)).output
lemma CA3_3_10I2R11Terms_sound (a : PairSlot) :
    (CA3_3_10I2R11Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R11Certificates_valid
    (CA3_3_10I2R11CertificateIndex a) (CA3_3_10I2R11P_sound a)
def CA3_3_10I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R11Entropy_sound : CA3_3_10I2R11Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R11Value CA3_3_10I2R11Terms CA3_3_10I2R11Terms_sound) (by decide +kernel)
def CA3_3_10I2R11Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R11Mass_sound : CA3_3_10I2R11Mass.Encloses (∑ a, CA3_3_10I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R11P CA3_3_10I2R11Value CA3_3_10I2R11P_sound) (by decide +kernel)
def CA3_3_10I2R11MassTerm : Ball := .exact 0
lemma CA3_3_10I2R11MassTerm_sound : CA3_3_10I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R11Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R11Mass_sound)
def CA3_3_10I2R11H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R11H_sound : CA3_3_10I2R11H.Encloses (homogeneousEntropy CA3_3_10I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R11Value CA3_3_10I2R11MassTerm_sound CA3_3_10I2R11Entropy_sound) (by decide +kernel)
def CA3_3_10I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA3_3_10I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA3_3_10I2R12Raw_sound (a : PairSlot) :
    (CA3_3_10I2R12Raw a).Encloses (CA3_3_10I2R12Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA3_3_10I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R12Certificates_valid :
    CA3_3_10I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R12Certificates (CA3_3_10I2R12CertificateIndex a)).input
lemma CA3_3_10I2R12P_check : ∀ a : PairSlot, contains (CA3_3_10I2R12Raw a) (CA3_3_10I2R12P a) = true := by
  decide +kernel
lemma CA3_3_10I2R12P_sound (a : PairSlot) :
    (CA3_3_10I2R12P a).Encloses (CA3_3_10I2R12Value a) :=
  contains_sound (CA3_3_10I2R12Raw_sound a) (CA3_3_10I2R12P_check a)
def CA3_3_10I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R12Certificates (CA3_3_10I2R12CertificateIndex a)).output
lemma CA3_3_10I2R12Terms_sound (a : PairSlot) :
    (CA3_3_10I2R12Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R12Certificates_valid
    (CA3_3_10I2R12CertificateIndex a) (CA3_3_10I2R12P_sound a)
def CA3_3_10I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R12Entropy_sound : CA3_3_10I2R12Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R12Value CA3_3_10I2R12Terms CA3_3_10I2R12Terms_sound) (by decide +kernel)
def CA3_3_10I2R12Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R12Mass_sound : CA3_3_10I2R12Mass.Encloses (∑ a, CA3_3_10I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R12P CA3_3_10I2R12Value CA3_3_10I2R12P_sound) (by decide +kernel)
def CA3_3_10I2R12MassTerm : Ball := .exact 0
lemma CA3_3_10I2R12MassTerm_sound : CA3_3_10I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R12Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R12Mass_sound)
def CA3_3_10I2R12H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R12H_sound : CA3_3_10I2R12H.Encloses (homogeneousEntropy CA3_3_10I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R12Value CA3_3_10I2R12MassTerm_sound CA3_3_10I2R12Entropy_sound) (by decide +kernel)
def CA3_3_10I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA3_3_10I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA3_3_10I2R13Raw_sound (a : PairSlot) :
    (CA3_3_10I2R13Raw a).Encloses (CA3_3_10I2R13Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA3_3_10I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R13Certificates_valid :
    CA3_3_10I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R13Certificates (CA3_3_10I2R13CertificateIndex a)).input
lemma CA3_3_10I2R13P_check : ∀ a : PairSlot, contains (CA3_3_10I2R13Raw a) (CA3_3_10I2R13P a) = true := by
  decide +kernel
lemma CA3_3_10I2R13P_sound (a : PairSlot) :
    (CA3_3_10I2R13P a).Encloses (CA3_3_10I2R13Value a) :=
  contains_sound (CA3_3_10I2R13Raw_sound a) (CA3_3_10I2R13P_check a)
def CA3_3_10I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R13Certificates (CA3_3_10I2R13CertificateIndex a)).output
lemma CA3_3_10I2R13Terms_sound (a : PairSlot) :
    (CA3_3_10I2R13Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R13Certificates_valid
    (CA3_3_10I2R13CertificateIndex a) (CA3_3_10I2R13P_sound a)
def CA3_3_10I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R13Entropy_sound : CA3_3_10I2R13Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R13Value CA3_3_10I2R13Terms CA3_3_10I2R13Terms_sound) (by decide +kernel)
def CA3_3_10I2R13Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R13Mass_sound : CA3_3_10I2R13Mass.Encloses (∑ a, CA3_3_10I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R13P CA3_3_10I2R13Value CA3_3_10I2R13P_sound) (by decide +kernel)
def CA3_3_10I2R13MassTerm : Ball := .exact 0
lemma CA3_3_10I2R13MassTerm_sound : CA3_3_10I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R13Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R13Mass_sound)
def CA3_3_10I2R13H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R13H_sound : CA3_3_10I2R13H.Encloses (homogeneousEntropy CA3_3_10I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R13Value CA3_3_10I2R13MassTerm_sound CA3_3_10I2R13Entropy_sound) (by decide +kernel)
def CA3_3_10I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA3_3_10I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA3_3_10I2R14Raw_sound (a : PairSlot) :
    (CA3_3_10I2R14Raw a).Encloses (CA3_3_10I2R14Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA3_3_10I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R14Certificates_valid :
    CA3_3_10I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R14Certificates (CA3_3_10I2R14CertificateIndex a)).input
lemma CA3_3_10I2R14P_check : ∀ a : PairSlot, contains (CA3_3_10I2R14Raw a) (CA3_3_10I2R14P a) = true := by
  decide +kernel
lemma CA3_3_10I2R14P_sound (a : PairSlot) :
    (CA3_3_10I2R14P a).Encloses (CA3_3_10I2R14Value a) :=
  contains_sound (CA3_3_10I2R14Raw_sound a) (CA3_3_10I2R14P_check a)
def CA3_3_10I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R14Certificates (CA3_3_10I2R14CertificateIndex a)).output
lemma CA3_3_10I2R14Terms_sound (a : PairSlot) :
    (CA3_3_10I2R14Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R14Certificates_valid
    (CA3_3_10I2R14CertificateIndex a) (CA3_3_10I2R14P_sound a)
def CA3_3_10I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R14Entropy_sound : CA3_3_10I2R14Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R14Value CA3_3_10I2R14Terms CA3_3_10I2R14Terms_sound) (by decide +kernel)
def CA3_3_10I2R14Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R14Mass_sound : CA3_3_10I2R14Mass.Encloses (∑ a, CA3_3_10I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R14P CA3_3_10I2R14Value CA3_3_10I2R14P_sound) (by decide +kernel)
def CA3_3_10I2R14MassTerm : Ball := .exact 0
lemma CA3_3_10I2R14MassTerm_sound : CA3_3_10I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R14Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R14Mass_sound)
def CA3_3_10I2R14H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R14H_sound : CA3_3_10I2R14H.Encloses (homogeneousEntropy CA3_3_10I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R14Value CA3_3_10I2R14MassTerm_sound CA3_3_10I2R14Entropy_sound) (by decide +kernel)
def CA3_3_10I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA3_3_10I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA3_3_10I2R15Raw_sound (a : PairSlot) :
    (CA3_3_10I2R15Raw a).Encloses (CA3_3_10I2R15Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA3_3_10I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R15Certificates_valid :
    CA3_3_10I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R15Certificates (CA3_3_10I2R15CertificateIndex a)).input
lemma CA3_3_10I2R15P_check : ∀ a : PairSlot, contains (CA3_3_10I2R15Raw a) (CA3_3_10I2R15P a) = true := by
  decide +kernel
lemma CA3_3_10I2R15P_sound (a : PairSlot) :
    (CA3_3_10I2R15P a).Encloses (CA3_3_10I2R15Value a) :=
  contains_sound (CA3_3_10I2R15Raw_sound a) (CA3_3_10I2R15P_check a)
def CA3_3_10I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R15Certificates (CA3_3_10I2R15CertificateIndex a)).output
lemma CA3_3_10I2R15Terms_sound (a : PairSlot) :
    (CA3_3_10I2R15Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R15Certificates_valid
    (CA3_3_10I2R15CertificateIndex a) (CA3_3_10I2R15P_sound a)
def CA3_3_10I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R15Entropy_sound : CA3_3_10I2R15Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R15Value CA3_3_10I2R15Terms CA3_3_10I2R15Terms_sound) (by decide +kernel)
def CA3_3_10I2R15Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R15Mass_sound : CA3_3_10I2R15Mass.Encloses (∑ a, CA3_3_10I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R15P CA3_3_10I2R15Value CA3_3_10I2R15P_sound) (by decide +kernel)
def CA3_3_10I2R15MassTerm : Ball := .exact 0
lemma CA3_3_10I2R15MassTerm_sound : CA3_3_10I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R15Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R15Mass_sound)
def CA3_3_10I2R15H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R15H_sound : CA3_3_10I2R15H.Encloses (homogeneousEntropy CA3_3_10I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R15Value CA3_3_10I2R15MassTerm_sound CA3_3_10I2R15Entropy_sound) (by decide +kernel)
def CA3_3_10I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA3_3_10I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 3 10)) A3_3_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA3_3_10I2R16Raw_sound (a : PairSlot) :
    (CA3_3_10I2R16Raw a).Encloses (CA3_3_10I2R16Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA3_3_10I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_3_10I2R16Certificates_valid :
    CA3_3_10I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_3_10I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R16Certificates (CA3_3_10I2R16CertificateIndex a)).input
lemma CA3_3_10I2R16P_check : ∀ a : PairSlot, contains (CA3_3_10I2R16Raw a) (CA3_3_10I2R16P a) = true := by
  decide +kernel
lemma CA3_3_10I2R16P_sound (a : PairSlot) :
    (CA3_3_10I2R16P a).Encloses (CA3_3_10I2R16Value a) :=
  contains_sound (CA3_3_10I2R16Raw_sound a) (CA3_3_10I2R16P_check a)
def CA3_3_10I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I2R16Certificates (CA3_3_10I2R16CertificateIndex a)).output
lemma CA3_3_10I2R16Terms_sound (a : PairSlot) :
    (CA3_3_10I2R16Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I2R16Certificates_valid
    (CA3_3_10I2R16CertificateIndex a) (CA3_3_10I2R16P_sound a)
def CA3_3_10I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R16Entropy_sound : CA3_3_10I2R16Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I2R16Value CA3_3_10I2R16Terms CA3_3_10I2R16Terms_sound) (by decide +kernel)
def CA3_3_10I2R16Mass : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R16Mass_sound : CA3_3_10I2R16Mass.Encloses (∑ a, CA3_3_10I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I2R16P CA3_3_10I2R16Value CA3_3_10I2R16P_sound) (by decide +kernel)
def CA3_3_10I2R16MassTerm : Ball := .exact 0
lemma CA3_3_10I2R16MassTerm_sound : CA3_3_10I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I2R16Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I2R16Mass_sound)
def CA3_3_10I2R16H : Ball := ⟨0, 0⟩
lemma CA3_3_10I2R16H_sound : CA3_3_10I2R16H.Encloses (homogeneousEntropy CA3_3_10I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I2R16Value CA3_3_10I2R16MassTerm_sound CA3_3_10I2R16Entropy_sound) (by decide +kernel)
def CA3_3_10I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_3_10I2R0H
  | 1 => CA3_3_10I2R1H
  | 2 => CA3_3_10I2R2H
  | 3 => CA3_3_10I2R3H
  | 4 => CA3_3_10I2R4H
  | 5 => CA3_3_10I2R5H
  | 6 => CA3_3_10I2R6H
  | 7 => CA3_3_10I2R7H
  | 8 => CA3_3_10I2R8H
  | 9 => CA3_3_10I2R9H
  | 10 => CA3_3_10I2R10H
  | 11 => CA3_3_10I2R11H
  | 12 => CA3_3_10I2R12H
  | 13 => CA3_3_10I2R13H
  | 14 => CA3_3_10I2R14H
  | 15 => CA3_3_10I2R15H
  | 16 => CA3_3_10I2R16H
  | _ => (.exact 0)
lemma CA3_3_10I2ResidualEntropies_sound (k : Fin 17) :
    (CA3_3_10I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA3_3_10I2R0H_sound
  · exact CA3_3_10I2R1H_sound
  · exact CA3_3_10I2R2H_sound
  · exact CA3_3_10I2R3H_sound
  · exact CA3_3_10I2R4H_sound
  · exact CA3_3_10I2R5H_sound
  · exact CA3_3_10I2R6H_sound
  · exact CA3_3_10I2R7H_sound
  · exact CA3_3_10I2R8H_sound
  · exact CA3_3_10I2R9H_sound
  · exact CA3_3_10I2R10H_sound
  · exact CA3_3_10I2R11H_sound
  · exact CA3_3_10I2R12H_sound
  · exact CA3_3_10I2R13H_sound
  · exact CA3_3_10I2R14H_sound
  · exact CA3_3_10I2R15H_sound
  · exact CA3_3_10I2R16H_sound
def CA3_3_10I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | 3, 0, 5 => Z3_0_5H2H
  | _, _, _ => (.exact 0)
lemma CA3_3_10I2Singles_sound (u : Shape) (hu : u ∈ below (shape 3 3 10))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA3_3_10I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A3_3_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact Z2_0_6H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact Z3_0_5H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 3 2) by decide +kernel) hd |>.elim
def CA3_3_10I2Singleton : Ball := ⟨(24142252657962249439325503564723 / 100000000000000000000000000000000), (9777366223 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I2Singleton_sound : CA3_3_10I2Singleton.Encloses
    (singletonEntropy (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA3_3_10I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_3_10Law_sound u) CA3_3_10I2Singles_sound) (by decide +kernel)
def CA3_3_10I2Group : Ball := ⟨(83438278599254707218444497574729 / 100000000000000000000000000000000), (155658116763 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I2Group_sound : CA3_3_10I2Group.Encloses
    (groupedEntropy (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA3_3_10I2Singleton_sound
    (finSumBall_sound 17 CA3_3_10I2ResidualEntropies _ CA3_3_10I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA3_3_10I2H : Ball := ⟨(28617512088637626964024434023143 / 25000000000000000000000000000000), (452848691841 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I2_sound : CA3_3_10I2H.Encloses (stageACapacity (shape 3 3 10) 2) := by
  have hb := contains_sound (Ball.add_sound CA3_3_10I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA3_3_10I2Group_sound)))
    (show contains (.add CA3_3_10I2PairH (.neg (.mul (.exact 2) CA3_3_10I2Group))) CA3_3_10I2H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg]
  exact hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
