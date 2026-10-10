import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA4_6_6I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA4_6_6I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA4_6_6I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA4_6_6I2R0Raw_sound (a : PairSlot) :
    (CA4_6_6I2R0Raw a).Encloses (CA4_6_6I2R0Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA4_6_6I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(16120553786259023039634395387 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(35194515439582966269226210913 / 25000000000000000000000000000000), (47791271 / 100000000000000000000000000000000)⟩ ⟨(-106601933282416248877794389871 / 12207031250000000000000000000), (296461550171 / 100000000000000000000000000000000)⟩ ⟨-13, 16120553786259023039634395387, 12207031250000000000000000000⟩]
lemma CA4_6_6I2R0Certificates_valid :
    CA4_6_6I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA4_6_6I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R0Certificates (CA4_6_6I2R0CertificateIndex a)).input
lemma CA4_6_6I2R0P_check : ∀ a : PairSlot, contains (CA4_6_6I2R0Raw a) (CA4_6_6I2R0P a) = true := by
  decide +kernel
lemma CA4_6_6I2R0P_sound (a : PairSlot) :
    (CA4_6_6I2R0P a).Encloses (CA4_6_6I2R0Value a) :=
  contains_sound (CA4_6_6I2R0Raw_sound a) (CA4_6_6I2R0P_check a)
def CA4_6_6I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R0Certificates (CA4_6_6I2R0CertificateIndex a)).output
lemma CA4_6_6I2R0Terms_sound (a : PairSlot) :
    (CA4_6_6I2R0Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R0Certificates_valid
    (CA4_6_6I2R0CertificateIndex a) (CA4_6_6I2R0P_sound a)
def CA4_6_6I2R0Entropy : Ball := ⟨(35194515439582966269226210913 / 25000000000000000000000000000000), (47791271 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2R0Entropy_sound : CA4_6_6I2R0Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R0Value CA4_6_6I2R0Terms CA4_6_6I2R0Terms_sound) (by decide +kernel)
def CA4_6_6I2R0Mass : Ball := ⟨(16120553786259023039634395387 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2R0Mass_sound : CA4_6_6I2R0Mass.Encloses (∑ a, CA4_6_6I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R0P CA4_6_6I2R0Value CA4_6_6I2R0P_sound) (by decide +kernel)
def CA4_6_6I2R0MassTermLogWitness : LogWitness := ⟨-13, 16120553786259023039634395387, 12207031250000000000000000000⟩
def CA4_6_6I2R0MassTermLog : Ball := ⟨(-106601933282416248877794389871 / 12207031250000000000000000000), (296461550171 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2R0MassTermLog_sound : CA4_6_6I2R0MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I2R0Mass_sound) (w := CA4_6_6I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I2R0MassTerm : Ball := ⟨(35194515439582966269226210913 / 25000000000000000000000000000000), (47791271 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2R0MassTerm_sound : CA4_6_6I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I2R0Mass_sound) CA4_6_6I2R0MassTermLog_sound) (by decide +kernel)
def CA4_6_6I2R0H : Ball := ⟨0, (47791271 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I2R0H_sound : CA4_6_6I2R0H.Encloses (homogeneousEntropy CA4_6_6I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R0Value CA4_6_6I2R0MassTerm_sound CA4_6_6I2R0Entropy_sound) (by decide +kernel)
def CA4_6_6I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA4_6_6I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA4_6_6I2R1Raw_sound (a : PairSlot) :
    (CA4_6_6I2R1Raw a).Encloses (CA4_6_6I2R1Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA4_6_6I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(342689840677687947278184466827 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(1707607198642413904839239804119 / 50000000000000000000000000000000), (1306213179 / 100000000000000000000000000000000)⟩ ⟨(-124573812522828737285493488462043 / 25000000000000000000000000000000), (23822801771 / 12500000000000000000000000000000)⟩ ⟨-8, 342689840677687947278184466827, 195312500000000000000000000000⟩]
lemma CA4_6_6I2R1Certificates_valid :
    CA4_6_6I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA4_6_6I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R1Certificates (CA4_6_6I2R1CertificateIndex a)).input
lemma CA4_6_6I2R1P_check : ∀ a : PairSlot, contains (CA4_6_6I2R1Raw a) (CA4_6_6I2R1P a) = true := by
  decide +kernel
lemma CA4_6_6I2R1P_sound (a : PairSlot) :
    (CA4_6_6I2R1P a).Encloses (CA4_6_6I2R1Value a) :=
  contains_sound (CA4_6_6I2R1Raw_sound a) (CA4_6_6I2R1P_check a)
def CA4_6_6I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R1Certificates (CA4_6_6I2R1CertificateIndex a)).output
lemma CA4_6_6I2R1Terms_sound (a : PairSlot) :
    (CA4_6_6I2R1Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R1Certificates_valid
    (CA4_6_6I2R1CertificateIndex a) (CA4_6_6I2R1P_sound a)
def CA4_6_6I2R1Entropy : Ball := ⟨(1707607198642413904839239804119 / 25000000000000000000000000000000), (1306213179 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I2R1Entropy_sound : CA4_6_6I2R1Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R1Value CA4_6_6I2R1Terms CA4_6_6I2R1Terms_sound) (by decide +kernel)
def CA4_6_6I2R1Mass : Ball := ⟨(342689840677687947278184466827 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I2R1Mass_sound : CA4_6_6I2R1Mass.Encloses (∑ a, CA4_6_6I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R1P CA4_6_6I2R1Value CA4_6_6I2R1P_sound) (by decide +kernel)
def CA4_6_6I2R1MassTermLogWitness : LogWitness := ⟨-7, 342689840677687947278184466827, 195312500000000000000000000000⟩
def CA4_6_6I2R1MassTermLog : Ball := ⟨(-214490266017660209100125380398921 / 50000000000000000000000000000000), (33881318097 / 20000000000000000000000000000000)⟩
lemma CA4_6_6I2R1MassTermLog_sound : CA4_6_6I2R1MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I2R1Mass_sound) (w := CA4_6_6I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I2R1MassTerm : Ball := ⟨(183759087721267205798870959323 / 3125000000000000000000000000000), (2322156761 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2R1MassTerm_sound : CA4_6_6I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I2R1Mass_sound) CA4_6_6I2R1MassTermLog_sound) (by decide +kernel)
def CA4_6_6I2R1H : Ball := ⟨(47506899374455251689654425907 / 5000000000000000000000000000000), (4934583119 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2R1H_sound : CA4_6_6I2R1H.Encloses (homogeneousEntropy CA4_6_6I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R1Value CA4_6_6I2R1MassTerm_sound CA4_6_6I2R1Entropy_sound) (by decide +kernel)
def CA4_6_6I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA4_6_6I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA4_6_6I2R2Raw_sound (a : PairSlot) :
    (CA4_6_6I2R2Raw a).Encloses (CA4_6_6I2R2Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA4_6_6I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(392578074076873432328971580703 / 10000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩ ⟨(12710127118449255107747581091313 / 100000000000000000000000000000000), (4987898579 / 100000000000000000000000000000000)⟩ ⟨(-161880246984455849479716824224667 / 50000000000000000000000000000000), (127054942887 / 100000000000000000000000000000000)⟩ ⟨-5, 392578074076873432328971580703, 312500000000000000000000000000⟩,
   .log ⟨(150055798188837320755194742107 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(871639779638983671793257631171 / 50000000000000000000000000000000), (635511053 / 100000000000000000000000000000000)⟩ ⟨(-290438553577940022604062310221717 / 50000000000000000000000000000000), (105879119081 / 50000000000000000000000000000000)⟩ ⟨-9, 150055798188837320755194742107, 97656250000000000000000000000⟩,
   .log ⟨(14429221027212306203050005222897 / 100000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩ ⟨(27933742503376835608680350860191 / 100000000000000000000000000000000), (12222025867 / 100000000000000000000000000000000)⟩ ⟨(-193591479752760938066881720058871 / 100000000000000000000000000000000), (84703295327 / 100000000000000000000000000000000)⟩ ⟨-3, 14429221027212306203050005222897, 12500000000000000000000000000000⟩]
lemma CA4_6_6I2R2Certificates_valid :
    CA4_6_6I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA4_6_6I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R2Certificates (CA4_6_6I2R2CertificateIndex a)).input
lemma CA4_6_6I2R2P_check : ∀ a : PairSlot, contains (CA4_6_6I2R2Raw a) (CA4_6_6I2R2P a) = true := by
  decide +kernel
lemma CA4_6_6I2R2P_sound (a : PairSlot) :
    (CA4_6_6I2R2P a).Encloses (CA4_6_6I2R2Value a) :=
  contains_sound (CA4_6_6I2R2Raw_sound a) (CA4_6_6I2R2P_check a)
def CA4_6_6I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R2Certificates (CA4_6_6I2R2CertificateIndex a)).output
lemma CA4_6_6I2R2Terms_sound (a : PairSlot) :
    (CA4_6_6I2R2Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R2Certificates_valid
    (CA4_6_6I2R2CertificateIndex a) (CA4_6_6I2R2P_sound a)
def CA4_6_6I2R2Entropy : Ball := ⟨(56840555858831280511348543567501 / 100000000000000000000000000000000), (23468845131 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2R2Entropy_sound : CA4_6_6I2R2Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R2Value CA4_6_6I2R2Terms CA4_6_6I2R2Terms_sound) (by decide +kernel)
def CA4_6_6I2R2Mass : Ball := ⟨(4576201140301024826530043161077 / 20000000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
lemma CA4_6_6I2R2Mass_sound : CA4_6_6I2R2Mass.Encloses (∑ a, CA4_6_6I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R2P CA4_6_6I2R2Value CA4_6_6I2R2P_sound) (by decide +kernel)
def CA4_6_6I2R2MassTermLogWitness : LogWitness := ⟨-3, 4576201140301024826530043161077, 2500000000000000000000000000000⟩
def CA4_6_6I2R2MassTermLog : Ball := ⟨(-147486306495714444044522497902991 / 100000000000000000000000000000000), (42351647707 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I2R2MassTermLog_sound : CA4_6_6I2R2MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I2R2Mass_sound) (w := CA4_6_6I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I2R2MassTerm : Ball := ⟨(33746350198223744188971964201703 / 100000000000000000000000000000000), (4845241521 / 25000000000000000000000000000000)⟩
lemma CA4_6_6I2R2MassTerm_sound : CA4_6_6I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I2R2Mass_sound) CA4_6_6I2R2MassTermLog_sound) (by decide +kernel)
def CA4_6_6I2R2H : Ball := ⟨(11547102830303768161188289682899 / 50000000000000000000000000000000), (8569962243 / 20000000000000000000000000000000)⟩
lemma CA4_6_6I2R2H_sound : CA4_6_6I2R2H.Encloses (homogeneousEntropy CA4_6_6I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R2Value CA4_6_6I2R2MassTerm_sound CA4_6_6I2R2Entropy_sound) (by decide +kernel)
def CA4_6_6I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA4_6_6I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA4_6_6I2R3Raw_sound (a : PairSlot) :
    (CA4_6_6I2R3Raw a).Encloses (CA4_6_6I2R3Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA4_6_6I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(41833881572148228222134364679 / 6250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(67022967522245838608633604997 / 2000000000000000000000000000000), (1275648373 / 100000000000000000000000000000000)⟩ ⟨(-15645719273757112229711772937109 / 3125000000000000000000000000000), (190582414043 / 100000000000000000000000000000000)⟩ ⟨-8, 41833881572148228222134364679, 24414062500000000000000000000⟩,
   .log ⟨(23560010139129578072062203869873 / 100000000000000000000000000000000), (23 / 25000000000000000000000000000000)⟩ ⟨(34058807647137848371923715806317 / 100000000000000000000000000000000), (4989026263 / 25000000000000000000000000000000)⟩ ⟨(-18070242460640631962391026863803 / 12500000000000000000000000000000), (42351647561 / 50000000000000000000000000000000)⟩ ⟨-3, 23560010139129578072062203869873, 12500000000000000000000000000000⟩,
   .log ⟨(1296524902521145729802750542957 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(2817013236335323675411586281071 / 50000000000000000000000000000000), (2196398657 / 100000000000000000000000000000000)⟩ ⟨(-21727413263389898323943316318353 / 5000000000000000000000000000000), (42351647501 / 25000000000000000000000000000000)⟩ ⟨-7, 1296524902521145729802750542957, 781250000000000000000000000000⟩]
lemma CA4_6_6I2R3Certificates_valid :
    CA4_6_6I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA4_6_6I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R3Certificates (CA4_6_6I2R3CertificateIndex a)).input
lemma CA4_6_6I2R3P_check : ∀ a : PairSlot, contains (CA4_6_6I2R3Raw a) (CA4_6_6I2R3P a) = true := by
  decide +kernel
lemma CA4_6_6I2R3P_sound (a : PairSlot) :
    (CA4_6_6I2R3P a).Encloses (CA4_6_6I2R3Value a) :=
  contains_sound (CA4_6_6I2R3Raw_sound a) (CA4_6_6I2R3P_check a)
def CA4_6_6I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R3Certificates (CA4_6_6I2R3CertificateIndex a)).output
lemma CA4_6_6I2R3Terms_sound (a : PairSlot) :
    (CA4_6_6I2R3Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R3Certificates_valid
    (CA4_6_6I2R3CertificateIndex a) (CA4_6_6I2R3P_sound a)
def CA4_6_6I2R3Entropy : Ball := ⟨(43043982495920787653178568618309 / 50000000000000000000000000000000), (11714076041 / 25000000000000000000000000000000)⟩
lemma CA4_6_6I2R3Entropy_sound : CA4_6_6I2R3Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R3Value CA4_6_6I2R3Terms CA4_6_6I2R3Terms_sound) (by decide +kernel)
def CA4_6_6I2R3Mass : Ball := ⟨(12762938573402547726709552123847 / 25000000000000000000000000000000), (21 / 10000000000000000000000000000000)⟩
lemma CA4_6_6I2R3Mass_sound : CA4_6_6I2R3Mass.Encloses (∑ a, CA4_6_6I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R3P CA4_6_6I2R3Value CA4_6_6I2R3P_sound) (by decide +kernel)
def CA4_6_6I2R3MassTermLogWitness : LogWitness := ⟨-1, 12762938573402547726709552123847, 12500000000000000000000000000000⟩
def CA4_6_6I2R3MassTermLog : Ball := ⟨(-2689321110977372408220498540859 / 4000000000000000000000000000000), (42351647777 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2R3MassTermLog_sound : CA4_6_6I2R3MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I2R3Mass_sound) (w := CA4_6_6I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I2R3MassTerm : Ball := ⟨(8580910035889725034669812880701 / 25000000000000000000000000000000), (4324251861 / 20000000000000000000000000000000)⟩
lemma CA4_6_6I2R3MassTerm_sound : CA4_6_6I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I2R3Mass_sound) CA4_6_6I2R3MassTermLog_sound) (by decide +kernel)
def CA4_6_6I2R3H : Ball := ⟨(25882162424141337583838942856907 / 50000000000000000000000000000000), (68477563469 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2R3H_sound : CA4_6_6I2R3H.Encloses (homogeneousEntropy CA4_6_6I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R3Value CA4_6_6I2R3MassTerm_sound CA4_6_6I2R3Entropy_sound) (by decide +kernel)
def CA4_6_6I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA4_6_6I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA4_6_6I2R4Raw_sound (a : PairSlot) :
    (CA4_6_6I2R4Raw a).Encloses (CA4_6_6I2R4Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA4_6_6I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(537944720769634333105778087 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(21632873274805694756710200643 / 50000000000000000000000000000000), (14581033 / 100000000000000000000000000000000)⟩ ⟨(-251337084922216436087667882147817 / 25000000000000000000000000000000), (84703300541 / 25000000000000000000000000000000)⟩ ⟨-15, 537944720769634333105778087, 381469726562500000000000000⟩,
   .log ⟨(1564721597811605367484139850661 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(1301054201376719947245861971097 / 20000000000000000000000000000000), (231939887 / 10000000000000000000000000000000)⟩ ⟨(-207873113529645396793973769755997 / 50000000000000000000000000000000), (148230766547 / 100000000000000000000000000000000)⟩ ⟨-6, 1564721597811605367484139850661, 1562500000000000000000000000000⟩,
   .log ⟨(16433806017972605324744269093053 / 100000000000000000000000000000000), (19 / 20000000000000000000000000000000)⟩ ⟨(14838326922518451431311550396907 / 50000000000000000000000000000000), (6959987707 / 50000000000000000000000000000000)⟩ ⟨(-90291481512503675759619089157319 / 50000000000000000000000000000000), (84703295309 / 100000000000000000000000000000000)⟩ ⟨-3, 16433806017972605324744269093053, 12500000000000000000000000000000⟩,
   .log ⟨(386641586375149809325801854211 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(3759919424212129235666645789669 / 100000000000000000000000000000000), (1473741767 / 100000000000000000000000000000000)⟩ ⟨(-121557003847613869011454362955111 / 25000000000000000000000000000000), (190582413923 / 100000000000000000000000000000000)⟩ ⟨-8, 386641586375149809325801854211, 195312500000000000000000000000⟩,
   .log ⟨(31690359963280958440486636419 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(51065294204368170268623218623 / 20000000000000000000000000000000), (87239041 / 100000000000000000000000000000000)⟩ ⟨(-100711411655501456969392828743963 / 12500000000000000000000000000000), (137642855517 / 50000000000000000000000000000000)⟩ ⟨-12, 31690359963280958440486636419, 24414062500000000000000000000⟩]
lemma CA4_6_6I2R4Certificates_valid :
    CA4_6_6I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA4_6_6I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R4Certificates (CA4_6_6I2R4CertificateIndex a)).input
lemma CA4_6_6I2R4P_check : ∀ a : PairSlot, contains (CA4_6_6I2R4Raw a) (CA4_6_6I2R4P a) = true := by
  decide +kernel
lemma CA4_6_6I2R4P_sound (a : PairSlot) :
    (CA4_6_6I2R4P a).Encloses (CA4_6_6I2R4Value a) :=
  contains_sound (CA4_6_6I2R4Raw_sound a) (CA4_6_6I2R4P_check a)
def CA4_6_6I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R4Certificates (CA4_6_6I2R4CertificateIndex a)).output
lemma CA4_6_6I2R4Terms_sound (a : PairSlot) :
    (CA4_6_6I2R4Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R4Certificates_valid
    (CA4_6_6I2R4CertificateIndex a) (CA4_6_6I2R4P_sound a)
def CA4_6_6I2R4Entropy : Ball := ⟨(50548892671349424436784968979809 / 100000000000000000000000000000000), (4324531559 / 20000000000000000000000000000000)⟩
lemma CA4_6_6I2R4Entropy_sound : CA4_6_6I2R4Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R4Value CA4_6_6I2R4Terms CA4_6_6I2R4Terms_sound) (by decide +kernel)
def CA4_6_6I2R4Mass : Ball := ⟨(2115011303459201040478593529703 / 10000000000000000000000000000000), (67 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I2R4Mass_sound : CA4_6_6I2R4Mass.Encloses (∑ a, CA4_6_6I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R4P CA4_6_6I2R4Value CA4_6_6I2R4P_sound) (by decide +kernel)
def CA4_6_6I2R4MassTermLogWitness : LogWitness := ⟨-3, 2115011303459201040478593529703, 1250000000000000000000000000000⟩
def CA4_6_6I2R4MassTermLog : Ball := ⟨(-3107049872169863249670890214253 / 2000000000000000000000000000000), (16940659073 / 20000000000000000000000000000000)⟩
lemma CA4_6_6I2R4MassTermLog_sound : CA4_6_6I2R4MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I2R4Mass_sound) (w := CA4_6_6I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I2R4MassTerm : Ball := ⟨(8214307000063408053921907574261 / 25000000000000000000000000000000), (17914842923 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2R4MassTerm_sound : CA4_6_6I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I2R4Mass_sound) CA4_6_6I2R4MassTermLog_sound) (by decide +kernel)
def CA4_6_6I2R4H : Ball := ⟨(3538332934219158444219467736553 / 20000000000000000000000000000000), (19768750359 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I2R4H_sound : CA4_6_6I2R4H.Encloses (homogeneousEntropy CA4_6_6I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R4Value CA4_6_6I2R4MassTerm_sound CA4_6_6I2R4Entropy_sound) (by decide +kernel)
def CA4_6_6I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA4_6_6I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA4_6_6I2R5Raw_sound (a : PairSlot) :
    (CA4_6_6I2R5Raw a).Encloses (CA4_6_6I2R5Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA4_6_6I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(366867964914050562920159919 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(8674616178805014278614289101 / 100000000000000000000000000000000), (2952131 / 100000000000000000000000000000000)⟩ ⟨(-1182253154869667366780382040839071 / 100000000000000000000000000000000), (201170393133 / 50000000000000000000000000000000)⟩ ⟨-18, 366867964914050562920159919, 190734863281250000000000000⟩,
   .log ⟨(18693864025217342876314549801 / 4000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(626928441304711925665858511673 / 25000000000000000000000000000000), (445340231 / 50000000000000000000000000000000)⟩ ⟨(-524009208699282499991064633567 / 97656250000000000000000000000), (23822801777 / 12500000000000000000000000000000)⟩ ⟨-8, 18693864025217342876314549801, 15625000000000000000000000000⟩,
   .log ⟨(1084027016605092340520746337 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(30039356161377808794623549681 / 20000000000000000000000000000000), (2570979 / 5000000000000000000000000000000)⟩ ⟨(-54122836980975867761544448498667 / 6250000000000000000000000000000), (296461537327 / 100000000000000000000000000000000)⟩ ⟨-13, 1084027016605092340520746337, 762939453125000000000000000⟩]
lemma CA4_6_6I2R5Certificates_valid :
    CA4_6_6I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA4_6_6I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R5Certificates (CA4_6_6I2R5CertificateIndex a)).input
lemma CA4_6_6I2R5P_check : ∀ a : PairSlot, contains (CA4_6_6I2R5Raw a) (CA4_6_6I2R5P a) = true := by
  decide +kernel
lemma CA4_6_6I2R5P_sound (a : PairSlot) :
    (CA4_6_6I2R5P a).Encloses (CA4_6_6I2R5Value a) :=
  contains_sound (CA4_6_6I2R5Raw_sound a) (CA4_6_6I2R5P_check a)
def CA4_6_6I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R5Certificates (CA4_6_6I2R5CertificateIndex a)).output
lemma CA4_6_6I2R5Terms_sound (a : PairSlot) :
    (CA4_6_6I2R5Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R5Certificates_valid
    (CA4_6_6I2R5CertificateIndex a) (CA4_6_6I2R5P_sound a)
def CA4_6_6I2R5Entropy : Ball := ⟨(1333292581102270880457583042099 / 25000000000000000000000000000000), (945052173 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I2R5Entropy_sound : CA4_6_6I2R5Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R5Value CA4_6_6I2R5Terms CA4_6_6I2R5Terms_sound) (by decide +kernel)
def CA4_6_6I2R5Mass : Ball := ⟨(97084953765188630096407201251 / 10000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I2R5Mass_sound : CA4_6_6I2R5Mass.Encloses (∑ a, CA4_6_6I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R5P CA4_6_6I2R5Value CA4_6_6I2R5P_sound) (by decide +kernel)
def CA4_6_6I2R5MassTermLogWitness : LogWitness := ⟨-7, 97084953765188630096407201251, 78125000000000000000000000000⟩
def CA4_6_6I2R5MassTermLog : Ball := ⟨(-231737698238005191053161152691633 / 50000000000000000000000000000000), (84703295453 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I2R5MassTermLog_sound : CA4_6_6I2R5MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I2R5Mass_sound) (w := CA4_6_6I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I2R5MassTerm : Ball := ⟨(899929748763518745743438399873 / 20000000000000000000000000000000), (164468317 / 10000000000000000000000000000000)⟩
lemma CA4_6_6I2R5MassTerm_sound : CA4_6_6I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I2R5Mass_sound) CA4_6_6I2R5MassTermLog_sound) (by decide +kernel)
def CA4_6_6I2R5H : Ball := ⟨(833521580591489793113140169031 / 100000000000000000000000000000000), (883696879 / 25000000000000000000000000000000)⟩
lemma CA4_6_6I2R5H_sound : CA4_6_6I2R5H.Encloses (homogeneousEntropy CA4_6_6I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R5Value CA4_6_6I2R5MassTerm_sound CA4_6_6I2R5Entropy_sound) (by decide +kernel)
def CA4_6_6I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA4_6_6I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA4_6_6I2R6Raw_sound (a : PairSlot) :
    (CA4_6_6I2R6Raw a).Encloses (CA4_6_6I2R6Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA4_6_6I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(46676588696815480865680291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(68042507860451276832750281 / 10000000000000000000000000000000), (28419 / 12500000000000000000000000000000)⟩ ⟨(-1457743801767876191483891357708957 / 100000000000000000000000000000000), (48704608711 / 10000000000000000000000000000000)⟩ ⟨-22, 46676588696815480865680291, 23841857910156250000000000⟩,
   .log ⟨(1470405179475994634931 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(8914239811705917108227 / 12500000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩ ⟨(-484995016945338399562250601604557 / 20000000000000000000000000000000), (159266777073 / 20000000000000000000000000000000)⟩ ⟨-35, 23526482871615914158896, 23283064365386962890625⟩,
   .log ⟨(2447214525206584752764435531 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1214409141915755952238289027 / 2500000000000000000000000000000), (16582993 / 100000000000000000000000000000000)⟩ ⟨(-198496556702684665049664880038973 / 20000000000000000000000000000000), (33881321979 / 10000000000000000000000000000000)⟩ ⟨-15, 2447214525206584752764435531, 1525878906250000000000000000⟩]
lemma CA4_6_6I2R6Certificates_valid :
    CA4_6_6I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA4_6_6I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R6Certificates (CA4_6_6I2R6CertificateIndex a)).input
lemma CA4_6_6I2R6P_check : ∀ a : PairSlot, contains (CA4_6_6I2R6Raw a) (CA4_6_6I2R6P a) = true := by
  decide +kernel
lemma CA4_6_6I2R6P_sound (a : PairSlot) :
    (CA4_6_6I2R6P a).Encloses (CA4_6_6I2R6Value a) :=
  contains_sound (CA4_6_6I2R6Raw_sound a) (CA4_6_6I2R6P_check a)
def CA4_6_6I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R6Certificates (CA4_6_6I2R6CertificateIndex a)).output
lemma CA4_6_6I2R6Terms_sound (a : PairSlot) :
    (CA4_6_6I2R6Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R6Certificates_valid
    (CA4_6_6I2R6CertificateIndex a) (CA4_6_6I2R6P_sound a)
def CA4_6_6I2R6Entropy : Ball := ⟨(12484339615419062730215074583 / 25000000000000000000000000000000), (3407559 / 20000000000000000000000000000000)⟩
lemma CA4_6_6I2R6Entropy_sound : CA4_6_6I2R6Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R6Value CA4_6_6I2R6Terms CA4_6_6I2R6Terms_sound) (by decide +kernel)
def CA4_6_6I2R6Mass : Ball := ⟨(623473513678439796404846421 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I2R6Mass_sound : CA4_6_6I2R6Mass.Encloses (∑ a, CA4_6_6I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R6P CA4_6_6I2R6Value CA4_6_6I2R6P_sound) (by decide +kernel)
def CA4_6_6I2R6MassTermLogWitness : LogWitness := ⟨-15, 623473513678439796404846421, 381469726562500000000000000⟩
def CA4_6_6I2R6MassTermLog : Ball := ⟨(-990593291812139828845765896723109 / 100000000000000000000000000000000), (338813299221 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2R6MassTermLog_sound : CA4_6_6I2R6MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I2R6Mass_sound) (w := CA4_6_6I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I2R6MassTerm : Ball := ⟨(49408694421792549308377853077 / 100000000000000000000000000000000), (337987 / 2000000000000000000000000000000)⟩
lemma CA4_6_6I2R6MassTerm_sound : CA4_6_6I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I2R6Mass_sound) CA4_6_6I2R6MassTermLog_sound) (by decide +kernel)
def CA4_6_6I2R6H : Ball := ⟨(105732807976740322496489051 / 20000000000000000000000000000000), (6787429 / 20000000000000000000000000000000)⟩
lemma CA4_6_6I2R6H_sound : CA4_6_6I2R6H.Encloses (homogeneousEntropy CA4_6_6I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R6Value CA4_6_6I2R6MassTerm_sound CA4_6_6I2R6Entropy_sound) (by decide +kernel)
def CA4_6_6I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA4_6_6I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA4_6_6I2R7Raw_sound (a : PairSlot) :
    (CA4_6_6I2R7Raw a).Encloses (CA4_6_6I2R7Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA4_6_6I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I2R7Certificates_valid :
    CA4_6_6I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R7Certificates (CA4_6_6I2R7CertificateIndex a)).input
lemma CA4_6_6I2R7P_check : ∀ a : PairSlot, contains (CA4_6_6I2R7Raw a) (CA4_6_6I2R7P a) = true := by
  decide +kernel
lemma CA4_6_6I2R7P_sound (a : PairSlot) :
    (CA4_6_6I2R7P a).Encloses (CA4_6_6I2R7Value a) :=
  contains_sound (CA4_6_6I2R7Raw_sound a) (CA4_6_6I2R7P_check a)
def CA4_6_6I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R7Certificates (CA4_6_6I2R7CertificateIndex a)).output
lemma CA4_6_6I2R7Terms_sound (a : PairSlot) :
    (CA4_6_6I2R7Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R7Certificates_valid
    (CA4_6_6I2R7CertificateIndex a) (CA4_6_6I2R7P_sound a)
def CA4_6_6I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R7Entropy_sound : CA4_6_6I2R7Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R7Value CA4_6_6I2R7Terms CA4_6_6I2R7Terms_sound) (by decide +kernel)
def CA4_6_6I2R7Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R7Mass_sound : CA4_6_6I2R7Mass.Encloses (∑ a, CA4_6_6I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R7P CA4_6_6I2R7Value CA4_6_6I2R7P_sound) (by decide +kernel)
def CA4_6_6I2R7MassTerm : Ball := .exact 0
lemma CA4_6_6I2R7MassTerm_sound : CA4_6_6I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R7Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I2R7Mass_sound)
def CA4_6_6I2R7H : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R7H_sound : CA4_6_6I2R7H.Encloses (homogeneousEntropy CA4_6_6I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R7Value CA4_6_6I2R7MassTerm_sound CA4_6_6I2R7Entropy_sound) (by decide +kernel)
def CA4_6_6I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA4_6_6I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA4_6_6I2R8Raw_sound (a : PairSlot) :
    (CA4_6_6I2R8Raw a).Encloses (CA4_6_6I2R8Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA4_6_6I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I2R8Certificates_valid :
    CA4_6_6I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R8Certificates (CA4_6_6I2R8CertificateIndex a)).input
lemma CA4_6_6I2R8P_check : ∀ a : PairSlot, contains (CA4_6_6I2R8Raw a) (CA4_6_6I2R8P a) = true := by
  decide +kernel
lemma CA4_6_6I2R8P_sound (a : PairSlot) :
    (CA4_6_6I2R8P a).Encloses (CA4_6_6I2R8Value a) :=
  contains_sound (CA4_6_6I2R8Raw_sound a) (CA4_6_6I2R8P_check a)
def CA4_6_6I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R8Certificates (CA4_6_6I2R8CertificateIndex a)).output
lemma CA4_6_6I2R8Terms_sound (a : PairSlot) :
    (CA4_6_6I2R8Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R8Certificates_valid
    (CA4_6_6I2R8CertificateIndex a) (CA4_6_6I2R8P_sound a)
def CA4_6_6I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R8Entropy_sound : CA4_6_6I2R8Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R8Value CA4_6_6I2R8Terms CA4_6_6I2R8Terms_sound) (by decide +kernel)
def CA4_6_6I2R8Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R8Mass_sound : CA4_6_6I2R8Mass.Encloses (∑ a, CA4_6_6I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R8P CA4_6_6I2R8Value CA4_6_6I2R8P_sound) (by decide +kernel)
def CA4_6_6I2R8MassTerm : Ball := .exact 0
lemma CA4_6_6I2R8MassTerm_sound : CA4_6_6I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R8Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I2R8Mass_sound)
def CA4_6_6I2R8H : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R8H_sound : CA4_6_6I2R8H.Encloses (homogeneousEntropy CA4_6_6I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R8Value CA4_6_6I2R8MassTerm_sound CA4_6_6I2R8Entropy_sound) (by decide +kernel)
def CA4_6_6I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA4_6_6I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA4_6_6I2R9Raw_sound (a : PairSlot) :
    (CA4_6_6I2R9Raw a).Encloses (CA4_6_6I2R9Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA4_6_6I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I2R9Certificates_valid :
    CA4_6_6I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R9Certificates (CA4_6_6I2R9CertificateIndex a)).input
lemma CA4_6_6I2R9P_check : ∀ a : PairSlot, contains (CA4_6_6I2R9Raw a) (CA4_6_6I2R9P a) = true := by
  decide +kernel
lemma CA4_6_6I2R9P_sound (a : PairSlot) :
    (CA4_6_6I2R9P a).Encloses (CA4_6_6I2R9Value a) :=
  contains_sound (CA4_6_6I2R9Raw_sound a) (CA4_6_6I2R9P_check a)
def CA4_6_6I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R9Certificates (CA4_6_6I2R9CertificateIndex a)).output
lemma CA4_6_6I2R9Terms_sound (a : PairSlot) :
    (CA4_6_6I2R9Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R9Certificates_valid
    (CA4_6_6I2R9CertificateIndex a) (CA4_6_6I2R9P_sound a)
def CA4_6_6I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R9Entropy_sound : CA4_6_6I2R9Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R9Value CA4_6_6I2R9Terms CA4_6_6I2R9Terms_sound) (by decide +kernel)
def CA4_6_6I2R9Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R9Mass_sound : CA4_6_6I2R9Mass.Encloses (∑ a, CA4_6_6I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R9P CA4_6_6I2R9Value CA4_6_6I2R9P_sound) (by decide +kernel)
def CA4_6_6I2R9MassTerm : Ball := .exact 0
lemma CA4_6_6I2R9MassTerm_sound : CA4_6_6I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R9Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I2R9Mass_sound)
def CA4_6_6I2R9H : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R9H_sound : CA4_6_6I2R9H.Encloses (homogeneousEntropy CA4_6_6I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R9Value CA4_6_6I2R9MassTerm_sound CA4_6_6I2R9Entropy_sound) (by decide +kernel)
def CA4_6_6I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA4_6_6I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA4_6_6I2R10Raw_sound (a : PairSlot) :
    (CA4_6_6I2R10Raw a).Encloses (CA4_6_6I2R10Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA4_6_6I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I2R10Certificates_valid :
    CA4_6_6I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R10Certificates (CA4_6_6I2R10CertificateIndex a)).input
lemma CA4_6_6I2R10P_check : ∀ a : PairSlot, contains (CA4_6_6I2R10Raw a) (CA4_6_6I2R10P a) = true := by
  decide +kernel
lemma CA4_6_6I2R10P_sound (a : PairSlot) :
    (CA4_6_6I2R10P a).Encloses (CA4_6_6I2R10Value a) :=
  contains_sound (CA4_6_6I2R10Raw_sound a) (CA4_6_6I2R10P_check a)
def CA4_6_6I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R10Certificates (CA4_6_6I2R10CertificateIndex a)).output
lemma CA4_6_6I2R10Terms_sound (a : PairSlot) :
    (CA4_6_6I2R10Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R10Certificates_valid
    (CA4_6_6I2R10CertificateIndex a) (CA4_6_6I2R10P_sound a)
def CA4_6_6I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R10Entropy_sound : CA4_6_6I2R10Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R10Value CA4_6_6I2R10Terms CA4_6_6I2R10Terms_sound) (by decide +kernel)
def CA4_6_6I2R10Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R10Mass_sound : CA4_6_6I2R10Mass.Encloses (∑ a, CA4_6_6I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R10P CA4_6_6I2R10Value CA4_6_6I2R10P_sound) (by decide +kernel)
def CA4_6_6I2R10MassTerm : Ball := .exact 0
lemma CA4_6_6I2R10MassTerm_sound : CA4_6_6I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R10Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I2R10Mass_sound)
def CA4_6_6I2R10H : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R10H_sound : CA4_6_6I2R10H.Encloses (homogeneousEntropy CA4_6_6I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R10Value CA4_6_6I2R10MassTerm_sound CA4_6_6I2R10Entropy_sound) (by decide +kernel)
def CA4_6_6I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA4_6_6I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA4_6_6I2R11Raw_sound (a : PairSlot) :
    (CA4_6_6I2R11Raw a).Encloses (CA4_6_6I2R11Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA4_6_6I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I2R11Certificates_valid :
    CA4_6_6I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R11Certificates (CA4_6_6I2R11CertificateIndex a)).input
lemma CA4_6_6I2R11P_check : ∀ a : PairSlot, contains (CA4_6_6I2R11Raw a) (CA4_6_6I2R11P a) = true := by
  decide +kernel
lemma CA4_6_6I2R11P_sound (a : PairSlot) :
    (CA4_6_6I2R11P a).Encloses (CA4_6_6I2R11Value a) :=
  contains_sound (CA4_6_6I2R11Raw_sound a) (CA4_6_6I2R11P_check a)
def CA4_6_6I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R11Certificates (CA4_6_6I2R11CertificateIndex a)).output
lemma CA4_6_6I2R11Terms_sound (a : PairSlot) :
    (CA4_6_6I2R11Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R11Certificates_valid
    (CA4_6_6I2R11CertificateIndex a) (CA4_6_6I2R11P_sound a)
def CA4_6_6I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R11Entropy_sound : CA4_6_6I2R11Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R11Value CA4_6_6I2R11Terms CA4_6_6I2R11Terms_sound) (by decide +kernel)
def CA4_6_6I2R11Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R11Mass_sound : CA4_6_6I2R11Mass.Encloses (∑ a, CA4_6_6I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R11P CA4_6_6I2R11Value CA4_6_6I2R11P_sound) (by decide +kernel)
def CA4_6_6I2R11MassTerm : Ball := .exact 0
lemma CA4_6_6I2R11MassTerm_sound : CA4_6_6I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R11Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I2R11Mass_sound)
def CA4_6_6I2R11H : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R11H_sound : CA4_6_6I2R11H.Encloses (homogeneousEntropy CA4_6_6I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R11Value CA4_6_6I2R11MassTerm_sound CA4_6_6I2R11Entropy_sound) (by decide +kernel)
def CA4_6_6I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA4_6_6I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA4_6_6I2R12Raw_sound (a : PairSlot) :
    (CA4_6_6I2R12Raw a).Encloses (CA4_6_6I2R12Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA4_6_6I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I2R12Certificates_valid :
    CA4_6_6I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R12Certificates (CA4_6_6I2R12CertificateIndex a)).input
lemma CA4_6_6I2R12P_check : ∀ a : PairSlot, contains (CA4_6_6I2R12Raw a) (CA4_6_6I2R12P a) = true := by
  decide +kernel
lemma CA4_6_6I2R12P_sound (a : PairSlot) :
    (CA4_6_6I2R12P a).Encloses (CA4_6_6I2R12Value a) :=
  contains_sound (CA4_6_6I2R12Raw_sound a) (CA4_6_6I2R12P_check a)
def CA4_6_6I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R12Certificates (CA4_6_6I2R12CertificateIndex a)).output
lemma CA4_6_6I2R12Terms_sound (a : PairSlot) :
    (CA4_6_6I2R12Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R12Certificates_valid
    (CA4_6_6I2R12CertificateIndex a) (CA4_6_6I2R12P_sound a)
def CA4_6_6I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R12Entropy_sound : CA4_6_6I2R12Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R12Value CA4_6_6I2R12Terms CA4_6_6I2R12Terms_sound) (by decide +kernel)
def CA4_6_6I2R12Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R12Mass_sound : CA4_6_6I2R12Mass.Encloses (∑ a, CA4_6_6I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R12P CA4_6_6I2R12Value CA4_6_6I2R12P_sound) (by decide +kernel)
def CA4_6_6I2R12MassTerm : Ball := .exact 0
lemma CA4_6_6I2R12MassTerm_sound : CA4_6_6I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R12Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I2R12Mass_sound)
def CA4_6_6I2R12H : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R12H_sound : CA4_6_6I2R12H.Encloses (homogeneousEntropy CA4_6_6I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R12Value CA4_6_6I2R12MassTerm_sound CA4_6_6I2R12Entropy_sound) (by decide +kernel)
def CA4_6_6I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA4_6_6I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA4_6_6I2R13Raw_sound (a : PairSlot) :
    (CA4_6_6I2R13Raw a).Encloses (CA4_6_6I2R13Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA4_6_6I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I2R13Certificates_valid :
    CA4_6_6I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R13Certificates (CA4_6_6I2R13CertificateIndex a)).input
lemma CA4_6_6I2R13P_check : ∀ a : PairSlot, contains (CA4_6_6I2R13Raw a) (CA4_6_6I2R13P a) = true := by
  decide +kernel
lemma CA4_6_6I2R13P_sound (a : PairSlot) :
    (CA4_6_6I2R13P a).Encloses (CA4_6_6I2R13Value a) :=
  contains_sound (CA4_6_6I2R13Raw_sound a) (CA4_6_6I2R13P_check a)
def CA4_6_6I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R13Certificates (CA4_6_6I2R13CertificateIndex a)).output
lemma CA4_6_6I2R13Terms_sound (a : PairSlot) :
    (CA4_6_6I2R13Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R13Certificates_valid
    (CA4_6_6I2R13CertificateIndex a) (CA4_6_6I2R13P_sound a)
def CA4_6_6I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R13Entropy_sound : CA4_6_6I2R13Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R13Value CA4_6_6I2R13Terms CA4_6_6I2R13Terms_sound) (by decide +kernel)
def CA4_6_6I2R13Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R13Mass_sound : CA4_6_6I2R13Mass.Encloses (∑ a, CA4_6_6I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R13P CA4_6_6I2R13Value CA4_6_6I2R13P_sound) (by decide +kernel)
def CA4_6_6I2R13MassTerm : Ball := .exact 0
lemma CA4_6_6I2R13MassTerm_sound : CA4_6_6I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R13Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I2R13Mass_sound)
def CA4_6_6I2R13H : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R13H_sound : CA4_6_6I2R13H.Encloses (homogeneousEntropy CA4_6_6I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R13Value CA4_6_6I2R13MassTerm_sound CA4_6_6I2R13Entropy_sound) (by decide +kernel)
def CA4_6_6I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA4_6_6I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA4_6_6I2R14Raw_sound (a : PairSlot) :
    (CA4_6_6I2R14Raw a).Encloses (CA4_6_6I2R14Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA4_6_6I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I2R14Certificates_valid :
    CA4_6_6I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R14Certificates (CA4_6_6I2R14CertificateIndex a)).input
lemma CA4_6_6I2R14P_check : ∀ a : PairSlot, contains (CA4_6_6I2R14Raw a) (CA4_6_6I2R14P a) = true := by
  decide +kernel
lemma CA4_6_6I2R14P_sound (a : PairSlot) :
    (CA4_6_6I2R14P a).Encloses (CA4_6_6I2R14Value a) :=
  contains_sound (CA4_6_6I2R14Raw_sound a) (CA4_6_6I2R14P_check a)
def CA4_6_6I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R14Certificates (CA4_6_6I2R14CertificateIndex a)).output
lemma CA4_6_6I2R14Terms_sound (a : PairSlot) :
    (CA4_6_6I2R14Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R14Certificates_valid
    (CA4_6_6I2R14CertificateIndex a) (CA4_6_6I2R14P_sound a)
def CA4_6_6I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R14Entropy_sound : CA4_6_6I2R14Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R14Value CA4_6_6I2R14Terms CA4_6_6I2R14Terms_sound) (by decide +kernel)
def CA4_6_6I2R14Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R14Mass_sound : CA4_6_6I2R14Mass.Encloses (∑ a, CA4_6_6I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R14P CA4_6_6I2R14Value CA4_6_6I2R14P_sound) (by decide +kernel)
def CA4_6_6I2R14MassTerm : Ball := .exact 0
lemma CA4_6_6I2R14MassTerm_sound : CA4_6_6I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R14Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I2R14Mass_sound)
def CA4_6_6I2R14H : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R14H_sound : CA4_6_6I2R14H.Encloses (homogeneousEntropy CA4_6_6I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R14Value CA4_6_6I2R14MassTerm_sound CA4_6_6I2R14Entropy_sound) (by decide +kernel)
def CA4_6_6I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA4_6_6I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA4_6_6I2R15Raw_sound (a : PairSlot) :
    (CA4_6_6I2R15Raw a).Encloses (CA4_6_6I2R15Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA4_6_6I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I2R15Certificates_valid :
    CA4_6_6I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R15Certificates (CA4_6_6I2R15CertificateIndex a)).input
lemma CA4_6_6I2R15P_check : ∀ a : PairSlot, contains (CA4_6_6I2R15Raw a) (CA4_6_6I2R15P a) = true := by
  decide +kernel
lemma CA4_6_6I2R15P_sound (a : PairSlot) :
    (CA4_6_6I2R15P a).Encloses (CA4_6_6I2R15Value a) :=
  contains_sound (CA4_6_6I2R15Raw_sound a) (CA4_6_6I2R15P_check a)
def CA4_6_6I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R15Certificates (CA4_6_6I2R15CertificateIndex a)).output
lemma CA4_6_6I2R15Terms_sound (a : PairSlot) :
    (CA4_6_6I2R15Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R15Certificates_valid
    (CA4_6_6I2R15CertificateIndex a) (CA4_6_6I2R15P_sound a)
def CA4_6_6I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R15Entropy_sound : CA4_6_6I2R15Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R15Value CA4_6_6I2R15Terms CA4_6_6I2R15Terms_sound) (by decide +kernel)
def CA4_6_6I2R15Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R15Mass_sound : CA4_6_6I2R15Mass.Encloses (∑ a, CA4_6_6I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R15P CA4_6_6I2R15Value CA4_6_6I2R15P_sound) (by decide +kernel)
def CA4_6_6I2R15MassTerm : Ball := .exact 0
lemma CA4_6_6I2R15MassTerm_sound : CA4_6_6I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R15Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I2R15Mass_sound)
def CA4_6_6I2R15H : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R15H_sound : CA4_6_6I2R15H.Encloses (homogeneousEntropy CA4_6_6I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R15Value CA4_6_6I2R15MassTerm_sound CA4_6_6I2R15Entropy_sound) (by decide +kernel)
def CA4_6_6I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA4_6_6I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA4_6_6I2R16Raw_sound (a : PairSlot) :
    (CA4_6_6I2R16Raw a).Encloses (CA4_6_6I2R16Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA4_6_6I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I2R16Certificates_valid :
    CA4_6_6I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R16Certificates (CA4_6_6I2R16CertificateIndex a)).input
lemma CA4_6_6I2R16P_check : ∀ a : PairSlot, contains (CA4_6_6I2R16Raw a) (CA4_6_6I2R16P a) = true := by
  decide +kernel
lemma CA4_6_6I2R16P_sound (a : PairSlot) :
    (CA4_6_6I2R16P a).Encloses (CA4_6_6I2R16Value a) :=
  contains_sound (CA4_6_6I2R16Raw_sound a) (CA4_6_6I2R16P_check a)
def CA4_6_6I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I2R16Certificates (CA4_6_6I2R16CertificateIndex a)).output
lemma CA4_6_6I2R16Terms_sound (a : PairSlot) :
    (CA4_6_6I2R16Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2R16Certificates_valid
    (CA4_6_6I2R16CertificateIndex a) (CA4_6_6I2R16P_sound a)
def CA4_6_6I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R16Entropy_sound : CA4_6_6I2R16Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I2R16Value CA4_6_6I2R16Terms CA4_6_6I2R16Terms_sound) (by decide +kernel)
def CA4_6_6I2R16Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R16Mass_sound : CA4_6_6I2R16Mass.Encloses (∑ a, CA4_6_6I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I2R16P CA4_6_6I2R16Value CA4_6_6I2R16P_sound) (by decide +kernel)
def CA4_6_6I2R16MassTerm : Ball := .exact 0
lemma CA4_6_6I2R16MassTerm_sound : CA4_6_6I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2R16Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I2R16Mass_sound)
def CA4_6_6I2R16H : Ball := ⟨0, 0⟩
lemma CA4_6_6I2R16H_sound : CA4_6_6I2R16H.Encloses (homogeneousEntropy CA4_6_6I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2R16Value CA4_6_6I2R16MassTerm_sound CA4_6_6I2R16Entropy_sound) (by decide +kernel)
def CA4_6_6I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_6_6I2R0H
  | 1 => CA4_6_6I2R1H
  | 2 => CA4_6_6I2R2H
  | 3 => CA4_6_6I2R3H
  | 4 => CA4_6_6I2R4H
  | 5 => CA4_6_6I2R5H
  | 6 => CA4_6_6I2R6H
  | 7 => CA4_6_6I2R7H
  | 8 => CA4_6_6I2R8H
  | 9 => CA4_6_6I2R9H
  | 10 => CA4_6_6I2R10H
  | 11 => CA4_6_6I2R11H
  | 12 => CA4_6_6I2R12H
  | 13 => CA4_6_6I2R13H
  | 14 => CA4_6_6I2R14H
  | 15 => CA4_6_6I2R15H
  | 16 => CA4_6_6I2R16H
  | _ => (.exact 0)
lemma CA4_6_6I2ResidualEntropies_sound (k : Fin 17) :
    (CA4_6_6I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA4_6_6I2R0H_sound
  · exact CA4_6_6I2R1H_sound
  · exact CA4_6_6I2R2H_sound
  · exact CA4_6_6I2R3H_sound
  · exact CA4_6_6I2R4H_sound
  · exact CA4_6_6I2R5H_sound
  · exact CA4_6_6I2R6H_sound
  · exact CA4_6_6I2R7H_sound
  · exact CA4_6_6I2R8H_sound
  · exact CA4_6_6I2R9H_sound
  · exact CA4_6_6I2R10H_sound
  · exact CA4_6_6I2R11H_sound
  · exact CA4_6_6I2R12H_sound
  · exact CA4_6_6I2R13H_sound
  · exact CA4_6_6I2R14H_sound
  · exact CA4_6_6I2R15H_sound
  · exact CA4_6_6I2R16H_sound
def CA4_6_6I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 0, 6, 2 => Z0_6_2H2H
  | 2, 0, 6 => Z2_0_6H2H
  | 3, 0, 5 => Z3_0_5H2H
  | 4, 0, 4 => Z4_0_4H2H
  | _, _, _ => (.exact 0)
lemma CA4_6_6I2Singles_sound (u : Shape) (hu : u ∈ below (shape 4 6 6))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA4_6_6I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A4_6_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z0_5_3H2H_sound
  · exact Z0_6_2H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 6 1) by decide +kernel) hd |>.elim
  · exact Z2_0_6H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 5 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 6 0) by decide +kernel) hd |>.elim
  · exact Z3_0_5H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 4 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 5 0) by decide +kernel) hd |>.elim
  · exact Z4_0_4H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 1 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 3 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 4 0) by decide +kernel) hd |>.elim
def CA4_6_6I2Singleton : Ball := ⟨(385647486515267613255081256021 / 12500000000000000000000000000000), (648017637 / 25000000000000000000000000000000)⟩
lemma CA4_6_6I2Singleton_sound : CA4_6_6I2Singleton.Encloses
    (singletonEntropy (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA4_6_6I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_6_6Law_sound u) CA4_6_6I2Singles_sound) (by decide +kernel)
def CA4_6_6I2Group : Ball := ⟨(97419563304228623145711164942971 / 100000000000000000000000000000000), (10128489767 / 6250000000000000000000000000000)⟩
lemma CA4_6_6I2Group_sound : CA4_6_6I2Group.Encloses
    (groupedEntropy (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA4_6_6I2Singleton_sound
    (finSumBall_sound 17 CA4_6_6I2ResidualEntropies _ CA4_6_6I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA4_6_6I2H : Ball := ⟨(57023359862945864118495179339019 / 50000000000000000000000000000000), (477361653827 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I2_sound : CA4_6_6I2H.Encloses (stageACapacity (shape 4 6 6) 2) := by
  have hb := contains_sound (Ball.add_sound CA4_6_6I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA4_6_6I2Group_sound)))
    (show contains (.add CA4_6_6I2PairH (.neg (.mul (.exact 2) CA4_6_6I2Group))) CA4_6_6I2H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg]
  exact hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
