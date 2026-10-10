import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA2_6_8I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_6_8I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA2_6_8I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA2_6_8I2R0Raw_sound (a : PairSlot) :
    (CA2_6_8I2R0Raw a).Encloses (CA2_6_8I2R0Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA2_6_8I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(7283242185896305552952829 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(119700847339367931999913737 / 100000000000000000000000000000000), (1543 / 4000000000000000000000000000000)⟩ ⟨(-821755231283971483508731748424759 / 50000000000000000000000000000000), (529409322223 / 100000000000000000000000000000000)⟩ ⟨-24, 7283242185896305552952829, 5960464477539062500000000⟩]
lemma CA2_6_8I2R0Certificates_valid :
    CA2_6_8I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA2_6_8I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R0Certificates (CA2_6_8I2R0CertificateIndex a)).input
lemma CA2_6_8I2R0P_check : ∀ a : PairSlot, contains (CA2_6_8I2R0Raw a) (CA2_6_8I2R0P a) = true := by
  decide +kernel
lemma CA2_6_8I2R0P_sound (a : PairSlot) :
    (CA2_6_8I2R0P a).Encloses (CA2_6_8I2R0Value a) :=
  contains_sound (CA2_6_8I2R0Raw_sound a) (CA2_6_8I2R0P_check a)
def CA2_6_8I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R0Certificates (CA2_6_8I2R0CertificateIndex a)).output
lemma CA2_6_8I2R0Terms_sound (a : PairSlot) :
    (CA2_6_8I2R0Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R0Certificates_valid
    (CA2_6_8I2R0CertificateIndex a) (CA2_6_8I2R0P_sound a)
def CA2_6_8I2R0Entropy : Ball := ⟨(119700847339367931999913737 / 100000000000000000000000000000000), (1543 / 4000000000000000000000000000000)⟩
lemma CA2_6_8I2R0Entropy_sound : CA2_6_8I2R0Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R0Value CA2_6_8I2R0Terms CA2_6_8I2R0Terms_sound) (by decide +kernel)
def CA2_6_8I2R0Mass : Ball := ⟨(7283242185896305552952829 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I2R0Mass_sound : CA2_6_8I2R0Mass.Encloses (∑ a, CA2_6_8I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R0P CA2_6_8I2R0Value CA2_6_8I2R0P_sound) (by decide +kernel)
def CA2_6_8I2R0MassTermLogWitness : LogWitness := ⟨-24, 7283242185896305552952829, 5960464477539062500000000⟩
def CA2_6_8I2R0MassTermLog : Ball := ⟨(-821755231283971483508731748424759 / 50000000000000000000000000000000), (529409322223 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I2R0MassTermLog_sound : CA2_6_8I2R0MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I2R0Mass_sound) (w := CA2_6_8I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I2R0MassTerm : Ball := ⟨(119700847339367931999913737 / 100000000000000000000000000000000), (1543 / 4000000000000000000000000000000)⟩
lemma CA2_6_8I2R0MassTerm_sound : CA2_6_8I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I2R0Mass_sound) CA2_6_8I2R0MassTermLog_sound) (by decide +kernel)
def CA2_6_8I2R0H : Ball := ⟨0, (1543 / 2000000000000000000000000000000)⟩
lemma CA2_6_8I2R0H_sound : CA2_6_8I2R0H.Encloses (homogeneousEntropy CA2_6_8I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R0Value CA2_6_8I2R0MassTerm_sound CA2_6_8I2R0Entropy_sound) (by decide +kernel)
def CA2_6_8I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA2_6_8I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA2_6_8I2R1Raw_sound (a : PairSlot) :
    (CA2_6_8I2R1Raw a).Encloses (CA2_6_8I2R1Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA2_6_8I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3241019566401678236465874989 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(33502540808053205599377088871 / 100000000000000000000000000000000), (439241 / 4000000000000000000000000000000)⟩ ⟨(-516851875183974785739036453103619 / 50000000000000000000000000000000), (84703310159 / 25000000000000000000000000000000)⟩ ⟨-15, 3241019566401678236465874989, 3051757812500000000000000000⟩]
lemma CA2_6_8I2R1Certificates_valid :
    CA2_6_8I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA2_6_8I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R1Certificates (CA2_6_8I2R1CertificateIndex a)).input
lemma CA2_6_8I2R1P_check : ∀ a : PairSlot, contains (CA2_6_8I2R1Raw a) (CA2_6_8I2R1P a) = true := by
  decide +kernel
lemma CA2_6_8I2R1P_sound (a : PairSlot) :
    (CA2_6_8I2R1P a).Encloses (CA2_6_8I2R1Value a) :=
  contains_sound (CA2_6_8I2R1Raw_sound a) (CA2_6_8I2R1P_check a)
def CA2_6_8I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R1Certificates (CA2_6_8I2R1CertificateIndex a)).output
lemma CA2_6_8I2R1Terms_sound (a : PairSlot) :
    (CA2_6_8I2R1Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R1Certificates_valid
    (CA2_6_8I2R1CertificateIndex a) (CA2_6_8I2R1P_sound a)
def CA2_6_8I2R1Entropy : Ball := ⟨(33502540808053205599377088871 / 50000000000000000000000000000000), (439241 / 2000000000000000000000000000000)⟩
lemma CA2_6_8I2R1Entropy_sound : CA2_6_8I2R1Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R1Value CA2_6_8I2R1Terms CA2_6_8I2R1Terms_sound) (by decide +kernel)
def CA2_6_8I2R1Mass : Ball := ⟨(3241019566401678236465874989 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma CA2_6_8I2R1Mass_sound : CA2_6_8I2R1Mass.Encloses (∑ a, CA2_6_8I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R1P CA2_6_8I2R1Value CA2_6_8I2R1P_sound) (by decide +kernel)
def CA2_6_8I2R1MassTermLogWitness : LogWitness := ⟨-14, 3241019566401678236465874989, 3051757812500000000000000000⟩
def CA2_6_8I2R1MassTermLog : Ball := ⟨(-241097258077988760134087428289227 / 25000000000000000000000000000000), (317637416953 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I2R1MassTermLog_sound : CA2_6_8I2R1MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I2R1Mass_sound) (w := CA2_6_8I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I2R1MassTerm : Ball := ⟨(12502414893384906351426921547 / 20000000000000000000000000000000), (20589421 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I2R1MassTerm_sound : CA2_6_8I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I2R1Mass_sound) CA2_6_8I2R1MassTermLog_sound) (by decide +kernel)
def CA2_6_8I2R1H : Ball := ⟨(4493007149181879441619570007 / 100000000000000000000000000000000), (42551471 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I2R1H_sound : CA2_6_8I2R1H.Encloses (homogeneousEntropy CA2_6_8I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R1Value CA2_6_8I2R1MassTerm_sound CA2_6_8I2R1Entropy_sound) (by decide +kernel)
def CA2_6_8I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA2_6_8I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA2_6_8I2R2Raw_sound (a : PairSlot) :
    (CA2_6_8I2R2Raw a).Encloses (CA2_6_8I2R2Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA2_6_8I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(140902655070367662508780278177 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(925005669100461279977077150509 / 100000000000000000000000000000000), (82052573 / 25000000000000000000000000000000)⟩ ⟨(-656485620259254656553045040293771 / 100000000000000000000000000000000), (58233515483 / 25000000000000000000000000000000)⟩ ⟨-10, 140902655070367662508780278177, 97656250000000000000000000000⟩,
   .log ⟨(7411802901943689158823834801 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(130695353006720826070060753251 / 100000000000000000000000000000000), (43946299 / 100000000000000000000000000000000)⟩ ⟨(-88167045680914531536555617695763 / 10000000000000000000000000000000), (296461538307 / 100000000000000000000000000000000)⟩ ⟨-13, 7411802901943689158823834801, 6103515625000000000000000000⟩,
   .log ⟨(532161634655843941550587720409 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(2786386716461794114624242134321 / 100000000000000000000000000000000), (1014206523 / 100000000000000000000000000000000)⟩ ⟨(-523597819723285338506403296232279 / 100000000000000000000000000000000), (95291207137 / 50000000000000000000000000000000)⟩ ⟨-8, 532161634655843941550587720409, 390625000000000000000000000000⟩]
lemma CA2_6_8I2R2Certificates_valid :
    CA2_6_8I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA2_6_8I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R2Certificates (CA2_6_8I2R2CertificateIndex a)).input
lemma CA2_6_8I2R2P_check : ∀ a : PairSlot, contains (CA2_6_8I2R2Raw a) (CA2_6_8I2R2P a) = true := by
  decide +kernel
lemma CA2_6_8I2R2P_sound (a : PairSlot) :
    (CA2_6_8I2R2P a).Encloses (CA2_6_8I2R2Value a) :=
  contains_sound (CA2_6_8I2R2Raw_sound a) (CA2_6_8I2R2P_check a)
def CA2_6_8I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R2Certificates (CA2_6_8I2R2CertificateIndex a)).output
lemma CA2_6_8I2R2Terms_sound (a : PairSlot) :
    (CA2_6_8I2R2Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R2Certificates_valid
    (CA2_6_8I2R2CertificateIndex a) (CA2_6_8I2R2P_sound a)
def CA2_6_8I2R2Entropy : Ball := ⟨(4897788760676158326718517941841 / 100000000000000000000000000000000), (351703941 / 20000000000000000000000000000000)⟩
lemma CA2_6_8I2R2Entropy_sound : CA2_6_8I2R2Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R2Value CA2_6_8I2R2Terms CA2_6_8I2R2Terms_sound) (by decide +kernel)
def CA2_6_8I2R2Mass : Ball := ⟨(843614156404354023203443615967 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
lemma CA2_6_8I2R2Mass_sound : CA2_6_8I2R2Mass.Encloses (∑ a, CA2_6_8I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R2P CA2_6_8I2R2Value CA2_6_8I2R2P_sound) (by decide +kernel)
def CA2_6_8I2R2MassTermLogWitness : LogWitness := ⟨-7, 843614156404354023203443615967, 781250000000000000000000000000⟩
def CA2_6_8I2R2MassTermLog : Ball := ⟨(-238761511778120627163225134528117 / 50000000000000000000000000000000), (84703295443 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I2R2MassTermLog_sound : CA2_6_8I2R2MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I2R2Mass_sound) (w := CA2_6_8I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I2R2MassTerm : Ball := ⟨(4028451826810549400482286207711 / 100000000000000000000000000000000), (35728451 / 2500000000000000000000000000000)⟩
lemma CA2_6_8I2R2MassTerm_sound : CA2_6_8I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I2R2Mass_sound) CA2_6_8I2R2MassTermLog_sound) (by decide +kernel)
def CA2_6_8I2R2H : Ball := ⟨(86933693386560892623623173413 / 10000000000000000000000000000000), (637531549 / 20000000000000000000000000000000)⟩
lemma CA2_6_8I2R2H_sound : CA2_6_8I2R2H.Encloses (homogeneousEntropy CA2_6_8I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R2Value CA2_6_8I2R2MassTerm_sound CA2_6_8I2R2Entropy_sound) (by decide +kernel)
def CA2_6_8I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA2_6_8I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA2_6_8I2R3Raw_sound (a : PairSlot) :
    (CA2_6_8I2R3Raw a).Encloses (CA2_6_8I2R3Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA2_6_8I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(109251866670461195107544193847 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(669290303757123260959902370953 / 50000000000000000000000000000000), (18507987 / 4000000000000000000000000000000)⟩ ⟨(-612612236435207375937502711790713 / 100000000000000000000000000000000), (105879119101 / 50000000000000000000000000000000)⟩ ⟨-9, 109251866670461195107544193847, 97656250000000000000000000000⟩,
   .log ⟨(3807659390537154766739618738827 / 50000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩ ⟨(4902377339947084153189162392023 / 25000000000000000000000000000000), (4031516267 / 50000000000000000000000000000000)⟩ ⟨(-64375208456545993095555699119747 / 25000000000000000000000000000000), (105879118939 / 100000000000000000000000000000000)⟩ ⟨-4, 3807659390537154766739618738827, 3125000000000000000000000000000⟩,
   .log ⟨(102919505735096066747862988197 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(542338490079643639377028344313 / 20000000000000000000000000000000), (122591551 / 12500000000000000000000000000000)⟩ ⟨(-131738509188813442510258290379967 / 25000000000000000000000000000000), (190582413729 / 100000000000000000000000000000000)⟩ ⟨-8, 102919505735096066747862988197, 78125000000000000000000000000⟩]
lemma CA2_6_8I2R3Certificates_valid :
    CA2_6_8I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA2_6_8I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R3Certificates (CA2_6_8I2R3CertificateIndex a)).input
lemma CA2_6_8I2R3P_check : ∀ a : PairSlot, contains (CA2_6_8I2R3Raw a) (CA2_6_8I2R3P a) = true := by
  decide +kernel
lemma CA2_6_8I2R3P_sound (a : PairSlot) :
    (CA2_6_8I2R3P a).Encloses (CA2_6_8I2R3Value a) :=
  contains_sound (CA2_6_8I2R3Raw_sound a) (CA2_6_8I2R3P_check a)
def CA2_6_8I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R3Certificates (CA2_6_8I2R3CertificateIndex a)).output
lemma CA2_6_8I2R3Terms_sound (a : PairSlot) :
    (CA2_6_8I2R3Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R3Certificates_valid
    (CA2_6_8I2R3CertificateIndex a) (CA2_6_8I2R3P_sound a)
def CA2_6_8I2R3Entropy : Ball := ⟨(23659782417700801331561596031563 / 50000000000000000000000000000000), (9506464617 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I2R3Entropy_sound : CA2_6_8I2R3Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R3Value CA2_6_8I2R3Terms CA2_6_8I2R3Terms_sound) (by decide +kernel)
def CA2_6_8I2R3Mass : Ball := ⟨(8348420043090712257433640806333 / 50000000000000000000000000000000), (23 / 25000000000000000000000000000000)⟩
lemma CA2_6_8I2R3Mass_sound : CA2_6_8I2R3Mass.Encloses (∑ a, CA2_6_8I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R3P CA2_6_8I2R3Value CA2_6_8I2R3P_sound) (by decide +kernel)
def CA2_6_8I2R3MassTermLogWitness : LogWitness := ⟨-3, 8348420043090712257433640806333, 6250000000000000000000000000000⟩
def CA2_6_8I2R3MassTermLog : Ball := ⟨(-178995070086538463090810528272429 / 100000000000000000000000000000000), (42351647641 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I2R3MassTermLog_sound : CA2_6_8I2R3MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I2R3Mass_sound) (w := CA2_6_8I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I2R3MassTerm : Ball := ⟨(466976884601526405198369062241 / 1562500000000000000000000000000), (7071386963 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I2R3MassTerm_sound : CA2_6_8I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I2R3Mass_sound) CA2_6_8I2R3MassTermLog_sound) (by decide +kernel)
def CA2_6_8I2R3H : Ball := ⟨(8716522110451956365213786039851 / 50000000000000000000000000000000), (828892579 / 2500000000000000000000000000000)⟩
lemma CA2_6_8I2R3H_sound : CA2_6_8I2R3H.Encloses (homogeneousEntropy CA2_6_8I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R3Value CA2_6_8I2R3MassTerm_sound CA2_6_8I2R3Entropy_sound) (by decide +kernel)
def CA2_6_8I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA2_6_8I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA2_6_8I2R4Raw_sound (a : PairSlot) :
    (CA2_6_8I2R4Raw a).Encloses (CA2_6_8I2R4Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA2_6_8I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(9402550556286229819547189751 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(136218635464807180293186953 / 156250000000000000000000000000), (3733253 / 12500000000000000000000000000000)⟩ ⟨(-231798611918100832579068578755583 / 25000000000000000000000000000000), (7940934147 / 2500000000000000000000000000000)⟩ ⟨-14, 9402550556286229819547189751, 6103515625000000000000000000⟩,
   .log ⟨(3543223831892394318588980025187 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩ ⟨(5917419753680388482268673928137 / 50000000000000000000000000000000), (4501841071 / 100000000000000000000000000000000)⟩ ⟨(-334013318629095128304943817936191 / 100000000000000000000000000000000), (63527471317 / 50000000000000000000000000000000)⟩ ⟨-5, 3543223831892394318588980025187, 3125000000000000000000000000000⟩,
   .log ⟨(9354963093004439840323456078769 / 25000000000000000000000000000000), (31 / 25000000000000000000000000000000)⟩ ⟨(36782547768190548772561755222693 / 100000000000000000000000000000000), (23771886129 / 100000000000000000000000000000000)⟩ ⟨(-98296881031246982051345585706517 / 100000000000000000000000000000000), (3176373569 / 5000000000000000000000000000000)⟩ ⟨-2, 9354963093004439840323456078769, 6250000000000000000000000000000⟩,
   .log ⟨(910537380326362943907589992403 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(291790323135791516072672677853 / 4000000000000000000000000000000), (2699393099 / 100000000000000000000000000000000)⟩ ⟨(-400574333136116582577552350313507 / 100000000000000000000000000000000), (29646153233 / 20000000000000000000000000000000)⟩ ⟨-6, 910537380326362943907589992403, 781250000000000000000000000000⟩,
   .log ⟨(48812956184422649195326386733 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(14887814358139884453910235623 / 4000000000000000000000000000000), (13437511 / 10000000000000000000000000000000)⟩ ⟨(-95311621147080136281874359575383 / 12500000000000000000000000000000), (34410713997 / 12500000000000000000000000000000)⟩ ⟨-12, 48812956184422649195326386733, 24414062500000000000000000000⟩]
lemma CA2_6_8I2R4Certificates_valid :
    CA2_6_8I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA2_6_8I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R4Certificates (CA2_6_8I2R4CertificateIndex a)).input
lemma CA2_6_8I2R4P_check : ∀ a : PairSlot, contains (CA2_6_8I2R4Raw a) (CA2_6_8I2R4P a) = true := by
  decide +kernel
lemma CA2_6_8I2R4P_sound (a : PairSlot) :
    (CA2_6_8I2R4P a).Encloses (CA2_6_8I2R4Value a) :=
  contains_sound (CA2_6_8I2R4Raw_sound a) (CA2_6_8I2R4P_check a)
def CA2_6_8I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R4Certificates (CA2_6_8I2R4CertificateIndex a)).output
lemma CA2_6_8I2R4Terms_sound (a : PairSlot) :
    (CA2_6_8I2R4Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R4Certificates_valid
    (CA2_6_8I2R4CertificateIndex a) (CA2_6_8I2R4P_sound a)
def CA2_6_8I2R4Entropy : Ball := ⟨(37794149076025064403696560009153 / 50000000000000000000000000000000), (38368461627 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I2R4Entropy_sound : CA2_6_8I2R4Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R4Value CA2_6_8I2R4Terms CA2_6_8I2R4Terms_sound) (by decide +kernel)
def CA2_6_8I2R4Mass : Ball := ⟨(48216067614404994882936565101297 / 100000000000000000000000000000000), (9 / 5000000000000000000000000000000)⟩
lemma CA2_6_8I2R4Mass_sound : CA2_6_8I2R4Mass.Encloses (∑ a, CA2_6_8I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R4P CA2_6_8I2R4Value CA2_6_8I2R4P_sound) (by decide +kernel)
def CA2_6_8I2R4MassTermLogWitness : LogWitness := ⟨-2, 48216067614404994882936565101297, 25000000000000000000000000000000⟩
def CA2_6_8I2R4MassTermLog : Ball := ⟨(-72947786748534767477246031256031 / 100000000000000000000000000000000), (31763735711 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I2R4MassTermLog_sound : CA2_6_8I2R4MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I2R4Mass_sound) (w := CA2_6_8I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I2R4MassTerm : Ball := ⟨(8793138545471372611168418006667 / 25000000000000000000000000000000), (30630448707 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I2R4MassTerm_sound : CA2_6_8I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I2R4Mass_sound) CA2_6_8I2R4MassTermLog_sound) (by decide +kernel)
def CA2_6_8I2R4H : Ball := ⟨(20207871985082319181359723995819 / 50000000000000000000000000000000), (34499455167 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I2R4H_sound : CA2_6_8I2R4H.Encloses (homogeneousEntropy CA2_6_8I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R4Value CA2_6_8I2R4MassTerm_sound CA2_6_8I2R4Entropy_sound) (by decide +kernel)
def CA2_6_8I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA2_6_8I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA2_6_8I2R5Raw_sound (a : PairSlot) :
    (CA2_6_8I2R5Raw a).Encloses (CA2_6_8I2R5Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA2_6_8I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(6643687772735896558483231589 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(12781469707835433312533761123 / 20000000000000000000000000000000), (4220569 / 20000000000000000000000000000000)⟩ ⟨(-480962913409609787935296114153293 / 50000000000000000000000000000000), (39704671287 / 12500000000000000000000000000000)⟩ ⟨-14, 6643687772735896558483231589, 6103515625000000000000000000⟩,
   .log ⟨(4266470274952823916557576969017 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩ ⟨(13458082730735454483262644488643 / 100000000000000000000000000000000), (2710380721 / 50000000000000000000000000000000)⟩ ⟨(-157719166704897128747034779156421 / 50000000000000000000000000000000), (127054942683 / 100000000000000000000000000000000)⟩ ⟨-5, 4266470274952823916557576969017, 3125000000000000000000000000000⟩,
   .log ⟨(39540563691210857175174239547 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1020036467046040262648351935589 / 100000000000000000000000000000000), (184206889 / 50000000000000000000000000000000)⟩ ⟨(-644930402998260543013779698531911 / 100000000000000000000000000000000), (232934061777 / 100000000000000000000000000000000)⟩ ⟨-10, 39540563691210857175174239547, 24414062500000000000000000000⟩]
lemma CA2_6_8I2R5Certificates_valid :
    CA2_6_8I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA2_6_8I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R5Certificates (CA2_6_8I2R5CertificateIndex a)).input
lemma CA2_6_8I2R5P_check : ∀ a : PairSlot, contains (CA2_6_8I2R5Raw a) (CA2_6_8I2R5P a) = true := by
  decide +kernel
lemma CA2_6_8I2R5P_sound (a : PairSlot) :
    (CA2_6_8I2R5P a).Encloses (CA2_6_8I2R5Value a) :=
  contains_sound (CA2_6_8I2R5Raw_sound a) (CA2_6_8I2R5P_check a)
def CA2_6_8I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R5Certificates (CA2_6_8I2R5CertificateIndex a)).output
lemma CA2_6_8I2R5Terms_sound (a : PairSlot) :
    (CA2_6_8I2R5Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R5Certificates_valid
    (CA2_6_8I2R5CertificateIndex a) (CA2_6_8I2R5P_sound a)
def CA2_6_8I2R5Entropy : Ball := ⟨(14542026546320671912473665229847 / 50000000000000000000000000000000), (1162055613 / 10000000000000000000000000000000)⟩
lemma CA2_6_8I2R5Entropy_sound : CA2_6_8I2R5Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R5Value CA2_6_8I2R5Terms CA2_6_8I2R5Terms_sound) (by decide +kernel)
def CA2_6_8I2R5Mass : Ball := ⟨(2215638108745201620908378579397 / 25000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
lemma CA2_6_8I2R5Mass_sound : CA2_6_8I2R5Mass.Encloses (∑ a, CA2_6_8I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R5P CA2_6_8I2R5Value CA2_6_8I2R5P_sound) (by decide +kernel)
def CA2_6_8I2R5MassTermLogWitness : LogWitness := ⟨-4, 2215638108745201620908378579397, 1562500000000000000000000000000⟩
def CA2_6_8I2R5MassTermLog : Ball := ⟨(-242333537764739794209388441775203 / 100000000000000000000000000000000), (52939559523 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I2R5MassTermLog_sound : CA2_6_8I2R5MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I2R5Mass_sound) (w := CA2_6_8I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I2R5MassTerm : Ball := ⟨(21476936851944078875885785250807 / 100000000000000000000000000000000), (469179629 / 5000000000000000000000000000000)⟩
lemma CA2_6_8I2R5MassTerm_sound : CA2_6_8I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I2R5Mass_sound) CA2_6_8I2R5MassTermLog_sound) (by decide +kernel)
def CA2_6_8I2R5H : Ball := ⟨(7607116240697264949061545208887 / 100000000000000000000000000000000), (2100414871 / 10000000000000000000000000000000)⟩
lemma CA2_6_8I2R5H_sound : CA2_6_8I2R5H.Encloses (homogeneousEntropy CA2_6_8I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R5Value CA2_6_8I2R5MassTerm_sound CA2_6_8I2R5Entropy_sound) (by decide +kernel)
def CA2_6_8I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA2_6_8I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA2_6_8I2R6Raw_sound (a : PairSlot) :
    (CA2_6_8I2R6Raw a).Encloses (CA2_6_8I2R6Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA2_6_8I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1879330769378702376110481489 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(10225447854657892196457485831 / 50000000000000000000000000000000), (6765397 / 100000000000000000000000000000000)⟩ ⟨(-544100486261839664827794617986551 / 50000000000000000000000000000000), (359989055821 / 100000000000000000000000000000000)⟩ ⟨-16, 1879330769378702376110481489, 1525878906250000000000000000⟩,
   .log ⟨(59202649002316270772539 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(608435171846847114190571 / 25000000000000000000000000000000), (799 / 100000000000000000000000000000000)⟩ ⟨(-256929031935311891997869421170823 / 12500000000000000000000000000000), (20540471593 / 3125000000000000000000000000000)⟩ ⟨-30, 59202649002316270772539, 46566128730773925781250⟩,
   .log ⟨(98531741176814041209907022063 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1227587166855035938190084268841 / 100000000000000000000000000000000), (208649089 / 50000000000000000000000000000000)⟩ ⟨(-311469977134613231710011141363691 / 50000000000000000000000000000000), (211758238351 / 100000000000000000000000000000000)⟩ ⟨-9, 98531741176814041209907022063, 97656250000000000000000000000⟩]
lemma CA2_6_8I2R6Certificates_valid :
    CA2_6_8I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA2_6_8I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R6Certificates (CA2_6_8I2R6CertificateIndex a)).input
lemma CA2_6_8I2R6P_check : ∀ a : PairSlot, contains (CA2_6_8I2R6Raw a) (CA2_6_8I2R6P a) = true := by
  decide +kernel
lemma CA2_6_8I2R6P_sound (a : PairSlot) :
    (CA2_6_8I2R6P a).Encloses (CA2_6_8I2R6Value a) :=
  contains_sound (CA2_6_8I2R6Raw_sound a) (CA2_6_8I2R6P_check a)
def CA2_6_8I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R6Certificates (CA2_6_8I2R6CertificateIndex a)).output
lemma CA2_6_8I2R6Terms_sound (a : PairSlot) :
    (CA2_6_8I2R6Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R6Certificates_valid
    (CA2_6_8I2R6CertificateIndex a) (CA2_6_8I2R6P_sound a)
def CA2_6_8I2R6Entropy : Ball := ⟨(1268493825755042281752827736733 / 100000000000000000000000000000000), (43083057 / 10000000000000000000000000000000)⟩
lemma CA2_6_8I2R6Entropy_sound : CA2_6_8I2R6Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R6Value CA2_6_8I2R6Terms CA2_6_8I2R6Terms_sound) (by decide +kernel)
def CA2_6_8I2R6Mass : Ball := ⟨(10041119035149074821855904863 / 5000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I2R6Mass_sound : CA2_6_8I2R6Mass.Encloses (∑ a, CA2_6_8I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R6P CA2_6_8I2R6Value CA2_6_8I2R6P_sound) (by decide +kernel)
def CA2_6_8I2R6MassTermLogWitness : LogWitness := ⟨-9, 10041119035149074821855904863, 9765625000000000000000000000⟩
def CA2_6_8I2R6MassTermLog : Ball := ⟨(-155262615641985741754365944816713 / 25000000000000000000000000000000), (42351648063 / 20000000000000000000000000000000)⟩
lemma CA2_6_8I2R6MassTermLog_sound : CA2_6_8I2R6MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I2R6Mass_sound) (w := CA2_6_8I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I2R6MassTerm : Ball := ⟨(1247208324295822018796855228129 / 100000000000000000000000000000000), (415291 / 97656250000000000000000000000)⟩
lemma CA2_6_8I2R6MassTerm_sound : CA2_6_8I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I2R6Mass_sound) CA2_6_8I2R6MassTermLog_sound) (by decide +kernel)
def CA2_6_8I2R6H : Ball := ⟨(5321375364805065738993127151 / 25000000000000000000000000000000), (428044277 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I2R6H_sound : CA2_6_8I2R6H.Encloses (homogeneousEntropy CA2_6_8I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R6Value CA2_6_8I2R6MassTerm_sound CA2_6_8I2R6Entropy_sound) (by decide +kernel)
def CA2_6_8I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA2_6_8I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA2_6_8I2R7Raw_sound (a : PairSlot) :
    (CA2_6_8I2R7Raw a).Encloses (CA2_6_8I2R7Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA2_6_8I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I2R7Certificates_valid :
    CA2_6_8I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R7Certificates (CA2_6_8I2R7CertificateIndex a)).input
lemma CA2_6_8I2R7P_check : ∀ a : PairSlot, contains (CA2_6_8I2R7Raw a) (CA2_6_8I2R7P a) = true := by
  decide +kernel
lemma CA2_6_8I2R7P_sound (a : PairSlot) :
    (CA2_6_8I2R7P a).Encloses (CA2_6_8I2R7Value a) :=
  contains_sound (CA2_6_8I2R7Raw_sound a) (CA2_6_8I2R7P_check a)
def CA2_6_8I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R7Certificates (CA2_6_8I2R7CertificateIndex a)).output
lemma CA2_6_8I2R7Terms_sound (a : PairSlot) :
    (CA2_6_8I2R7Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R7Certificates_valid
    (CA2_6_8I2R7CertificateIndex a) (CA2_6_8I2R7P_sound a)
def CA2_6_8I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R7Entropy_sound : CA2_6_8I2R7Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R7Value CA2_6_8I2R7Terms CA2_6_8I2R7Terms_sound) (by decide +kernel)
def CA2_6_8I2R7Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R7Mass_sound : CA2_6_8I2R7Mass.Encloses (∑ a, CA2_6_8I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R7P CA2_6_8I2R7Value CA2_6_8I2R7P_sound) (by decide +kernel)
def CA2_6_8I2R7MassTerm : Ball := .exact 0
lemma CA2_6_8I2R7MassTerm_sound : CA2_6_8I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R7Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I2R7Mass_sound)
def CA2_6_8I2R7H : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R7H_sound : CA2_6_8I2R7H.Encloses (homogeneousEntropy CA2_6_8I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R7Value CA2_6_8I2R7MassTerm_sound CA2_6_8I2R7Entropy_sound) (by decide +kernel)
def CA2_6_8I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA2_6_8I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA2_6_8I2R8Raw_sound (a : PairSlot) :
    (CA2_6_8I2R8Raw a).Encloses (CA2_6_8I2R8Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA2_6_8I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I2R8Certificates_valid :
    CA2_6_8I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R8Certificates (CA2_6_8I2R8CertificateIndex a)).input
lemma CA2_6_8I2R8P_check : ∀ a : PairSlot, contains (CA2_6_8I2R8Raw a) (CA2_6_8I2R8P a) = true := by
  decide +kernel
lemma CA2_6_8I2R8P_sound (a : PairSlot) :
    (CA2_6_8I2R8P a).Encloses (CA2_6_8I2R8Value a) :=
  contains_sound (CA2_6_8I2R8Raw_sound a) (CA2_6_8I2R8P_check a)
def CA2_6_8I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R8Certificates (CA2_6_8I2R8CertificateIndex a)).output
lemma CA2_6_8I2R8Terms_sound (a : PairSlot) :
    (CA2_6_8I2R8Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R8Certificates_valid
    (CA2_6_8I2R8CertificateIndex a) (CA2_6_8I2R8P_sound a)
def CA2_6_8I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R8Entropy_sound : CA2_6_8I2R8Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R8Value CA2_6_8I2R8Terms CA2_6_8I2R8Terms_sound) (by decide +kernel)
def CA2_6_8I2R8Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R8Mass_sound : CA2_6_8I2R8Mass.Encloses (∑ a, CA2_6_8I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R8P CA2_6_8I2R8Value CA2_6_8I2R8P_sound) (by decide +kernel)
def CA2_6_8I2R8MassTerm : Ball := .exact 0
lemma CA2_6_8I2R8MassTerm_sound : CA2_6_8I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R8Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I2R8Mass_sound)
def CA2_6_8I2R8H : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R8H_sound : CA2_6_8I2R8H.Encloses (homogeneousEntropy CA2_6_8I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R8Value CA2_6_8I2R8MassTerm_sound CA2_6_8I2R8Entropy_sound) (by decide +kernel)
def CA2_6_8I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA2_6_8I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA2_6_8I2R9Raw_sound (a : PairSlot) :
    (CA2_6_8I2R9Raw a).Encloses (CA2_6_8I2R9Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA2_6_8I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I2R9Certificates_valid :
    CA2_6_8I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R9Certificates (CA2_6_8I2R9CertificateIndex a)).input
lemma CA2_6_8I2R9P_check : ∀ a : PairSlot, contains (CA2_6_8I2R9Raw a) (CA2_6_8I2R9P a) = true := by
  decide +kernel
lemma CA2_6_8I2R9P_sound (a : PairSlot) :
    (CA2_6_8I2R9P a).Encloses (CA2_6_8I2R9Value a) :=
  contains_sound (CA2_6_8I2R9Raw_sound a) (CA2_6_8I2R9P_check a)
def CA2_6_8I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R9Certificates (CA2_6_8I2R9CertificateIndex a)).output
lemma CA2_6_8I2R9Terms_sound (a : PairSlot) :
    (CA2_6_8I2R9Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R9Certificates_valid
    (CA2_6_8I2R9CertificateIndex a) (CA2_6_8I2R9P_sound a)
def CA2_6_8I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R9Entropy_sound : CA2_6_8I2R9Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R9Value CA2_6_8I2R9Terms CA2_6_8I2R9Terms_sound) (by decide +kernel)
def CA2_6_8I2R9Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R9Mass_sound : CA2_6_8I2R9Mass.Encloses (∑ a, CA2_6_8I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R9P CA2_6_8I2R9Value CA2_6_8I2R9P_sound) (by decide +kernel)
def CA2_6_8I2R9MassTerm : Ball := .exact 0
lemma CA2_6_8I2R9MassTerm_sound : CA2_6_8I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R9Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I2R9Mass_sound)
def CA2_6_8I2R9H : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R9H_sound : CA2_6_8I2R9H.Encloses (homogeneousEntropy CA2_6_8I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R9Value CA2_6_8I2R9MassTerm_sound CA2_6_8I2R9Entropy_sound) (by decide +kernel)
def CA2_6_8I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA2_6_8I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA2_6_8I2R10Raw_sound (a : PairSlot) :
    (CA2_6_8I2R10Raw a).Encloses (CA2_6_8I2R10Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA2_6_8I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I2R10Certificates_valid :
    CA2_6_8I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R10Certificates (CA2_6_8I2R10CertificateIndex a)).input
lemma CA2_6_8I2R10P_check : ∀ a : PairSlot, contains (CA2_6_8I2R10Raw a) (CA2_6_8I2R10P a) = true := by
  decide +kernel
lemma CA2_6_8I2R10P_sound (a : PairSlot) :
    (CA2_6_8I2R10P a).Encloses (CA2_6_8I2R10Value a) :=
  contains_sound (CA2_6_8I2R10Raw_sound a) (CA2_6_8I2R10P_check a)
def CA2_6_8I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R10Certificates (CA2_6_8I2R10CertificateIndex a)).output
lemma CA2_6_8I2R10Terms_sound (a : PairSlot) :
    (CA2_6_8I2R10Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R10Certificates_valid
    (CA2_6_8I2R10CertificateIndex a) (CA2_6_8I2R10P_sound a)
def CA2_6_8I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R10Entropy_sound : CA2_6_8I2R10Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R10Value CA2_6_8I2R10Terms CA2_6_8I2R10Terms_sound) (by decide +kernel)
def CA2_6_8I2R10Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R10Mass_sound : CA2_6_8I2R10Mass.Encloses (∑ a, CA2_6_8I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R10P CA2_6_8I2R10Value CA2_6_8I2R10P_sound) (by decide +kernel)
def CA2_6_8I2R10MassTerm : Ball := .exact 0
lemma CA2_6_8I2R10MassTerm_sound : CA2_6_8I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R10Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I2R10Mass_sound)
def CA2_6_8I2R10H : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R10H_sound : CA2_6_8I2R10H.Encloses (homogeneousEntropy CA2_6_8I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R10Value CA2_6_8I2R10MassTerm_sound CA2_6_8I2R10Entropy_sound) (by decide +kernel)
def CA2_6_8I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA2_6_8I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA2_6_8I2R11Raw_sound (a : PairSlot) :
    (CA2_6_8I2R11Raw a).Encloses (CA2_6_8I2R11Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA2_6_8I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I2R11Certificates_valid :
    CA2_6_8I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R11Certificates (CA2_6_8I2R11CertificateIndex a)).input
lemma CA2_6_8I2R11P_check : ∀ a : PairSlot, contains (CA2_6_8I2R11Raw a) (CA2_6_8I2R11P a) = true := by
  decide +kernel
lemma CA2_6_8I2R11P_sound (a : PairSlot) :
    (CA2_6_8I2R11P a).Encloses (CA2_6_8I2R11Value a) :=
  contains_sound (CA2_6_8I2R11Raw_sound a) (CA2_6_8I2R11P_check a)
def CA2_6_8I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R11Certificates (CA2_6_8I2R11CertificateIndex a)).output
lemma CA2_6_8I2R11Terms_sound (a : PairSlot) :
    (CA2_6_8I2R11Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R11Certificates_valid
    (CA2_6_8I2R11CertificateIndex a) (CA2_6_8I2R11P_sound a)
def CA2_6_8I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R11Entropy_sound : CA2_6_8I2R11Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R11Value CA2_6_8I2R11Terms CA2_6_8I2R11Terms_sound) (by decide +kernel)
def CA2_6_8I2R11Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R11Mass_sound : CA2_6_8I2R11Mass.Encloses (∑ a, CA2_6_8I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R11P CA2_6_8I2R11Value CA2_6_8I2R11P_sound) (by decide +kernel)
def CA2_6_8I2R11MassTerm : Ball := .exact 0
lemma CA2_6_8I2R11MassTerm_sound : CA2_6_8I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R11Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I2R11Mass_sound)
def CA2_6_8I2R11H : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R11H_sound : CA2_6_8I2R11H.Encloses (homogeneousEntropy CA2_6_8I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R11Value CA2_6_8I2R11MassTerm_sound CA2_6_8I2R11Entropy_sound) (by decide +kernel)
def CA2_6_8I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA2_6_8I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA2_6_8I2R12Raw_sound (a : PairSlot) :
    (CA2_6_8I2R12Raw a).Encloses (CA2_6_8I2R12Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA2_6_8I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I2R12Certificates_valid :
    CA2_6_8I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R12Certificates (CA2_6_8I2R12CertificateIndex a)).input
lemma CA2_6_8I2R12P_check : ∀ a : PairSlot, contains (CA2_6_8I2R12Raw a) (CA2_6_8I2R12P a) = true := by
  decide +kernel
lemma CA2_6_8I2R12P_sound (a : PairSlot) :
    (CA2_6_8I2R12P a).Encloses (CA2_6_8I2R12Value a) :=
  contains_sound (CA2_6_8I2R12Raw_sound a) (CA2_6_8I2R12P_check a)
def CA2_6_8I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R12Certificates (CA2_6_8I2R12CertificateIndex a)).output
lemma CA2_6_8I2R12Terms_sound (a : PairSlot) :
    (CA2_6_8I2R12Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R12Certificates_valid
    (CA2_6_8I2R12CertificateIndex a) (CA2_6_8I2R12P_sound a)
def CA2_6_8I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R12Entropy_sound : CA2_6_8I2R12Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R12Value CA2_6_8I2R12Terms CA2_6_8I2R12Terms_sound) (by decide +kernel)
def CA2_6_8I2R12Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R12Mass_sound : CA2_6_8I2R12Mass.Encloses (∑ a, CA2_6_8I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R12P CA2_6_8I2R12Value CA2_6_8I2R12P_sound) (by decide +kernel)
def CA2_6_8I2R12MassTerm : Ball := .exact 0
lemma CA2_6_8I2R12MassTerm_sound : CA2_6_8I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R12Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I2R12Mass_sound)
def CA2_6_8I2R12H : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R12H_sound : CA2_6_8I2R12H.Encloses (homogeneousEntropy CA2_6_8I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R12Value CA2_6_8I2R12MassTerm_sound CA2_6_8I2R12Entropy_sound) (by decide +kernel)
def CA2_6_8I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA2_6_8I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA2_6_8I2R13Raw_sound (a : PairSlot) :
    (CA2_6_8I2R13Raw a).Encloses (CA2_6_8I2R13Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA2_6_8I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I2R13Certificates_valid :
    CA2_6_8I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R13Certificates (CA2_6_8I2R13CertificateIndex a)).input
lemma CA2_6_8I2R13P_check : ∀ a : PairSlot, contains (CA2_6_8I2R13Raw a) (CA2_6_8I2R13P a) = true := by
  decide +kernel
lemma CA2_6_8I2R13P_sound (a : PairSlot) :
    (CA2_6_8I2R13P a).Encloses (CA2_6_8I2R13Value a) :=
  contains_sound (CA2_6_8I2R13Raw_sound a) (CA2_6_8I2R13P_check a)
def CA2_6_8I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R13Certificates (CA2_6_8I2R13CertificateIndex a)).output
lemma CA2_6_8I2R13Terms_sound (a : PairSlot) :
    (CA2_6_8I2R13Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R13Certificates_valid
    (CA2_6_8I2R13CertificateIndex a) (CA2_6_8I2R13P_sound a)
def CA2_6_8I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R13Entropy_sound : CA2_6_8I2R13Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R13Value CA2_6_8I2R13Terms CA2_6_8I2R13Terms_sound) (by decide +kernel)
def CA2_6_8I2R13Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R13Mass_sound : CA2_6_8I2R13Mass.Encloses (∑ a, CA2_6_8I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R13P CA2_6_8I2R13Value CA2_6_8I2R13P_sound) (by decide +kernel)
def CA2_6_8I2R13MassTerm : Ball := .exact 0
lemma CA2_6_8I2R13MassTerm_sound : CA2_6_8I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R13Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I2R13Mass_sound)
def CA2_6_8I2R13H : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R13H_sound : CA2_6_8I2R13H.Encloses (homogeneousEntropy CA2_6_8I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R13Value CA2_6_8I2R13MassTerm_sound CA2_6_8I2R13Entropy_sound) (by decide +kernel)
def CA2_6_8I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA2_6_8I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA2_6_8I2R14Raw_sound (a : PairSlot) :
    (CA2_6_8I2R14Raw a).Encloses (CA2_6_8I2R14Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA2_6_8I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I2R14Certificates_valid :
    CA2_6_8I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R14Certificates (CA2_6_8I2R14CertificateIndex a)).input
lemma CA2_6_8I2R14P_check : ∀ a : PairSlot, contains (CA2_6_8I2R14Raw a) (CA2_6_8I2R14P a) = true := by
  decide +kernel
lemma CA2_6_8I2R14P_sound (a : PairSlot) :
    (CA2_6_8I2R14P a).Encloses (CA2_6_8I2R14Value a) :=
  contains_sound (CA2_6_8I2R14Raw_sound a) (CA2_6_8I2R14P_check a)
def CA2_6_8I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R14Certificates (CA2_6_8I2R14CertificateIndex a)).output
lemma CA2_6_8I2R14Terms_sound (a : PairSlot) :
    (CA2_6_8I2R14Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R14Certificates_valid
    (CA2_6_8I2R14CertificateIndex a) (CA2_6_8I2R14P_sound a)
def CA2_6_8I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R14Entropy_sound : CA2_6_8I2R14Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R14Value CA2_6_8I2R14Terms CA2_6_8I2R14Terms_sound) (by decide +kernel)
def CA2_6_8I2R14Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R14Mass_sound : CA2_6_8I2R14Mass.Encloses (∑ a, CA2_6_8I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R14P CA2_6_8I2R14Value CA2_6_8I2R14P_sound) (by decide +kernel)
def CA2_6_8I2R14MassTerm : Ball := .exact 0
lemma CA2_6_8I2R14MassTerm_sound : CA2_6_8I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R14Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I2R14Mass_sound)
def CA2_6_8I2R14H : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R14H_sound : CA2_6_8I2R14H.Encloses (homogeneousEntropy CA2_6_8I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R14Value CA2_6_8I2R14MassTerm_sound CA2_6_8I2R14Entropy_sound) (by decide +kernel)
def CA2_6_8I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA2_6_8I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA2_6_8I2R15Raw_sound (a : PairSlot) :
    (CA2_6_8I2R15Raw a).Encloses (CA2_6_8I2R15Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA2_6_8I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I2R15Certificates_valid :
    CA2_6_8I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R15Certificates (CA2_6_8I2R15CertificateIndex a)).input
lemma CA2_6_8I2R15P_check : ∀ a : PairSlot, contains (CA2_6_8I2R15Raw a) (CA2_6_8I2R15P a) = true := by
  decide +kernel
lemma CA2_6_8I2R15P_sound (a : PairSlot) :
    (CA2_6_8I2R15P a).Encloses (CA2_6_8I2R15Value a) :=
  contains_sound (CA2_6_8I2R15Raw_sound a) (CA2_6_8I2R15P_check a)
def CA2_6_8I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R15Certificates (CA2_6_8I2R15CertificateIndex a)).output
lemma CA2_6_8I2R15Terms_sound (a : PairSlot) :
    (CA2_6_8I2R15Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R15Certificates_valid
    (CA2_6_8I2R15CertificateIndex a) (CA2_6_8I2R15P_sound a)
def CA2_6_8I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R15Entropy_sound : CA2_6_8I2R15Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R15Value CA2_6_8I2R15Terms CA2_6_8I2R15Terms_sound) (by decide +kernel)
def CA2_6_8I2R15Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R15Mass_sound : CA2_6_8I2R15Mass.Encloses (∑ a, CA2_6_8I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R15P CA2_6_8I2R15Value CA2_6_8I2R15P_sound) (by decide +kernel)
def CA2_6_8I2R15MassTerm : Ball := .exact 0
lemma CA2_6_8I2R15MassTerm_sound : CA2_6_8I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R15Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I2R15Mass_sound)
def CA2_6_8I2R15H : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R15H_sound : CA2_6_8I2R15H.Encloses (homogeneousEntropy CA2_6_8I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R15Value CA2_6_8I2R15MassTerm_sound CA2_6_8I2R15Entropy_sound) (by decide +kernel)
def CA2_6_8I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA2_6_8I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA2_6_8I2R16Raw_sound (a : PairSlot) :
    (CA2_6_8I2R16Raw a).Encloses (CA2_6_8I2R16Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA2_6_8I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I2R16Certificates_valid :
    CA2_6_8I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R16Certificates (CA2_6_8I2R16CertificateIndex a)).input
lemma CA2_6_8I2R16P_check : ∀ a : PairSlot, contains (CA2_6_8I2R16Raw a) (CA2_6_8I2R16P a) = true := by
  decide +kernel
lemma CA2_6_8I2R16P_sound (a : PairSlot) :
    (CA2_6_8I2R16P a).Encloses (CA2_6_8I2R16Value a) :=
  contains_sound (CA2_6_8I2R16Raw_sound a) (CA2_6_8I2R16P_check a)
def CA2_6_8I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I2R16Certificates (CA2_6_8I2R16CertificateIndex a)).output
lemma CA2_6_8I2R16Terms_sound (a : PairSlot) :
    (CA2_6_8I2R16Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I2R16Certificates_valid
    (CA2_6_8I2R16CertificateIndex a) (CA2_6_8I2R16P_sound a)
def CA2_6_8I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R16Entropy_sound : CA2_6_8I2R16Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I2R16Value CA2_6_8I2R16Terms CA2_6_8I2R16Terms_sound) (by decide +kernel)
def CA2_6_8I2R16Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R16Mass_sound : CA2_6_8I2R16Mass.Encloses (∑ a, CA2_6_8I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I2R16P CA2_6_8I2R16Value CA2_6_8I2R16P_sound) (by decide +kernel)
def CA2_6_8I2R16MassTerm : Ball := .exact 0
lemma CA2_6_8I2R16MassTerm_sound : CA2_6_8I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I2R16Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I2R16Mass_sound)
def CA2_6_8I2R16H : Ball := ⟨0, 0⟩
lemma CA2_6_8I2R16H_sound : CA2_6_8I2R16H.Encloses (homogeneousEntropy CA2_6_8I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I2R16Value CA2_6_8I2R16MassTerm_sound CA2_6_8I2R16Entropy_sound) (by decide +kernel)
def CA2_6_8I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_6_8I2R0H
  | 1 => CA2_6_8I2R1H
  | 2 => CA2_6_8I2R2H
  | 3 => CA2_6_8I2R3H
  | 4 => CA2_6_8I2R4H
  | 5 => CA2_6_8I2R5H
  | 6 => CA2_6_8I2R6H
  | 7 => CA2_6_8I2R7H
  | 8 => CA2_6_8I2R8H
  | 9 => CA2_6_8I2R9H
  | 10 => CA2_6_8I2R10H
  | 11 => CA2_6_8I2R11H
  | 12 => CA2_6_8I2R12H
  | 13 => CA2_6_8I2R13H
  | 14 => CA2_6_8I2R14H
  | 15 => CA2_6_8I2R15H
  | 16 => CA2_6_8I2R16H
  | _ => (.exact 0)
lemma CA2_6_8I2ResidualEntropies_sound (k : Fin 17) :
    (CA2_6_8I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_6_8I2R0H_sound
  · exact CA2_6_8I2R1H_sound
  · exact CA2_6_8I2R2H_sound
  · exact CA2_6_8I2R3H_sound
  · exact CA2_6_8I2R4H_sound
  · exact CA2_6_8I2R5H_sound
  · exact CA2_6_8I2R6H_sound
  · exact CA2_6_8I2R7H_sound
  · exact CA2_6_8I2R8H_sound
  · exact CA2_6_8I2R9H_sound
  · exact CA2_6_8I2R10H_sound
  · exact CA2_6_8I2R11H_sound
  · exact CA2_6_8I2R12H_sound
  · exact CA2_6_8I2R13H_sound
  · exact CA2_6_8I2R14H_sound
  · exact CA2_6_8I2R15H_sound
  · exact CA2_6_8I2R16H_sound
def CA2_6_8I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 0, 6, 2 => Z0_6_2H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | _, _, _ => (.exact 0)
lemma CA2_6_8I2Singles_sound (u : Shape) (hu : u ∈ below (shape 2 6 8))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA2_6_8I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A2_6_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z0_5_3H2H_sound
  · exact Z0_6_2H2H_sound
  · exact Z1_0_7H2H_sound
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
def CA2_6_8I2Singleton : Ball := ⟨(15172583866467906805800478596961 / 50000000000000000000000000000000), (25355929183 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I2Singleton_sound : CA2_6_8I2Singleton.Encloses
    (singletonEntropy (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA2_6_8I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_6_8Law_sound u) CA2_6_8I2Singles_sound) (by decide +kernel)
def CA2_6_8I2Group : Ball := ⟨(9669618760717564072244334628689 / 10000000000000000000000000000000), (152601066307 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I2Group_sound : CA2_6_8I2Group.Encloses
    (groupedEntropy (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_6_8I2Singleton_sound
    (finSumBall_sound 17 CA2_6_8I2ResidualEntropies _ CA2_6_8I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA2_6_8I2H : Ball := ⟨(25438310392363462550988190426307 / 25000000000000000000000000000000), (466388455693 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I2_sound : CA2_6_8I2H.Encloses (stageACapacity (shape 2 6 8) 2) := by
  have hb := contains_sound (Ball.add_sound CA2_6_8I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA2_6_8I2Group_sound)))
    (show contains (.add CA2_6_8I2PairH (.neg (.mul (.exact 2) CA2_6_8I2Group))) CA2_6_8I2H = true by decide +kernel)
  unfold CA2_6_8I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
