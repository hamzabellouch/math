import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA2_5_9I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_5_9I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA2_5_9I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA2_5_9I2R0Raw_sound (a : PairSlot) :
    (CA2_5_9I2R0Raw a).Encloses (CA2_5_9I2R0Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA2_5_9I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I2R0Certificates_valid :
    CA2_5_9I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R0Certificates (CA2_5_9I2R0CertificateIndex a)).input
lemma CA2_5_9I2R0P_check : ∀ a : PairSlot, contains (CA2_5_9I2R0Raw a) (CA2_5_9I2R0P a) = true := by
  decide +kernel
lemma CA2_5_9I2R0P_sound (a : PairSlot) :
    (CA2_5_9I2R0P a).Encloses (CA2_5_9I2R0Value a) :=
  contains_sound (CA2_5_9I2R0Raw_sound a) (CA2_5_9I2R0P_check a)
def CA2_5_9I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R0Certificates (CA2_5_9I2R0CertificateIndex a)).output
lemma CA2_5_9I2R0Terms_sound (a : PairSlot) :
    (CA2_5_9I2R0Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R0Certificates_valid
    (CA2_5_9I2R0CertificateIndex a) (CA2_5_9I2R0P_sound a)
def CA2_5_9I2R0Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R0Entropy_sound : CA2_5_9I2R0Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R0Value CA2_5_9I2R0Terms CA2_5_9I2R0Terms_sound) (by decide +kernel)
def CA2_5_9I2R0Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R0Mass_sound : CA2_5_9I2R0Mass.Encloses (∑ a, CA2_5_9I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R0P CA2_5_9I2R0Value CA2_5_9I2R0P_sound) (by decide +kernel)
def CA2_5_9I2R0MassTerm : Ball := .exact 0
lemma CA2_5_9I2R0MassTerm_sound : CA2_5_9I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R0Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I2R0Mass_sound)
def CA2_5_9I2R0H : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R0H_sound : CA2_5_9I2R0H.Encloses (homogeneousEntropy CA2_5_9I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R0Value CA2_5_9I2R0MassTerm_sound CA2_5_9I2R0Entropy_sound) (by decide +kernel)
def CA2_5_9I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA2_5_9I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA2_5_9I2R1Raw_sound (a : PairSlot) :
    (CA2_5_9I2R1Raw a).Encloses (CA2_5_9I2R1Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA2_5_9I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(15446294267654093658823153 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(44167187154123555521479247 / 5000000000000000000000000000000), (287869 / 100000000000000000000000000000000)⟩ ⟨(-1429701726148437809485208500868057 / 100000000000000000000000000000000), (14558479939 / 3125000000000000000000000000000)⟩ ⟨-21, 15446294267654093658823153, 11920928955078125000000000⟩]
lemma CA2_5_9I2R1Certificates_valid :
    CA2_5_9I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA2_5_9I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R1Certificates (CA2_5_9I2R1CertificateIndex a)).input
lemma CA2_5_9I2R1P_check : ∀ a : PairSlot, contains (CA2_5_9I2R1Raw a) (CA2_5_9I2R1P a) = true := by
  decide +kernel
lemma CA2_5_9I2R1P_sound (a : PairSlot) :
    (CA2_5_9I2R1P a).Encloses (CA2_5_9I2R1Value a) :=
  contains_sound (CA2_5_9I2R1Raw_sound a) (CA2_5_9I2R1P_check a)
def CA2_5_9I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R1Certificates (CA2_5_9I2R1CertificateIndex a)).output
lemma CA2_5_9I2R1Terms_sound (a : PairSlot) :
    (CA2_5_9I2R1Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R1Certificates_valid
    (CA2_5_9I2R1CertificateIndex a) (CA2_5_9I2R1P_sound a)
def CA2_5_9I2R1Entropy : Ball := ⟨(44167187154123555521479247 / 2500000000000000000000000000000), (287869 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I2R1Entropy_sound : CA2_5_9I2R1Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R1Value CA2_5_9I2R1Terms CA2_5_9I2R1Terms_sound) (by decide +kernel)
def CA2_5_9I2R1Mass : Ball := ⟨(15446294267654093658823153 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I2R1Mass_sound : CA2_5_9I2R1Mass.Encloses (∑ a, CA2_5_9I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R1P CA2_5_9I2R1Value CA2_5_9I2R1P_sound) (by decide +kernel)
def CA2_5_9I2R1MassTermLogWitness : LogWitness := ⟨-20, 15446294267654093658823153, 11920928955078125000000000⟩
def CA2_5_9I2R1MassTermLog : Ball := ⟨(-1360387008092443278543485307817727 / 100000000000000000000000000000000), (88939106873 / 20000000000000000000000000000000)⟩
lemma CA2_5_9I2R1MassTermLog_sound : CA2_5_9I2R1MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I2R1Mass_sound) (w := CA2_5_9I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I2R1MassTerm : Ball := ⟨(67241401743646111151768287 / 4000000000000000000000000000000), (549567 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2R1MassTerm_sound : CA2_5_9I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I2R1Mass_sound) CA2_5_9I2R1MassTermLog_sound) (by decide +kernel)
def CA2_5_9I2R1H : Ball := ⟨(17130488514757888412992541 / 20000000000000000000000000000000), (225061 / 20000000000000000000000000000000)⟩
lemma CA2_5_9I2R1H_sound : CA2_5_9I2R1H.Encloses (homogeneousEntropy CA2_5_9I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R1Value CA2_5_9I2R1MassTerm_sound CA2_5_9I2R1Entropy_sound) (by decide +kernel)
def CA2_5_9I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA2_5_9I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA2_5_9I2R2Raw_sound (a : PairSlot) :
    (CA2_5_9I2R2Raw a).Encloses (CA2_5_9I2R2Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA2_5_9I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(13448325190745958237288110239 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(119879324072629199536564734163 / 100000000000000000000000000000000), (19934561 / 50000000000000000000000000000000)⟩ ⟨(-178281417756198197539321688437499 / 20000000000000000000000000000000), (296461538997 / 100000000000000000000000000000000)⟩ ⟨-13, 13448325190745958237288110239, 12207031250000000000000000000⟩,
   .log ⟨(282323780452652185071222811 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(15765225654074667926548964821 / 100000000000000000000000000000000), (10509 / 195312500000000000000000000000)⟩ ⟨(-1116818826157551717896683661857721 / 100000000000000000000000000000000), (190582448567 / 50000000000000000000000000000000)⟩ ⟨-17, 282323780452652185071222811, 152587890625000000000000000⟩,
   .log ⟨(50783447597251899709700684141 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(385210478056688646600278217389 / 100000000000000000000000000000000), (64522889 / 50000000000000000000000000000000)⟩ ⟨(-758535499818121767047583016378033 / 100000000000000000000000000000000), (254109888133 / 100000000000000000000000000000000)⟩ ⟨-11, 50783447597251899709700684141, 48828125000000000000000000000⟩]
lemma CA2_5_9I2R2Certificates_valid :
    CA2_5_9I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA2_5_9I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R2Certificates (CA2_5_9I2R2CertificateIndex a)).input
lemma CA2_5_9I2R2P_check : ∀ a : PairSlot, contains (CA2_5_9I2R2Raw a) (CA2_5_9I2R2P a) = true := by
  decide +kernel
lemma CA2_5_9I2R2P_sound (a : PairSlot) :
    (CA2_5_9I2R2P a).Encloses (CA2_5_9I2R2Value a) :=
  contains_sound (CA2_5_9I2R2Raw_sound a) (CA2_5_9I2R2P_check a)
def CA2_5_9I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R2Certificates (CA2_5_9I2R2CertificateIndex a)).output
lemma CA2_5_9I2R2Terms_sound (a : PairSlot) :
    (CA2_5_9I2R2Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R2Certificates_valid
    (CA2_5_9I2R2CertificateIndex a) (CA2_5_9I2R2P_sound a)
def CA2_5_9I2R2Entropy : Ball := ⟨(656499577510096381526505615357 / 100000000000000000000000000000000), (109772619 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I2R2Entropy_sound : CA2_5_9I2R2Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R2Value CA2_5_9I2R2Terms CA2_5_9I2R2Terms_sound) (by decide +kernel)
def CA2_5_9I2R2Mass : Ball := ⟨(80503335783270338034989132729 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I2R2Mass_sound : CA2_5_9I2R2Mass.Encloses (∑ a, CA2_5_9I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R2P CA2_5_9I2R2Value CA2_5_9I2R2P_sound) (by decide +kernel)
def CA2_5_9I2R2MassTermLogWitness : LogWitness := ⟨-11, 80503335783270338034989132729, 48828125000000000000000000000⟩
def CA2_5_9I2R2MassTermLog : Ball := ⟨(-14249253686205517097888745662231 / 2000000000000000000000000000000), (254109891649 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2R2MassTermLog_sound : CA2_5_9I2R2MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I2R2Mass_sound) (w := CA2_5_9I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I2R2MassTerm : Ball := ⟨(57355622708080268666003791401 / 10000000000000000000000000000000), (204566983 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2R2MassTerm_sound : CA2_5_9I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I2R2Mass_sound) CA2_5_9I2R2MassTermLog_sound) (by decide +kernel)
def CA2_5_9I2R2H : Ball := ⟨(82943350429293694866467701347 / 100000000000000000000000000000000), (424112221 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2R2H_sound : CA2_5_9I2R2H.Encloses (homogeneousEntropy CA2_5_9I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R2Value CA2_5_9I2R2MassTerm_sound CA2_5_9I2R2Entropy_sound) (by decide +kernel)
def CA2_5_9I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA2_5_9I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA2_5_9I2R3Raw_sound (a : PairSlot) :
    (CA2_5_9I2R3Raw a).Encloses (CA2_5_9I2R3Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA2_5_9I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2435297310659647602143457693 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(450772362784741535350836775619 / 100000000000000000000000000000000), (2417317 / 1562500000000000000000000000000)⟩ ⟨(-740398079218739959029923724054193 / 100000000000000000000000000000000), (127054942919 / 50000000000000000000000000000000)⟩ ⟨-11, 2435297310659647602143457693, 1953125000000000000000000000⟩,
   .log ⟨(2129985717566248000727447269227 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(8198431987958046886550801924529 / 100000000000000000000000000000000), (3157294189 / 100000000000000000000000000000000)⟩ ⟨(-15396219646628789554713718736161 / 4000000000000000000000000000000), (118584613 / 80000000000000000000000000000)⟩ ⟨-6, 2129985717566248000727447269227, 1562500000000000000000000000000⟩,
   .log ⟨(26882798760508601774438039839 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(888745450918071274338589927737 / 100000000000000000000000000000000), (31309599 / 10000000000000000000000000000000)⟩ ⟨(-165300023043667812162660823878931 / 25000000000000000000000000000000), (116467031 / 50000000000000000000000000000)⟩ ⟨-10, 26882798760508601774438039839, 19531250000000000000000000000⟩]
lemma CA2_5_9I2R3Certificates_valid :
    CA2_5_9I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA2_5_9I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R3Certificates (CA2_5_9I2R3CertificateIndex a)).input
lemma CA2_5_9I2R3P_check : ∀ a : PairSlot, contains (CA2_5_9I2R3Raw a) (CA2_5_9I2R3P a) = true := by
  decide +kernel
lemma CA2_5_9I2R3P_sound (a : PairSlot) :
    (CA2_5_9I2R3P a).Encloses (CA2_5_9I2R3Value a) :=
  contains_sound (CA2_5_9I2R3Raw_sound a) (CA2_5_9I2R3P_check a)
def CA2_5_9I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R3Certificates (CA2_5_9I2R3CertificateIndex a)).output
lemma CA2_5_9I2R3Terms_sound (a : PairSlot) :
    (CA2_5_9I2R3Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R3Certificates_valid
    (CA2_5_9I2R3CertificateIndex a) (CA2_5_9I2R3P_sound a)
def CA2_5_9I2R3Entropy : Ball := ⟨(1907589960332171939248045725577 / 10000000000000000000000000000000), (3625098467 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I2R3Entropy_sound : CA2_5_9I2R3Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R3Value CA2_5_9I2R3Terms CA2_5_9I2R3Terms_sound) (by decide +kernel)
def CA2_5_9I2R3Mass : Ball := ⟨(2325282144135282199653223910747 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I2R3Mass_sound : CA2_5_9I2R3Mass.Encloses (∑ a, CA2_5_9I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R3P CA2_5_9I2R3Value CA2_5_9I2R3P_sound) (by decide +kernel)
def CA2_5_9I2R3MassTermLogWitness : LogWitness := ⟨-5, 2325282144135282199653223910747, 1562500000000000000000000000000⟩
def CA2_5_9I2R3MassTermLog : Ball := ⟨(-306818162143517270594524012514053 / 100000000000000000000000000000000), (127054942657 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2R3MassTermLog_sound : CA2_5_9I2R3MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I2R3Mass_sound) (w := CA2_5_9I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I2R3MassTerm : Ball := ⟨(2853755175714898042149589920809 / 20000000000000000000000000000000), (590877187 / 10000000000000000000000000000000)⟩
lemma CA2_5_9I2R3MassTerm_sound : CA2_5_9I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I2R3Mass_sound) CA2_5_9I2R3MassTermLog_sound) (by decide +kernel)
def CA2_5_9I2R3H : Ball := ⟨(192284948989889167269300306069 / 4000000000000000000000000000000), (3289742201 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I2R3H_sound : CA2_5_9I2R3H.Encloses (homogeneousEntropy CA2_5_9I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R3Value CA2_5_9I2R3MassTerm_sound CA2_5_9I2R3Entropy_sound) (by decide +kernel)
def CA2_5_9I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA2_5_9I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA2_5_9I2R4Raw_sound (a : PairSlot) :
    (CA2_5_9I2R4Raw a).Encloses (CA2_5_9I2R4Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA2_5_9I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3828098270400182291888320817 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(9070114340891405229949781027 / 12500000000000000000000000000000), (24318951 / 100000000000000000000000000000000)⟩ ⟨(-473870506983784003132945954197861 / 50000000000000000000000000000000), (158818684153 / 50000000000000000000000000000000)⟩ ⟨-14, 3828098270400182291888320817, 3051757812500000000000000000⟩,
   .log ⟨(2832054442480734568472529862261 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩ ⟨(5046958606471071858858950380841 / 50000000000000000000000000000000), (4197976047 / 100000000000000000000000000000000)⟩ ⟨(-71283355726031802428228276296787 / 20000000000000000000000000000000), (926442289 / 625000000000000000000000000000)⟩ ⟨-6, 2832054442480734568472529862261, 1562500000000000000000000000000⟩,
   .log ⟨(7459423225686522421399854785953 / 25000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩ ⟨(9021409510534333997929849792521 / 25000000000000000000000000000000), (4738782971 / 25000000000000000000000000000000)⟩ ⟨(-60469886461657733198408369629621 / 50000000000000000000000000000000), (992616739 / 1562500000000000000000000000000)⟩ ⟨-2, 7459423225686522421399854785953, 6250000000000000000000000000000⟩,
   .log ⟨(353828186837348644017151682629 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(6026146435692866440667433416913 / 100000000000000000000000000000000), (2397633083 / 100000000000000000000000000000000)⟩ ⟨(-425781965645308170662892233837533 / 100000000000000000000000000000000), (169406589817 / 100000000000000000000000000000000)⟩ ⟨-7, 353828186837348644017151682629, 195312500000000000000000000000⟩,
   .log ⟨(52559516800331754163666714549 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(198437911271665158719651026751 / 50000000000000000000000000000000), (16694867 / 12500000000000000000000000000000)⟩ ⟨(-94387241051658899721379744189137 / 12500000000000000000000000000000), (127054943049 / 50000000000000000000000000000000)⟩ ⟨-11, 52559516800331754163666714549, 48828125000000000000000000000⟩]
lemma CA2_5_9I2R4Certificates_valid :
    CA2_5_9I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA2_5_9I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R4Certificates (CA2_5_9I2R4CertificateIndex a)).input
lemma CA2_5_9I2R4P_check : ∀ a : PairSlot, contains (CA2_5_9I2R4Raw a) (CA2_5_9I2R4P a) = true := by
  decide +kernel
lemma CA2_5_9I2R4P_sound (a : PairSlot) :
    (CA2_5_9I2R4P a).Encloses (CA2_5_9I2R4Value a) :=
  contains_sound (CA2_5_9I2R4Raw_sound a) (CA2_5_9I2R4P_check a)
def CA2_5_9I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R4Certificates (CA2_5_9I2R4CertificateIndex a)).output
lemma CA2_5_9I2R4Terms_sound (a : PairSlot) :
    (CA2_5_9I2R4Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R4Certificates_valid
    (CA2_5_9I2R4CertificateIndex a) (CA2_5_9I2R4P_sound a)
def CA2_5_9I2R4Entropy : Ball := ⟨(8608470373925618638701070759651 / 12500000000000000000000000000000), (16164273491 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I2R4Entropy_sound : CA2_5_9I2R4Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R4Value CA2_5_9I2R4Terms CA2_5_9I2R4Terms_sound) (by decide +kernel)
def CA2_5_9I2R4Mass : Ball := ⟨(38400299192288280458012912327183 / 100000000000000000000000000000000), (113 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2R4Mass_sound : CA2_5_9I2R4Mass.Encloses (∑ a, CA2_5_9I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R4P CA2_5_9I2R4Value CA2_5_9I2R4P_sound) (by decide +kernel)
def CA2_5_9I2R4MassTermLogWitness : LogWitness := ⟨-2, 38400299192288280458012912327183, 25000000000000000000000000000000⟩
def CA2_5_9I2R4MassTermLog : Ball := ⟨(-5981905843493267938244762848697 / 6250000000000000000000000000000), (63527471343 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2R4MassTermLog_sound : CA2_5_9I2R4MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I2R4Mass_sound) (w := CA2_5_9I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I2R4MassTerm : Ball := ⟨(36753115860838253091643556582981 / 100000000000000000000000000000000), (12197369587 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I2R4MassTerm_sound : CA2_5_9I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I2R4Mass_sound) CA2_5_9I2R4MassTermLog_sound) (by decide +kernel)
def CA2_5_9I2R4H : Ball := ⟨(32114647130566696017965009494227 / 100000000000000000000000000000000), (14180821539 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I2R4H_sound : CA2_5_9I2R4H.Encloses (homogeneousEntropy CA2_5_9I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R4Value CA2_5_9I2R4MassTerm_sound CA2_5_9I2R4Entropy_sound) (by decide +kernel)
def CA2_5_9I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA2_5_9I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA2_5_9I2R5Raw_sound (a : PairSlot) :
    (CA2_5_9I2R5Raw a).Encloses (CA2_5_9I2R5Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA2_5_9I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5600488392744089971371737059 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(188261028826472976735768689537 / 100000000000000000000000000000000), (13282637 / 20000000000000000000000000000000)⟩ ⟨(-210094432423051247419052727635687 / 25000000000000000000000000000000), (11858461441 / 4000000000000000000000000000000)⟩ ⟨-13, 5600488392744089971371737059, 3051757812500000000000000000⟩,
   .log ⟨(7032027662952837067374330528689 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩ ⟨(431051849177102147077217782683 / 1562500000000000000000000000000), (11912718347 / 100000000000000000000000000000000)⟩ ⟨(-196154791118599458479523003440067 / 100000000000000000000000000000000), (84703295001 / 100000000000000000000000000000000)⟩ ⟨-3, 7032027662952837067374330528689, 6250000000000000000000000000000⟩,
   .log ⟨(522995654078156671821857071841 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(137374021387740878646307130533 / 5000000000000000000000000000000), (498368879 / 50000000000000000000000000000000)⟩ ⟨(-525335231054182534454967113010739 / 100000000000000000000000000000000), (4764560343 / 2500000000000000000000000000000)⟩ ⟨-8, 522995654078156671821857071841, 390625000000000000000000000000⟩]
lemma CA2_5_9I2R5Certificates_valid :
    CA2_5_9I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA2_5_9I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R5Certificates (CA2_5_9I2R5CertificateIndex a)).input
lemma CA2_5_9I2R5P_check : ∀ a : PairSlot, contains (CA2_5_9I2R5Raw a) (CA2_5_9I2R5P a) = true := by
  decide +kernel
lemma CA2_5_9I2R5P_sound (a : PairSlot) :
    (CA2_5_9I2R5P a).Encloses (CA2_5_9I2R5Value a) :=
  contains_sound (CA2_5_9I2R5Raw_sound a) (CA2_5_9I2R5P_check a)
def CA2_5_9I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R5Certificates (CA2_5_9I2R5CertificateIndex a)).output
lemma CA2_5_9I2R5Terms_sound (a : PairSlot) :
    (CA2_5_9I2R5Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R5Certificates_valid
    (CA2_5_9I2R5CertificateIndex a) (CA2_5_9I2R5P_sound a)
def CA2_5_9I2R5Entropy : Ball := ⟨(30523059803915827962603849391909 / 50000000000000000000000000000000), (1297586929 / 5000000000000000000000000000000)⟩
lemma CA2_5_9I2R5Entropy_sound : CA2_5_9I2R5Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R5Value CA2_5_9I2R5Terms CA2_5_9I2R5Terms_sound) (by decide +kernel)
def CA2_5_9I2R5Mass : Ball := ⟨(2921890586710961433291201015491 / 10000000000000000000000000000000), (21 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I2R5Mass_sound : CA2_5_9I2R5Mass.Encloses (∑ a, CA2_5_9I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R5P CA2_5_9I2R5Value CA2_5_9I2R5P_sound) (by decide +kernel)
def CA2_5_9I2R5MassTermLogWitness : LogWitness := ⟨-2, 2921890586710961433291201015491, 2500000000000000000000000000000⟩
def CA2_5_9I2R5MassTermLog : Ball := ⟨(-61517711251202312490872296417681 / 50000000000000000000000000000000), (7940933917 / 12500000000000000000000000000000)⟩
lemma CA2_5_9I2R5MassTermLog_sound : CA2_5_9I2R5MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I2R5Mass_sound) (w := CA2_5_9I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I2R5MassTerm : Ball := ⟨(4493700535522275955311475321987 / 12500000000000000000000000000000), (18562032153 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2R5MassTerm_sound : CA2_5_9I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I2R5Mass_sound) CA2_5_9I2R5MassTermLog_sound) (by decide +kernel)
def CA2_5_9I2R5H : Ball := ⟨(12548257661826724141357948103961 / 50000000000000000000000000000000), (44513770733 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2R5H_sound : CA2_5_9I2R5H.Encloses (homogeneousEntropy CA2_5_9I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R5Value CA2_5_9I2R5MassTerm_sound CA2_5_9I2R5Entropy_sound) (by decide +kernel)
def CA2_5_9I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA2_5_9I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA2_5_9I2R6Raw_sound (a : PairSlot) :
    (CA2_5_9I2R6Raw a).Encloses (CA2_5_9I2R6Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA2_5_9I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(127392809289938692686235391 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(142213182094479633474873263753 / 100000000000000000000000000000000), (48341857 / 100000000000000000000000000000000)⟩ ⟨(-872137518048179641181611031582051 / 100000000000000000000000000000000), (148230768847 / 50000000000000000000000000000000)⟩ ⟨-13, 127392809289938692686235391, 95367431640625000000000000⟩,
   .log ⟨(1027360337815347984744841 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(18896945527695584274138771 / 100000000000000000000000000000000), (6111 / 100000000000000000000000000000000)⟩ ⟨(-459842200251748861877244363010299 / 25000000000000000000000000000000), (118604079991 / 20000000000000000000000000000000)⟩ ⟨-27, 1027360337815347984744841, 745058059692382812500000⟩,
   .log ⟨(1709849214635406479942292747789 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(6956974636259068527774212910991 / 100000000000000000000000000000000), (1267261313 / 50000000000000000000000000000000)⟩ ⟨(-406876499793726774946044078329567 / 100000000000000000000000000000000), (18528845781 / 12500000000000000000000000000000)⟩ ⟨-6, 1709849214635406479942292747789, 1562500000000000000000000000000⟩]
lemma CA2_5_9I2R6Certificates_valid :
    CA2_5_9I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA2_5_9I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R6Certificates (CA2_5_9I2R6CertificateIndex a)).input
lemma CA2_5_9I2R6P_check : ∀ a : PairSlot, contains (CA2_5_9I2R6Raw a) (CA2_5_9I2R6P a) = true := by
  decide +kernel
lemma CA2_5_9I2R6P_sound (a : PairSlot) :
    (CA2_5_9I2R6P a).Encloses (CA2_5_9I2R6Value a) :=
  contains_sound (CA2_5_9I2R6Raw_sound a) (CA2_5_9I2R6P_check a)
def CA2_5_9I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R6Certificates (CA2_5_9I2R6CertificateIndex a)).output
lemma CA2_5_9I2R6Terms_sound (a : PairSlot) :
    (CA2_5_9I2R6Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R6Certificates_valid
    (CA2_5_9I2R6CertificateIndex a) (CA2_5_9I2R6P_sound a)
def CA2_5_9I2R6Entropy : Ball := ⟨(7241438794339083185892507716039 / 100000000000000000000000000000000), (1315609281 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I2R6Entropy_sound : CA2_5_9I2R6Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R6Value CA2_5_9I2R6Terms CA2_5_9I2R6Terms_sound) (by decide +kernel)
def CA2_5_9I2R6Mass : Ball := ⟨(1742463828534306415965938497567 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I2R6Mass_sound : CA2_5_9I2R6Mass.Encloses (∑ a, CA2_5_9I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R6P CA2_5_9I2R6Value CA2_5_9I2R6P_sound) (by decide +kernel)
def CA2_5_9I2R6MassTermLogWitness : LogWitness := ⟨-6, 1742463828534306415965938497567, 1562500000000000000000000000000⟩
def CA2_5_9I2R6MassTermLog : Ball := ⟨(-202493504046221639271742787434751 / 50000000000000000000000000000000), (148230766469 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2R6MassTermLog_sound : CA2_5_9I2R6MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I2R6Mass_sound) (w := CA2_5_9I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I2R6MassTerm : Ball := ⟨(7056752126274128498103940381303 / 100000000000000000000000000000000), (1291433769 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I2R6MassTerm_sound : CA2_5_9I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I2R6Mass_sound) CA2_5_9I2R6MassTermLog_sound) (by decide +kernel)
def CA2_5_9I2R6H : Ball := ⟨(11542916754059667986785458421 / 6250000000000000000000000000000), (52140861 / 1000000000000000000000000000000)⟩
lemma CA2_5_9I2R6H_sound : CA2_5_9I2R6H.Encloses (homogeneousEntropy CA2_5_9I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R6Value CA2_5_9I2R6MassTerm_sound CA2_5_9I2R6Entropy_sound) (by decide +kernel)
def CA2_5_9I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA2_5_9I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA2_5_9I2R7Raw_sound (a : PairSlot) :
    (CA2_5_9I2R7Raw a).Encloses (CA2_5_9I2R7Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA2_5_9I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I2R7Certificates_valid :
    CA2_5_9I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R7Certificates (CA2_5_9I2R7CertificateIndex a)).input
lemma CA2_5_9I2R7P_check : ∀ a : PairSlot, contains (CA2_5_9I2R7Raw a) (CA2_5_9I2R7P a) = true := by
  decide +kernel
lemma CA2_5_9I2R7P_sound (a : PairSlot) :
    (CA2_5_9I2R7P a).Encloses (CA2_5_9I2R7Value a) :=
  contains_sound (CA2_5_9I2R7Raw_sound a) (CA2_5_9I2R7P_check a)
def CA2_5_9I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R7Certificates (CA2_5_9I2R7CertificateIndex a)).output
lemma CA2_5_9I2R7Terms_sound (a : PairSlot) :
    (CA2_5_9I2R7Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R7Certificates_valid
    (CA2_5_9I2R7CertificateIndex a) (CA2_5_9I2R7P_sound a)
def CA2_5_9I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R7Entropy_sound : CA2_5_9I2R7Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R7Value CA2_5_9I2R7Terms CA2_5_9I2R7Terms_sound) (by decide +kernel)
def CA2_5_9I2R7Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R7Mass_sound : CA2_5_9I2R7Mass.Encloses (∑ a, CA2_5_9I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R7P CA2_5_9I2R7Value CA2_5_9I2R7P_sound) (by decide +kernel)
def CA2_5_9I2R7MassTerm : Ball := .exact 0
lemma CA2_5_9I2R7MassTerm_sound : CA2_5_9I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R7Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I2R7Mass_sound)
def CA2_5_9I2R7H : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R7H_sound : CA2_5_9I2R7H.Encloses (homogeneousEntropy CA2_5_9I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R7Value CA2_5_9I2R7MassTerm_sound CA2_5_9I2R7Entropy_sound) (by decide +kernel)
def CA2_5_9I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA2_5_9I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA2_5_9I2R8Raw_sound (a : PairSlot) :
    (CA2_5_9I2R8Raw a).Encloses (CA2_5_9I2R8Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA2_5_9I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I2R8Certificates_valid :
    CA2_5_9I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R8Certificates (CA2_5_9I2R8CertificateIndex a)).input
lemma CA2_5_9I2R8P_check : ∀ a : PairSlot, contains (CA2_5_9I2R8Raw a) (CA2_5_9I2R8P a) = true := by
  decide +kernel
lemma CA2_5_9I2R8P_sound (a : PairSlot) :
    (CA2_5_9I2R8P a).Encloses (CA2_5_9I2R8Value a) :=
  contains_sound (CA2_5_9I2R8Raw_sound a) (CA2_5_9I2R8P_check a)
def CA2_5_9I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R8Certificates (CA2_5_9I2R8CertificateIndex a)).output
lemma CA2_5_9I2R8Terms_sound (a : PairSlot) :
    (CA2_5_9I2R8Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R8Certificates_valid
    (CA2_5_9I2R8CertificateIndex a) (CA2_5_9I2R8P_sound a)
def CA2_5_9I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R8Entropy_sound : CA2_5_9I2R8Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R8Value CA2_5_9I2R8Terms CA2_5_9I2R8Terms_sound) (by decide +kernel)
def CA2_5_9I2R8Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R8Mass_sound : CA2_5_9I2R8Mass.Encloses (∑ a, CA2_5_9I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R8P CA2_5_9I2R8Value CA2_5_9I2R8P_sound) (by decide +kernel)
def CA2_5_9I2R8MassTerm : Ball := .exact 0
lemma CA2_5_9I2R8MassTerm_sound : CA2_5_9I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R8Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I2R8Mass_sound)
def CA2_5_9I2R8H : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R8H_sound : CA2_5_9I2R8H.Encloses (homogeneousEntropy CA2_5_9I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R8Value CA2_5_9I2R8MassTerm_sound CA2_5_9I2R8Entropy_sound) (by decide +kernel)
def CA2_5_9I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA2_5_9I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA2_5_9I2R9Raw_sound (a : PairSlot) :
    (CA2_5_9I2R9Raw a).Encloses (CA2_5_9I2R9Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA2_5_9I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I2R9Certificates_valid :
    CA2_5_9I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R9Certificates (CA2_5_9I2R9CertificateIndex a)).input
lemma CA2_5_9I2R9P_check : ∀ a : PairSlot, contains (CA2_5_9I2R9Raw a) (CA2_5_9I2R9P a) = true := by
  decide +kernel
lemma CA2_5_9I2R9P_sound (a : PairSlot) :
    (CA2_5_9I2R9P a).Encloses (CA2_5_9I2R9Value a) :=
  contains_sound (CA2_5_9I2R9Raw_sound a) (CA2_5_9I2R9P_check a)
def CA2_5_9I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R9Certificates (CA2_5_9I2R9CertificateIndex a)).output
lemma CA2_5_9I2R9Terms_sound (a : PairSlot) :
    (CA2_5_9I2R9Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R9Certificates_valid
    (CA2_5_9I2R9CertificateIndex a) (CA2_5_9I2R9P_sound a)
def CA2_5_9I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R9Entropy_sound : CA2_5_9I2R9Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R9Value CA2_5_9I2R9Terms CA2_5_9I2R9Terms_sound) (by decide +kernel)
def CA2_5_9I2R9Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R9Mass_sound : CA2_5_9I2R9Mass.Encloses (∑ a, CA2_5_9I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R9P CA2_5_9I2R9Value CA2_5_9I2R9P_sound) (by decide +kernel)
def CA2_5_9I2R9MassTerm : Ball := .exact 0
lemma CA2_5_9I2R9MassTerm_sound : CA2_5_9I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R9Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I2R9Mass_sound)
def CA2_5_9I2R9H : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R9H_sound : CA2_5_9I2R9H.Encloses (homogeneousEntropy CA2_5_9I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R9Value CA2_5_9I2R9MassTerm_sound CA2_5_9I2R9Entropy_sound) (by decide +kernel)
def CA2_5_9I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA2_5_9I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA2_5_9I2R10Raw_sound (a : PairSlot) :
    (CA2_5_9I2R10Raw a).Encloses (CA2_5_9I2R10Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA2_5_9I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I2R10Certificates_valid :
    CA2_5_9I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R10Certificates (CA2_5_9I2R10CertificateIndex a)).input
lemma CA2_5_9I2R10P_check : ∀ a : PairSlot, contains (CA2_5_9I2R10Raw a) (CA2_5_9I2R10P a) = true := by
  decide +kernel
lemma CA2_5_9I2R10P_sound (a : PairSlot) :
    (CA2_5_9I2R10P a).Encloses (CA2_5_9I2R10Value a) :=
  contains_sound (CA2_5_9I2R10Raw_sound a) (CA2_5_9I2R10P_check a)
def CA2_5_9I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R10Certificates (CA2_5_9I2R10CertificateIndex a)).output
lemma CA2_5_9I2R10Terms_sound (a : PairSlot) :
    (CA2_5_9I2R10Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R10Certificates_valid
    (CA2_5_9I2R10CertificateIndex a) (CA2_5_9I2R10P_sound a)
def CA2_5_9I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R10Entropy_sound : CA2_5_9I2R10Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R10Value CA2_5_9I2R10Terms CA2_5_9I2R10Terms_sound) (by decide +kernel)
def CA2_5_9I2R10Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R10Mass_sound : CA2_5_9I2R10Mass.Encloses (∑ a, CA2_5_9I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R10P CA2_5_9I2R10Value CA2_5_9I2R10P_sound) (by decide +kernel)
def CA2_5_9I2R10MassTerm : Ball := .exact 0
lemma CA2_5_9I2R10MassTerm_sound : CA2_5_9I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R10Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I2R10Mass_sound)
def CA2_5_9I2R10H : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R10H_sound : CA2_5_9I2R10H.Encloses (homogeneousEntropy CA2_5_9I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R10Value CA2_5_9I2R10MassTerm_sound CA2_5_9I2R10Entropy_sound) (by decide +kernel)
def CA2_5_9I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA2_5_9I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA2_5_9I2R11Raw_sound (a : PairSlot) :
    (CA2_5_9I2R11Raw a).Encloses (CA2_5_9I2R11Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA2_5_9I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I2R11Certificates_valid :
    CA2_5_9I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R11Certificates (CA2_5_9I2R11CertificateIndex a)).input
lemma CA2_5_9I2R11P_check : ∀ a : PairSlot, contains (CA2_5_9I2R11Raw a) (CA2_5_9I2R11P a) = true := by
  decide +kernel
lemma CA2_5_9I2R11P_sound (a : PairSlot) :
    (CA2_5_9I2R11P a).Encloses (CA2_5_9I2R11Value a) :=
  contains_sound (CA2_5_9I2R11Raw_sound a) (CA2_5_9I2R11P_check a)
def CA2_5_9I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R11Certificates (CA2_5_9I2R11CertificateIndex a)).output
lemma CA2_5_9I2R11Terms_sound (a : PairSlot) :
    (CA2_5_9I2R11Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R11Certificates_valid
    (CA2_5_9I2R11CertificateIndex a) (CA2_5_9I2R11P_sound a)
def CA2_5_9I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R11Entropy_sound : CA2_5_9I2R11Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R11Value CA2_5_9I2R11Terms CA2_5_9I2R11Terms_sound) (by decide +kernel)
def CA2_5_9I2R11Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R11Mass_sound : CA2_5_9I2R11Mass.Encloses (∑ a, CA2_5_9I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R11P CA2_5_9I2R11Value CA2_5_9I2R11P_sound) (by decide +kernel)
def CA2_5_9I2R11MassTerm : Ball := .exact 0
lemma CA2_5_9I2R11MassTerm_sound : CA2_5_9I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R11Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I2R11Mass_sound)
def CA2_5_9I2R11H : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R11H_sound : CA2_5_9I2R11H.Encloses (homogeneousEntropy CA2_5_9I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R11Value CA2_5_9I2R11MassTerm_sound CA2_5_9I2R11Entropy_sound) (by decide +kernel)
def CA2_5_9I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA2_5_9I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA2_5_9I2R12Raw_sound (a : PairSlot) :
    (CA2_5_9I2R12Raw a).Encloses (CA2_5_9I2R12Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA2_5_9I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I2R12Certificates_valid :
    CA2_5_9I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R12Certificates (CA2_5_9I2R12CertificateIndex a)).input
lemma CA2_5_9I2R12P_check : ∀ a : PairSlot, contains (CA2_5_9I2R12Raw a) (CA2_5_9I2R12P a) = true := by
  decide +kernel
lemma CA2_5_9I2R12P_sound (a : PairSlot) :
    (CA2_5_9I2R12P a).Encloses (CA2_5_9I2R12Value a) :=
  contains_sound (CA2_5_9I2R12Raw_sound a) (CA2_5_9I2R12P_check a)
def CA2_5_9I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R12Certificates (CA2_5_9I2R12CertificateIndex a)).output
lemma CA2_5_9I2R12Terms_sound (a : PairSlot) :
    (CA2_5_9I2R12Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R12Certificates_valid
    (CA2_5_9I2R12CertificateIndex a) (CA2_5_9I2R12P_sound a)
def CA2_5_9I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R12Entropy_sound : CA2_5_9I2R12Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R12Value CA2_5_9I2R12Terms CA2_5_9I2R12Terms_sound) (by decide +kernel)
def CA2_5_9I2R12Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R12Mass_sound : CA2_5_9I2R12Mass.Encloses (∑ a, CA2_5_9I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R12P CA2_5_9I2R12Value CA2_5_9I2R12P_sound) (by decide +kernel)
def CA2_5_9I2R12MassTerm : Ball := .exact 0
lemma CA2_5_9I2R12MassTerm_sound : CA2_5_9I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R12Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I2R12Mass_sound)
def CA2_5_9I2R12H : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R12H_sound : CA2_5_9I2R12H.Encloses (homogeneousEntropy CA2_5_9I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R12Value CA2_5_9I2R12MassTerm_sound CA2_5_9I2R12Entropy_sound) (by decide +kernel)
def CA2_5_9I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA2_5_9I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA2_5_9I2R13Raw_sound (a : PairSlot) :
    (CA2_5_9I2R13Raw a).Encloses (CA2_5_9I2R13Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA2_5_9I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I2R13Certificates_valid :
    CA2_5_9I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R13Certificates (CA2_5_9I2R13CertificateIndex a)).input
lemma CA2_5_9I2R13P_check : ∀ a : PairSlot, contains (CA2_5_9I2R13Raw a) (CA2_5_9I2R13P a) = true := by
  decide +kernel
lemma CA2_5_9I2R13P_sound (a : PairSlot) :
    (CA2_5_9I2R13P a).Encloses (CA2_5_9I2R13Value a) :=
  contains_sound (CA2_5_9I2R13Raw_sound a) (CA2_5_9I2R13P_check a)
def CA2_5_9I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R13Certificates (CA2_5_9I2R13CertificateIndex a)).output
lemma CA2_5_9I2R13Terms_sound (a : PairSlot) :
    (CA2_5_9I2R13Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R13Certificates_valid
    (CA2_5_9I2R13CertificateIndex a) (CA2_5_9I2R13P_sound a)
def CA2_5_9I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R13Entropy_sound : CA2_5_9I2R13Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R13Value CA2_5_9I2R13Terms CA2_5_9I2R13Terms_sound) (by decide +kernel)
def CA2_5_9I2R13Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R13Mass_sound : CA2_5_9I2R13Mass.Encloses (∑ a, CA2_5_9I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R13P CA2_5_9I2R13Value CA2_5_9I2R13P_sound) (by decide +kernel)
def CA2_5_9I2R13MassTerm : Ball := .exact 0
lemma CA2_5_9I2R13MassTerm_sound : CA2_5_9I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R13Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I2R13Mass_sound)
def CA2_5_9I2R13H : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R13H_sound : CA2_5_9I2R13H.Encloses (homogeneousEntropy CA2_5_9I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R13Value CA2_5_9I2R13MassTerm_sound CA2_5_9I2R13Entropy_sound) (by decide +kernel)
def CA2_5_9I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA2_5_9I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA2_5_9I2R14Raw_sound (a : PairSlot) :
    (CA2_5_9I2R14Raw a).Encloses (CA2_5_9I2R14Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA2_5_9I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I2R14Certificates_valid :
    CA2_5_9I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R14Certificates (CA2_5_9I2R14CertificateIndex a)).input
lemma CA2_5_9I2R14P_check : ∀ a : PairSlot, contains (CA2_5_9I2R14Raw a) (CA2_5_9I2R14P a) = true := by
  decide +kernel
lemma CA2_5_9I2R14P_sound (a : PairSlot) :
    (CA2_5_9I2R14P a).Encloses (CA2_5_9I2R14Value a) :=
  contains_sound (CA2_5_9I2R14Raw_sound a) (CA2_5_9I2R14P_check a)
def CA2_5_9I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R14Certificates (CA2_5_9I2R14CertificateIndex a)).output
lemma CA2_5_9I2R14Terms_sound (a : PairSlot) :
    (CA2_5_9I2R14Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R14Certificates_valid
    (CA2_5_9I2R14CertificateIndex a) (CA2_5_9I2R14P_sound a)
def CA2_5_9I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R14Entropy_sound : CA2_5_9I2R14Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R14Value CA2_5_9I2R14Terms CA2_5_9I2R14Terms_sound) (by decide +kernel)
def CA2_5_9I2R14Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R14Mass_sound : CA2_5_9I2R14Mass.Encloses (∑ a, CA2_5_9I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R14P CA2_5_9I2R14Value CA2_5_9I2R14P_sound) (by decide +kernel)
def CA2_5_9I2R14MassTerm : Ball := .exact 0
lemma CA2_5_9I2R14MassTerm_sound : CA2_5_9I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R14Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I2R14Mass_sound)
def CA2_5_9I2R14H : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R14H_sound : CA2_5_9I2R14H.Encloses (homogeneousEntropy CA2_5_9I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R14Value CA2_5_9I2R14MassTerm_sound CA2_5_9I2R14Entropy_sound) (by decide +kernel)
def CA2_5_9I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA2_5_9I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA2_5_9I2R15Raw_sound (a : PairSlot) :
    (CA2_5_9I2R15Raw a).Encloses (CA2_5_9I2R15Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA2_5_9I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I2R15Certificates_valid :
    CA2_5_9I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R15Certificates (CA2_5_9I2R15CertificateIndex a)).input
lemma CA2_5_9I2R15P_check : ∀ a : PairSlot, contains (CA2_5_9I2R15Raw a) (CA2_5_9I2R15P a) = true := by
  decide +kernel
lemma CA2_5_9I2R15P_sound (a : PairSlot) :
    (CA2_5_9I2R15P a).Encloses (CA2_5_9I2R15Value a) :=
  contains_sound (CA2_5_9I2R15Raw_sound a) (CA2_5_9I2R15P_check a)
def CA2_5_9I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R15Certificates (CA2_5_9I2R15CertificateIndex a)).output
lemma CA2_5_9I2R15Terms_sound (a : PairSlot) :
    (CA2_5_9I2R15Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R15Certificates_valid
    (CA2_5_9I2R15CertificateIndex a) (CA2_5_9I2R15P_sound a)
def CA2_5_9I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R15Entropy_sound : CA2_5_9I2R15Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R15Value CA2_5_9I2R15Terms CA2_5_9I2R15Terms_sound) (by decide +kernel)
def CA2_5_9I2R15Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R15Mass_sound : CA2_5_9I2R15Mass.Encloses (∑ a, CA2_5_9I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R15P CA2_5_9I2R15Value CA2_5_9I2R15P_sound) (by decide +kernel)
def CA2_5_9I2R15MassTerm : Ball := .exact 0
lemma CA2_5_9I2R15MassTerm_sound : CA2_5_9I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R15Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I2R15Mass_sound)
def CA2_5_9I2R15H : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R15H_sound : CA2_5_9I2R15H.Encloses (homogeneousEntropy CA2_5_9I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R15Value CA2_5_9I2R15MassTerm_sound CA2_5_9I2R15Entropy_sound) (by decide +kernel)
def CA2_5_9I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA2_5_9I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 5 9)) A2_5_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA2_5_9I2R16Raw_sound (a : PairSlot) :
    (CA2_5_9I2R16Raw a).Encloses (CA2_5_9I2R16Value a) := by
  exact residualBall_sound_on (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 5 9) (show (shape 2 5 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA2_5_9I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_5_9I2R16Certificates_valid :
    CA2_5_9I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_5_9I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R16Certificates (CA2_5_9I2R16CertificateIndex a)).input
lemma CA2_5_9I2R16P_check : ∀ a : PairSlot, contains (CA2_5_9I2R16Raw a) (CA2_5_9I2R16P a) = true := by
  decide +kernel
lemma CA2_5_9I2R16P_sound (a : PairSlot) :
    (CA2_5_9I2R16P a).Encloses (CA2_5_9I2R16Value a) :=
  contains_sound (CA2_5_9I2R16Raw_sound a) (CA2_5_9I2R16P_check a)
def CA2_5_9I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I2R16Certificates (CA2_5_9I2R16CertificateIndex a)).output
lemma CA2_5_9I2R16Terms_sound (a : PairSlot) :
    (CA2_5_9I2R16Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2R16Certificates_valid
    (CA2_5_9I2R16CertificateIndex a) (CA2_5_9I2R16P_sound a)
def CA2_5_9I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R16Entropy_sound : CA2_5_9I2R16Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_5_9I2R16Value CA2_5_9I2R16Terms CA2_5_9I2R16Terms_sound) (by decide +kernel)
def CA2_5_9I2R16Mass : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R16Mass_sound : CA2_5_9I2R16Mass.Encloses (∑ a, CA2_5_9I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_5_9I2R16P CA2_5_9I2R16Value CA2_5_9I2R16P_sound) (by decide +kernel)
def CA2_5_9I2R16MassTerm : Ball := .exact 0
lemma CA2_5_9I2R16MassTerm_sound : CA2_5_9I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I2R16Value a))) :=
  entropyTerm_zero_ball (CA2_5_9I2R16Mass_sound)
def CA2_5_9I2R16H : Ball := ⟨0, 0⟩
lemma CA2_5_9I2R16H_sound : CA2_5_9I2R16H.Encloses (homogeneousEntropy CA2_5_9I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I2R16Value CA2_5_9I2R16MassTerm_sound CA2_5_9I2R16Entropy_sound) (by decide +kernel)
def CA2_5_9I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_5_9I2R0H
  | 1 => CA2_5_9I2R1H
  | 2 => CA2_5_9I2R2H
  | 3 => CA2_5_9I2R3H
  | 4 => CA2_5_9I2R4H
  | 5 => CA2_5_9I2R5H
  | 6 => CA2_5_9I2R6H
  | 7 => CA2_5_9I2R7H
  | 8 => CA2_5_9I2R8H
  | 9 => CA2_5_9I2R9H
  | 10 => CA2_5_9I2R10H
  | 11 => CA2_5_9I2R11H
  | 12 => CA2_5_9I2R12H
  | 13 => CA2_5_9I2R13H
  | 14 => CA2_5_9I2R14H
  | 15 => CA2_5_9I2R15H
  | 16 => CA2_5_9I2R16H
  | _ => (.exact 0)
lemma CA2_5_9I2ResidualEntropies_sound (k : Fin 17) :
    (CA2_5_9I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_5_9I2R0H_sound
  · exact CA2_5_9I2R1H_sound
  · exact CA2_5_9I2R2H_sound
  · exact CA2_5_9I2R3H_sound
  · exact CA2_5_9I2R4H_sound
  · exact CA2_5_9I2R5H_sound
  · exact CA2_5_9I2R6H_sound
  · exact CA2_5_9I2R7H_sound
  · exact CA2_5_9I2R8H_sound
  · exact CA2_5_9I2R9H_sound
  · exact CA2_5_9I2R10H_sound
  · exact CA2_5_9I2R11H_sound
  · exact CA2_5_9I2R12H_sound
  · exact CA2_5_9I2R13H_sound
  · exact CA2_5_9I2R14H_sound
  · exact CA2_5_9I2R15H_sound
  · exact CA2_5_9I2R16H_sound
def CA2_5_9I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | _, _, _ => (.exact 0)
lemma CA2_5_9I2Singles_sound (u : Shape) (hu : u ∈ below (shape 2 5 9))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA2_5_9I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A2_5_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z0_5_3H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact Z2_0_6H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 5 1) by decide +kernel) hd |>.elim
def CA2_5_9I2Singleton : Ball := ⟨(30652448503721051159498519689651 / 100000000000000000000000000000000), (25420405831 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2Singleton_sound : CA2_5_9I2Singleton.Encloses
    (singletonEntropy (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA2_5_9I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_5_9Law_sound u) CA2_5_9I2Singles_sound) (by decide +kernel)
def CA2_5_9I2Group : Ball := ⟨(92938450353625246814009033042313 / 100000000000000000000000000000000), (2909115103 / 2000000000000000000000000000000)⟩
lemma CA2_5_9I2Group_sound : CA2_5_9I2Group.Encloses
    (groupedEntropy (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_5_9I2Singleton_sound
    (finSumBall_sound 17 CA2_5_9I2ResidualEntropies _ CA2_5_9I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA2_5_9I2H : Ball := ⟨(53271317490750496935685571785111 / 50000000000000000000000000000000), (449852656411 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I2_sound : CA2_5_9I2H.Encloses (stageACapacity (shape 2 5 9) 2) := by
  have hb := contains_sound (Ball.add_sound CA2_5_9I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA2_5_9I2Group_sound)))
    (show contains (.add CA2_5_9I2PairH (.neg (.mul (.exact 2) CA2_5_9I2Group))) CA2_5_9I2H = true by decide +kernel)
  unfold CA2_5_9I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
