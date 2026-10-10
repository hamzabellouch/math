import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA3_4_9I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_4_9I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA3_4_9I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA3_4_9I2R0Raw_sound (a : PairSlot) :
    (CA3_4_9I2R0Raw a).Encloses (CA3_4_9I2R0Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA3_4_9I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I2R0Certificates_valid :
    CA3_4_9I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R0Certificates (CA3_4_9I2R0CertificateIndex a)).input
lemma CA3_4_9I2R0P_check : ∀ a : PairSlot, contains (CA3_4_9I2R0Raw a) (CA3_4_9I2R0P a) = true := by
  decide +kernel
lemma CA3_4_9I2R0P_sound (a : PairSlot) :
    (CA3_4_9I2R0P a).Encloses (CA3_4_9I2R0Value a) :=
  contains_sound (CA3_4_9I2R0Raw_sound a) (CA3_4_9I2R0P_check a)
def CA3_4_9I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R0Certificates (CA3_4_9I2R0CertificateIndex a)).output
lemma CA3_4_9I2R0Terms_sound (a : PairSlot) :
    (CA3_4_9I2R0Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R0Certificates_valid
    (CA3_4_9I2R0CertificateIndex a) (CA3_4_9I2R0P_sound a)
def CA3_4_9I2R0Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R0Entropy_sound : CA3_4_9I2R0Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R0Value CA3_4_9I2R0Terms CA3_4_9I2R0Terms_sound) (by decide +kernel)
def CA3_4_9I2R0Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R0Mass_sound : CA3_4_9I2R0Mass.Encloses (∑ a, CA3_4_9I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R0P CA3_4_9I2R0Value CA3_4_9I2R0P_sound) (by decide +kernel)
def CA3_4_9I2R0MassTerm : Ball := .exact 0
lemma CA3_4_9I2R0MassTerm_sound : CA3_4_9I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R0Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R0Mass_sound)
def CA3_4_9I2R0H : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R0H_sound : CA3_4_9I2R0H.Encloses (homogeneousEntropy CA3_4_9I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R0Value CA3_4_9I2R0MassTerm_sound CA3_4_9I2R0Entropy_sound) (by decide +kernel)
def CA3_4_9I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA3_4_9I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA3_4_9I2R1Raw_sound (a : PairSlot) :
    (CA3_4_9I2R1Raw a).Encloses (CA3_4_9I2R1Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA3_4_9I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2961092486317753981806299 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(849205210818614472015140153 / 100000000000000000000000000000000), (34489 / 12500000000000000000000000000000)⟩ ⟨(-89621188668383771972172972770083 / 6250000000000000000000000000000), (465869809591 / 100000000000000000000000000000000)⟩ ⟨-21, 2961092486317753981806299, 2384185791015625000000000⟩]
lemma CA3_4_9I2R1Certificates_valid :
    CA3_4_9I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA3_4_9I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R1Certificates (CA3_4_9I2R1CertificateIndex a)).input
lemma CA3_4_9I2R1P_check : ∀ a : PairSlot, contains (CA3_4_9I2R1Raw a) (CA3_4_9I2R1P a) = true := by
  decide +kernel
lemma CA3_4_9I2R1P_sound (a : PairSlot) :
    (CA3_4_9I2R1P a).Encloses (CA3_4_9I2R1Value a) :=
  contains_sound (CA3_4_9I2R1Raw_sound a) (CA3_4_9I2R1P_check a)
def CA3_4_9I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R1Certificates (CA3_4_9I2R1CertificateIndex a)).output
lemma CA3_4_9I2R1Terms_sound (a : PairSlot) :
    (CA3_4_9I2R1Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R1Certificates_valid
    (CA3_4_9I2R1CertificateIndex a) (CA3_4_9I2R1P_sound a)
def CA3_4_9I2R1Entropy : Ball := ⟨(849205210818614472015140153 / 50000000000000000000000000000000), (34489 / 6250000000000000000000000000000)⟩
lemma CA3_4_9I2R1Entropy_sound : CA3_4_9I2R1Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R1Value CA3_4_9I2R1Terms CA3_4_9I2R1Terms_sound) (by decide +kernel)
def CA3_4_9I2R1Mass : Ball := ⟨(2961092486317753981806299 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I2R1Mass_sound : CA3_4_9I2R1Mass.Encloses (∑ a, CA3_4_9I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R1P CA3_4_9I2R1Value CA3_4_9I2R1P_sound) (by decide +kernel)
def CA3_4_9I2R1MassTermLogWitness : LogWitness := ⟨-20, 2961092486317753981806299, 2384185791015625000000000⟩
def CA3_4_9I2R1MassTermLog : Ball := ⟨(-682312150319072910306522185635499 / 50000000000000000000000000000000), (111173496477 / 25000000000000000000000000000000)⟩
lemma CA3_4_9I2R1MassTermLog_sound : CA3_4_9I2R1MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R1Mass_sound) (w := CA3_4_9I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I2R1MassTerm : Ball := ⟨(808155752653246679917399297 / 50000000000000000000000000000000), (26337 / 5000000000000000000000000000000)⟩
lemma CA3_4_9I2R1MassTerm_sound : CA3_4_9I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R1Mass_sound) CA3_4_9I2R1MassTermLog_sound) (by decide +kernel)
def CA3_4_9I2R1H : Ball := ⟨(5131182270670974012217607 / 6250000000000000000000000000000), (269641 / 25000000000000000000000000000000)⟩
lemma CA3_4_9I2R1H_sound : CA3_4_9I2R1H.Encloses (homogeneousEntropy CA3_4_9I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R1Value CA3_4_9I2R1MassTerm_sound CA3_4_9I2R1Entropy_sound) (by decide +kernel)
def CA3_4_9I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA3_4_9I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA3_4_9I2R2Raw_sound (a : PairSlot) :
    (CA3_4_9I2R2Raw a).Encloses (CA3_4_9I2R2Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA3_4_9I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2662620585721420017024656709 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(118808483387719070591604441351 / 100000000000000000000000000000000), (39468239 / 100000000000000000000000000000000)⟩ ⟨(-892417673211436333438693782157249 / 100000000000000000000000000000000), (296461539073 / 100000000000000000000000000000000)⟩ ⟨-13, 2662620585721420017024656709, 2441406250000000000000000000⟩,
   .log ⟨(903945099847381946666593881 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(10498338947010504097231655437 / 100000000000000000000000000000000), (1722767 / 50000000000000000000000000000000)⟩ ⟨(-1161391211566166657234958092089781 / 100000000000000000000000000000000), (381164936919 / 100000000000000000000000000000000)⟩ ⟨-17, 903945099847381946666593881, 762939453125000000000000000⟩,
   .log ⟨(12130784726064703499147662307 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(370274477774716566427238229337 / 100000000000000000000000000000000), (33394321 / 25000000000000000000000000000000)⟩ ⟨(-381544234499448311559192971659527 / 50000000000000000000000000000000), (275285712001 / 100000000000000000000000000000000)⟩ ⟨-12, 12130784726064703499147662307, 6103515625000000000000000000⟩]
lemma CA3_4_9I2R2Certificates_valid :
    CA3_4_9I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA3_4_9I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R2Certificates (CA3_4_9I2R2CertificateIndex a)).input
lemma CA3_4_9I2R2P_check : ∀ a : PairSlot, contains (CA3_4_9I2R2Raw a) (CA3_4_9I2R2P a) = true := by
  decide +kernel
lemma CA3_4_9I2R2P_sound (a : PairSlot) :
    (CA3_4_9I2R2P a).Encloses (CA3_4_9I2R2Value a) :=
  contains_sound (CA3_4_9I2R2Raw_sound a) (CA3_4_9I2R2P_check a)
def CA3_4_9I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R2Certificates (CA3_4_9I2R2CertificateIndex a)).output
lemma CA3_4_9I2R2Terms_sound (a : PairSlot) :
    (CA3_4_9I2R2Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R2Certificates_valid
    (CA3_4_9I2R2CertificateIndex a) (CA3_4_9I2R2P_sound a)
def CA3_4_9I2R2Entropy : Ball := ⟨(628888122444175715804910422913 / 100000000000000000000000000000000), (21940483 / 10000000000000000000000000000000)⟩
lemma CA3_4_9I2R2Entropy_sound : CA3_4_9I2R2Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R2Value CA3_4_9I2R2Terms CA3_4_9I2R2Terms_sound) (by decide +kernel)
def CA3_4_9I2R2Mass : Ball := ⟨(961965437014597225752130051 / 1250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I2R2Mass_sound : CA3_4_9I2R2Mass.Encloses (∑ a, CA3_4_9I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R2P CA3_4_9I2R2Value CA3_4_9I2R2P_sound) (by decide +kernel)
def CA3_4_9I2R2MassTermLogWitness : LogWitness := ⟨-11, 961965437014597225752130051, 610351562500000000000000000⟩
def CA3_4_9I2R2MassTermLog : Ball := ⟨(-716967558751746717927349993101709 / 100000000000000000000000000000000), (31763736499 / 12500000000000000000000000000000)⟩
lemma CA3_4_9I2R2MassTermLog_sound : CA3_4_9I2R2MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R2Mass_sound) (w := CA3_4_9I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I2R2MassTerm : Ball := ⟨(4310612568624455895852198643 / 781250000000000000000000000000), (19555599 / 10000000000000000000000000000000)⟩
lemma CA3_4_9I2R2MassTerm_sound : CA3_4_9I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R2Mass_sound) CA3_4_9I2R2MassTermLog_sound) (by decide +kernel)
def CA3_4_9I2R2H : Ball := ⟨(77129713660245361135828996609 / 100000000000000000000000000000000), (20748041 / 5000000000000000000000000000000)⟩
lemma CA3_4_9I2R2H_sound : CA3_4_9I2R2H.Encloses (homogeneousEntropy CA3_4_9I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R2Value CA3_4_9I2R2MassTerm_sound CA3_4_9I2R2Entropy_sound) (by decide +kernel)
def CA3_4_9I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA3_4_9I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA3_4_9I2R3Raw_sound (a : PairSlot) :
    (CA3_4_9I2R3Raw a).Encloses (CA3_4_9I2R3Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA3_4_9I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(63065380170987248489996400911 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(464713240624695623579038050939 / 100000000000000000000000000000000), (80127687 / 50000000000000000000000000000000)⟩ ⟨(-147375069924174797158524850477827 / 20000000000000000000000000000000), (254109885781 / 100000000000000000000000000000000)⟩ ⟨-11, 63065380170987248489996400911, 48828125000000000000000000000⟩,
   .log ⟨(445344646416109351263041104079 / 20000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩ ⟨(2117969559395514344629812661969 / 25000000000000000000000000000000), (1650344481 / 50000000000000000000000000000000)⟩ ⟨(-380463908380132535544902353615437 / 100000000000000000000000000000000), (37057691591 / 25000000000000000000000000000000)⟩ ⟨-6, 445344646416109351263041104079, 312500000000000000000000000000⟩,
   .log ⟨(113396433956510867113178585959 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(153811728604174436385946652067 / 20000000000000000000000000000000), (132069463 / 50000000000000000000000000000000)⟩ ⟨(-339101776038132304026122658759803 / 50000000000000000000000000000000), (116467030697 / 50000000000000000000000000000000)⟩ ⟨-10, 113396433956510867113178585959, 97656250000000000000000000000⟩]
lemma CA3_4_9I2R3Certificates_valid :
    CA3_4_9I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA3_4_9I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R3Certificates (CA3_4_9I2R3CertificateIndex a)).input
lemma CA3_4_9I2R3P_check : ∀ a : PairSlot, contains (CA3_4_9I2R3Raw a) (CA3_4_9I2R3P a) = true := by
  decide +kernel
lemma CA3_4_9I2R3P_sound (a : PairSlot) :
    (CA3_4_9I2R3P a).Encloses (CA3_4_9I2R3Value a) :=
  contains_sound (CA3_4_9I2R3Raw_sound a) (CA3_4_9I2R3P_check a)
def CA3_4_9I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R3Certificates (CA3_4_9I2R3CertificateIndex a)).output
lemma CA3_4_9I2R3Terms_sound (a : PairSlot) :
    (CA3_4_9I2R3Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R3Certificates_valid
    (CA3_4_9I2R3CertificateIndex a) (CA3_4_9I2R3P_sound a)
def CA3_4_9I2R3Entropy : Ball := ⟨(194113002424552503680560439183 / 1000000000000000000000000000000), (1862541631 / 25000000000000000000000000000000)⟩
lemma CA3_4_9I2R3Entropy_sound : CA3_4_9I2R3Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R3Value CA3_4_9I2R3Terms CA3_4_9I2R3Terms_sound) (by decide +kernel)
def CA3_4_9I2R3Mass : Ball := ⟨(480637009241608974383676101453 / 10000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
lemma CA3_4_9I2R3Mass_sound : CA3_4_9I2R3Mass.Encloses (∑ a, CA3_4_9I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R3P CA3_4_9I2R3Value CA3_4_9I2R3P_sound) (by decide +kernel)
def CA3_4_9I2R3MassTermLogWitness : LogWitness := ⟨-5, 480637009241608974383676101453, 312500000000000000000000000000⟩
def CA3_4_9I2R3MassTermLog : Ball := ⟨(-303522804530987493211666450419657 / 100000000000000000000000000000000), (63527471361 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I2R3MassTermLog_sound : CA3_4_9I2R3MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R3Mass_sound) (w := CA3_4_9I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I2R3MassTerm : Ball := ⟨(7294214650319965502922602621079 / 50000000000000000000000000000000), (305336543 / 5000000000000000000000000000000)⟩
lemma CA3_4_9I2R3MassTerm_sound : CA3_4_9I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R3Mass_sound) CA3_4_9I2R3MassTermLog_sound) (by decide +kernel)
def CA3_4_9I2R3H : Ball := ⟨(2411435470907659681105419338071 / 50000000000000000000000000000000), (1694612173 / 12500000000000000000000000000000)⟩
lemma CA3_4_9I2R3H_sound : CA3_4_9I2R3H.Encloses (homogeneousEntropy CA3_4_9I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R3Value CA3_4_9I2R3MassTerm_sound CA3_4_9I2R3Entropy_sound) (by decide +kernel)
def CA3_4_9I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA3_4_9I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA3_4_9I2R4Raw_sound (a : PairSlot) :
    (CA3_4_9I2R4Raw a).Encloses (CA3_4_9I2R4Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA3_4_9I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(4623100515197636596302359599 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(85885304912106424752106925081 / 100000000000000000000000000000000), (29369399 / 100000000000000000000000000000000)⟩ ⟨(-116108908715284072767299146936791 / 12500000000000000000000000000000), (15881868303 / 5000000000000000000000000000000)⟩ ⟨-14, 4623100515197636596302359599, 3051757812500000000000000000⟩,
   .log ⟨(1611521471481617569636159217241 / 50000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩ ⟨(2767662637555370849218275890653 / 25000000000000000000000000000000), (4095035417 / 100000000000000000000000000000000)⟩ ⟨(-171742212966657406520456083400811 / 50000000000000000000000000000000), (127054942593 / 100000000000000000000000000000000)⟩ ⟨-5, 1611521471481617569636159217241, 1562500000000000000000000000000⟩,
   .log ⟨(8391789291930128613674735173291 / 25000000000000000000000000000000), (13 / 12500000000000000000000000000000)⟩ ⟨(36642649332842067791324251940707 / 100000000000000000000000000000000), (2132436627 / 10000000000000000000000000000000)⟩ ⟨(-10916220622960310255925014085969 / 10000000000000000000000000000000), (31763735679 / 50000000000000000000000000000000)⟩ ⟨-2, 8391789291930128613674735173291, 6250000000000000000000000000000⟩,
   .log ⟨(31217071843515331933395889141 / 2000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(1623263285052397325525672402621 / 25000000000000000000000000000000), (1322094437 / 50000000000000000000000000000000)⟩ ⟨(-415993733990036605144244965066989 / 100000000000000000000000000000000), (21175823739 / 12500000000000000000000000000000)⟩ ⟨-7, 31217071843515331933395889141, 15625000000000000000000000000⟩,
   .log ⟨(743390276070452316441660391 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(535559867148594134063805993269 / 100000000000000000000000000000000), (94451413 / 50000000000000000000000000000000)⟩ ⟨(-720428938053311645075035565753419 / 100000000000000000000000000000000), (254109885541 / 100000000000000000000000000000000)⟩ ⟨-11, 743390276070452316441660391, 488281250000000000000000000⟩]
lemma CA3_4_9I2R4Certificates_valid :
    CA3_4_9I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA3_4_9I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R4Certificates (CA3_4_9I2R4CertificateIndex a)).input
lemma CA3_4_9I2R4P_check : ∀ a : PairSlot, contains (CA3_4_9I2R4Raw a) (CA3_4_9I2R4P a) = true := by
  decide +kernel
lemma CA3_4_9I2R4P_sound (a : PairSlot) :
    (CA3_4_9I2R4P a).Encloses (CA3_4_9I2R4Value a) :=
  contains_sound (CA3_4_9I2R4Raw_sound a) (CA3_4_9I2R4P_check a)
def CA3_4_9I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R4Certificates (CA3_4_9I2R4CertificateIndex a)).output
lemma CA3_4_9I2R4Terms_sound (a : PairSlot) :
    (CA3_4_9I2R4Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R4Certificates_valid
    (CA3_4_9I2R4CertificateIndex a) (CA3_4_9I2R4P_sound a)
def CA3_4_9I2R4Entropy : Ball := ⟨(7247738719067702017284385813033 / 10000000000000000000000000000000), (8762614119 / 25000000000000000000000000000000)⟩
lemma CA3_4_9I2R4Entropy_sound : CA3_4_9I2R4Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R4Value CA3_4_9I2R4Terms CA3_4_9I2R4Terms_sound) (by decide +kernel)
def CA3_4_9I2R4Mass : Ball := ⟨(10806945416916588426153135488431 / 25000000000000000000000000000000), (153 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I2R4Mass_sound : CA3_4_9I2R4Mass.Encloses (∑ a, CA3_4_9I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R4P CA3_4_9I2R4Value CA3_4_9I2R4P_sound) (by decide +kernel)
def CA3_4_9I2R4MassTermLogWitness : LogWitness := ⟨-2, 10806945416916588426153135488431, 6250000000000000000000000000000⟩
def CA3_4_9I2R4MassTermLog : Ball := ⟨(-41934340163775995053156294938029 / 50000000000000000000000000000000), (63527471403 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I2R4MassTermLog_sound : CA3_4_9I2R4MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R4Mass_sound) (w := CA3_4_9I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I2R4MassTerm : Ball := ⟨(9063642504886804196860635101949 / 25000000000000000000000000000000), (13730758383 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I2R4MassTerm_sound : CA3_4_9I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R4Mass_sound) CA3_4_9I2R4MassTermLog_sound) (by decide +kernel)
def CA3_4_9I2R4H : Ball := ⟨(18111408585564901692700658861267 / 50000000000000000000000000000000), (31255986621 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I2R4H_sound : CA3_4_9I2R4H.Encloses (homogeneousEntropy CA3_4_9I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R4Value CA3_4_9I2R4MassTerm_sound CA3_4_9I2R4Entropy_sound) (by decide +kernel)
def CA3_4_9I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA3_4_9I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA3_4_9I2R5Raw_sound (a : PairSlot) :
    (CA3_4_9I2R5Raw a).Encloses (CA3_4_9I2R5Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA3_4_9I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(7272508322125620575782948437 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(236866464334893733212117780143 / 100000000000000000000000000000000), (40040357 / 50000000000000000000000000000000)⟩ ⟨(-203563246203393495460811346542017 / 25000000000000000000000000000000), (68821427829 / 25000000000000000000000000000000)⟩ ⟨-12, 7272508322125620575782948437, 6103515625000000000000000000⟩,
   .log ⟨(17592763981361906146979831159223 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩ ⟨(7642659550239816707168560158683 / 25000000000000000000000000000000), (14901650853 / 100000000000000000000000000000000)⟩ ⟨(-34753650118135338438594227075673 / 20000000000000000000000000000000), (84703294993 / 100000000000000000000000000000000)⟩ ⟨-3, 17592763981361906146979831159223, 12500000000000000000000000000000⟩,
   .log ⟨(328839673074914029910480820183 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(3304317811514671185683979148613 / 100000000000000000000000000000000), (1253421187 / 100000000000000000000000000000000)⟩ ⟨(-502420796830360528557032476853169 / 100000000000000000000000000000000), (190582413603 / 100000000000000000000000000000000)⟩ ⟨-8, 328839673074914029910480820183, 195312500000000000000000000000⟩]
lemma CA3_4_9I2R5Certificates_valid :
    CA3_4_9I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA3_4_9I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R5Certificates (CA3_4_9I2R5CertificateIndex a)).input
lemma CA3_4_9I2R5P_check : ∀ a : PairSlot, contains (CA3_4_9I2R5Raw a) (CA3_4_9I2R5P a) = true := by
  decide +kernel
lemma CA3_4_9I2R5P_sound (a : PairSlot) :
    (CA3_4_9I2R5P a).Encloses (CA3_4_9I2R5Value a) :=
  contains_sound (CA3_4_9I2R5Raw_sound a) (CA3_4_9I2R5P_check a)
def CA3_4_9I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R5Certificates (CA3_4_9I2R5CertificateIndex a)).output
lemma CA3_4_9I2R5Terms_sound (a : PairSlot) :
    (CA3_4_9I2R5Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R5Certificates_valid
    (CA3_4_9I2R5CertificateIndex a) (CA3_4_9I2R5P_sound a)
def CA3_4_9I2R5Entropy : Ball := ⟨(1065994452400275992111573048859 / 1562500000000000000000000000000), (8117576377 / 25000000000000000000000000000000)⟩
lemma CA3_4_9I2R5Entropy_sound : CA3_4_9I2R5Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R5Value CA3_4_9I2R5Terms CA3_4_9I2R5Terms_sound) (by decide +kernel)
def CA3_4_9I2R5Mass : Ball := ⟨(18279533360800236689103924593337 / 50000000000000000000000000000000), (1 / 1000000000000000000000000000000)⟩
lemma CA3_4_9I2R5Mass_sound : CA3_4_9I2R5Mass.Encloses (∑ a, CA3_4_9I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R5P CA3_4_9I2R5Value CA3_4_9I2R5P_sound) (by decide +kernel)
def CA3_4_9I2R5MassTermLogWitness : LogWitness := ⟨-2, 18279533360800236689103924593337, 12500000000000000000000000000000⟩
def CA3_4_9I2R5MassTermLog : Ball := ⟨(-100624096703649036266445403338169 / 100000000000000000000000000000000), (31763735661 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I2R5MassTermLog_sound : CA3_4_9I2R5MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R5Mass_sound) (w := CA3_4_9I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I2R5MassTerm : Ball := ⟨(36787230651894833723090796725369 / 100000000000000000000000000000000), (2903131341 / 12500000000000000000000000000000)⟩
lemma CA3_4_9I2R5MassTerm_sound : CA3_4_9I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R5Mass_sound) CA3_4_9I2R5MassTermLog_sound) (by decide +kernel)
def CA3_4_9I2R5H : Ball := ⟨(31436414301722829772049878401607 / 100000000000000000000000000000000), (13923839059 / 25000000000000000000000000000000)⟩
lemma CA3_4_9I2R5H_sound : CA3_4_9I2R5H.Encloses (homogeneousEntropy CA3_4_9I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R5Value CA3_4_9I2R5MassTerm_sound CA3_4_9I2R5Entropy_sound) (by decide +kernel)
def CA3_4_9I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA3_4_9I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA3_4_9I2R6Raw_sound (a : PairSlot) :
    (CA3_4_9I2R6Raw a).Encloses (CA3_4_9I2R6Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA3_4_9I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(21998567971416970171570656021 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(185270797860241581996859903193 / 100000000000000000000000000000000), (32608651 / 50000000000000000000000000000000)⟩ ⟨(-421097405296941091625585047822189 / 50000000000000000000000000000000), (296461536107 / 100000000000000000000000000000000)⟩ ⟨-13, 21998567971416970171570656021, 12207031250000000000000000000⟩,
   .log ⟨(1385997100016570164729329 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(25078593183583505991673963 / 100000000000000000000000000000000), (4119 / 50000000000000000000000000000000)⟩ ⟨(-452356523388174497394634131179329 / 25000000000000000000000000000000), (592995213347 / 100000000000000000000000000000000)⟩ ⟨-27, 1385997100016570164729329, 745058059692382812500000⟩,
   .log ⟨(1153366528626991987959968739203 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(2173714097963675283279431707373 / 25000000000000000000000000000000), (3419288129 / 100000000000000000000000000000000)⟩ ⟨(-188466896169714658507801571192217 / 50000000000000000000000000000000), (148230766257 / 100000000000000000000000000000000)⟩ ⟨-6, 1153366528626991987959968739203, 781250000000000000000000000000⟩]
lemma CA3_4_9I2R6Certificates_valid :
    CA3_4_9I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA3_4_9I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R6Certificates (CA3_4_9I2R6CertificateIndex a)).input
lemma CA3_4_9I2R6P_check : ∀ a : PairSlot, contains (CA3_4_9I2R6Raw a) (CA3_4_9I2R6P a) = true := by
  decide +kernel
lemma CA3_4_9I2R6P_sound (a : PairSlot) :
    (CA3_4_9I2R6P a).Encloses (CA3_4_9I2R6Value a) :=
  contains_sound (CA3_4_9I2R6Raw_sound a) (CA3_4_9I2R6P_check a)
def CA3_4_9I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R6Certificates (CA3_4_9I2R6CertificateIndex a)).output
lemma CA3_4_9I2R6Terms_sound (a : PairSlot) :
    (CA3_4_9I2R6Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R6Certificates_valid
    (CA3_4_9I2R6CertificateIndex a) (CA3_4_9I2R6P_sound a)
def CA3_4_9I2R6Entropy : Ball := ⟨(2266362036190387866030857495951 / 25000000000000000000000000000000), (3549739209 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I2R6Entropy_sound : CA3_4_9I2R6Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R6Value CA3_4_9I2R6Terms CA3_4_9I2R6Terms_sound) (by decide +kernel)
def CA3_4_9I2R6Mass : Ball := ⟨(1175366482595508974701704124553 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
lemma CA3_4_9I2R6Mass_sound : CA3_4_9I2R6Mass.Encloses (∑ a, CA3_4_9I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R6P CA3_4_9I2R6Value CA3_4_9I2R6P_sound) (by decide +kernel)
def CA3_4_9I2R6MassTermLogWitness : LogWitness := ⟨-6, 1175366482595508974701704124553, 781250000000000000000000000000⟩
def CA3_4_9I2R6MassTermLog : Ball := ⟨(-375044300638145820613044638924319 / 100000000000000000000000000000000), (148230766419 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I2R6MassTermLog_sound : CA3_4_9I2R6MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R6Mass_sound) (w := CA3_4_9I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I2R6MassTerm : Ball := ⟨(88162900091710011023539451221 / 1000000000000000000000000000000), (871127387 / 25000000000000000000000000000000)⟩
lemma CA3_4_9I2R6MassTerm_sound : CA3_4_9I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R6Mass_sound) CA3_4_9I2R6MassTermLog_sound) (by decide +kernel)
def CA3_4_9I2R6H : Ball := ⟨(31144766948818795221185607713 / 12500000000000000000000000000000), (7034248757 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I2R6H_sound : CA3_4_9I2R6H.Encloses (homogeneousEntropy CA3_4_9I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R6Value CA3_4_9I2R6MassTerm_sound CA3_4_9I2R6Entropy_sound) (by decide +kernel)
def CA3_4_9I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA3_4_9I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA3_4_9I2R7Raw_sound (a : PairSlot) :
    (CA3_4_9I2R7Raw a).Encloses (CA3_4_9I2R7Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA3_4_9I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I2R7Certificates_valid :
    CA3_4_9I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R7Certificates (CA3_4_9I2R7CertificateIndex a)).input
lemma CA3_4_9I2R7P_check : ∀ a : PairSlot, contains (CA3_4_9I2R7Raw a) (CA3_4_9I2R7P a) = true := by
  decide +kernel
lemma CA3_4_9I2R7P_sound (a : PairSlot) :
    (CA3_4_9I2R7P a).Encloses (CA3_4_9I2R7Value a) :=
  contains_sound (CA3_4_9I2R7Raw_sound a) (CA3_4_9I2R7P_check a)
def CA3_4_9I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R7Certificates (CA3_4_9I2R7CertificateIndex a)).output
lemma CA3_4_9I2R7Terms_sound (a : PairSlot) :
    (CA3_4_9I2R7Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R7Certificates_valid
    (CA3_4_9I2R7CertificateIndex a) (CA3_4_9I2R7P_sound a)
def CA3_4_9I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R7Entropy_sound : CA3_4_9I2R7Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R7Value CA3_4_9I2R7Terms CA3_4_9I2R7Terms_sound) (by decide +kernel)
def CA3_4_9I2R7Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R7Mass_sound : CA3_4_9I2R7Mass.Encloses (∑ a, CA3_4_9I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R7P CA3_4_9I2R7Value CA3_4_9I2R7P_sound) (by decide +kernel)
def CA3_4_9I2R7MassTerm : Ball := .exact 0
lemma CA3_4_9I2R7MassTerm_sound : CA3_4_9I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R7Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R7Mass_sound)
def CA3_4_9I2R7H : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R7H_sound : CA3_4_9I2R7H.Encloses (homogeneousEntropy CA3_4_9I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R7Value CA3_4_9I2R7MassTerm_sound CA3_4_9I2R7Entropy_sound) (by decide +kernel)
def CA3_4_9I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA3_4_9I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA3_4_9I2R8Raw_sound (a : PairSlot) :
    (CA3_4_9I2R8Raw a).Encloses (CA3_4_9I2R8Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA3_4_9I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I2R8Certificates_valid :
    CA3_4_9I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R8Certificates (CA3_4_9I2R8CertificateIndex a)).input
lemma CA3_4_9I2R8P_check : ∀ a : PairSlot, contains (CA3_4_9I2R8Raw a) (CA3_4_9I2R8P a) = true := by
  decide +kernel
lemma CA3_4_9I2R8P_sound (a : PairSlot) :
    (CA3_4_9I2R8P a).Encloses (CA3_4_9I2R8Value a) :=
  contains_sound (CA3_4_9I2R8Raw_sound a) (CA3_4_9I2R8P_check a)
def CA3_4_9I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R8Certificates (CA3_4_9I2R8CertificateIndex a)).output
lemma CA3_4_9I2R8Terms_sound (a : PairSlot) :
    (CA3_4_9I2R8Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R8Certificates_valid
    (CA3_4_9I2R8CertificateIndex a) (CA3_4_9I2R8P_sound a)
def CA3_4_9I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R8Entropy_sound : CA3_4_9I2R8Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R8Value CA3_4_9I2R8Terms CA3_4_9I2R8Terms_sound) (by decide +kernel)
def CA3_4_9I2R8Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R8Mass_sound : CA3_4_9I2R8Mass.Encloses (∑ a, CA3_4_9I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R8P CA3_4_9I2R8Value CA3_4_9I2R8P_sound) (by decide +kernel)
def CA3_4_9I2R8MassTerm : Ball := .exact 0
lemma CA3_4_9I2R8MassTerm_sound : CA3_4_9I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R8Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R8Mass_sound)
def CA3_4_9I2R8H : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R8H_sound : CA3_4_9I2R8H.Encloses (homogeneousEntropy CA3_4_9I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R8Value CA3_4_9I2R8MassTerm_sound CA3_4_9I2R8Entropy_sound) (by decide +kernel)
def CA3_4_9I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA3_4_9I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA3_4_9I2R9Raw_sound (a : PairSlot) :
    (CA3_4_9I2R9Raw a).Encloses (CA3_4_9I2R9Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA3_4_9I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I2R9Certificates_valid :
    CA3_4_9I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R9Certificates (CA3_4_9I2R9CertificateIndex a)).input
lemma CA3_4_9I2R9P_check : ∀ a : PairSlot, contains (CA3_4_9I2R9Raw a) (CA3_4_9I2R9P a) = true := by
  decide +kernel
lemma CA3_4_9I2R9P_sound (a : PairSlot) :
    (CA3_4_9I2R9P a).Encloses (CA3_4_9I2R9Value a) :=
  contains_sound (CA3_4_9I2R9Raw_sound a) (CA3_4_9I2R9P_check a)
def CA3_4_9I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R9Certificates (CA3_4_9I2R9CertificateIndex a)).output
lemma CA3_4_9I2R9Terms_sound (a : PairSlot) :
    (CA3_4_9I2R9Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R9Certificates_valid
    (CA3_4_9I2R9CertificateIndex a) (CA3_4_9I2R9P_sound a)
def CA3_4_9I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R9Entropy_sound : CA3_4_9I2R9Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R9Value CA3_4_9I2R9Terms CA3_4_9I2R9Terms_sound) (by decide +kernel)
def CA3_4_9I2R9Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R9Mass_sound : CA3_4_9I2R9Mass.Encloses (∑ a, CA3_4_9I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R9P CA3_4_9I2R9Value CA3_4_9I2R9P_sound) (by decide +kernel)
def CA3_4_9I2R9MassTerm : Ball := .exact 0
lemma CA3_4_9I2R9MassTerm_sound : CA3_4_9I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R9Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R9Mass_sound)
def CA3_4_9I2R9H : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R9H_sound : CA3_4_9I2R9H.Encloses (homogeneousEntropy CA3_4_9I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R9Value CA3_4_9I2R9MassTerm_sound CA3_4_9I2R9Entropy_sound) (by decide +kernel)
def CA3_4_9I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA3_4_9I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA3_4_9I2R10Raw_sound (a : PairSlot) :
    (CA3_4_9I2R10Raw a).Encloses (CA3_4_9I2R10Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA3_4_9I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I2R10Certificates_valid :
    CA3_4_9I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R10Certificates (CA3_4_9I2R10CertificateIndex a)).input
lemma CA3_4_9I2R10P_check : ∀ a : PairSlot, contains (CA3_4_9I2R10Raw a) (CA3_4_9I2R10P a) = true := by
  decide +kernel
lemma CA3_4_9I2R10P_sound (a : PairSlot) :
    (CA3_4_9I2R10P a).Encloses (CA3_4_9I2R10Value a) :=
  contains_sound (CA3_4_9I2R10Raw_sound a) (CA3_4_9I2R10P_check a)
def CA3_4_9I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R10Certificates (CA3_4_9I2R10CertificateIndex a)).output
lemma CA3_4_9I2R10Terms_sound (a : PairSlot) :
    (CA3_4_9I2R10Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R10Certificates_valid
    (CA3_4_9I2R10CertificateIndex a) (CA3_4_9I2R10P_sound a)
def CA3_4_9I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R10Entropy_sound : CA3_4_9I2R10Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R10Value CA3_4_9I2R10Terms CA3_4_9I2R10Terms_sound) (by decide +kernel)
def CA3_4_9I2R10Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R10Mass_sound : CA3_4_9I2R10Mass.Encloses (∑ a, CA3_4_9I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R10P CA3_4_9I2R10Value CA3_4_9I2R10P_sound) (by decide +kernel)
def CA3_4_9I2R10MassTerm : Ball := .exact 0
lemma CA3_4_9I2R10MassTerm_sound : CA3_4_9I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R10Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R10Mass_sound)
def CA3_4_9I2R10H : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R10H_sound : CA3_4_9I2R10H.Encloses (homogeneousEntropy CA3_4_9I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R10Value CA3_4_9I2R10MassTerm_sound CA3_4_9I2R10Entropy_sound) (by decide +kernel)
def CA3_4_9I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA3_4_9I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA3_4_9I2R11Raw_sound (a : PairSlot) :
    (CA3_4_9I2R11Raw a).Encloses (CA3_4_9I2R11Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA3_4_9I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I2R11Certificates_valid :
    CA3_4_9I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R11Certificates (CA3_4_9I2R11CertificateIndex a)).input
lemma CA3_4_9I2R11P_check : ∀ a : PairSlot, contains (CA3_4_9I2R11Raw a) (CA3_4_9I2R11P a) = true := by
  decide +kernel
lemma CA3_4_9I2R11P_sound (a : PairSlot) :
    (CA3_4_9I2R11P a).Encloses (CA3_4_9I2R11Value a) :=
  contains_sound (CA3_4_9I2R11Raw_sound a) (CA3_4_9I2R11P_check a)
def CA3_4_9I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R11Certificates (CA3_4_9I2R11CertificateIndex a)).output
lemma CA3_4_9I2R11Terms_sound (a : PairSlot) :
    (CA3_4_9I2R11Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R11Certificates_valid
    (CA3_4_9I2R11CertificateIndex a) (CA3_4_9I2R11P_sound a)
def CA3_4_9I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R11Entropy_sound : CA3_4_9I2R11Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R11Value CA3_4_9I2R11Terms CA3_4_9I2R11Terms_sound) (by decide +kernel)
def CA3_4_9I2R11Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R11Mass_sound : CA3_4_9I2R11Mass.Encloses (∑ a, CA3_4_9I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R11P CA3_4_9I2R11Value CA3_4_9I2R11P_sound) (by decide +kernel)
def CA3_4_9I2R11MassTerm : Ball := .exact 0
lemma CA3_4_9I2R11MassTerm_sound : CA3_4_9I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R11Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R11Mass_sound)
def CA3_4_9I2R11H : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R11H_sound : CA3_4_9I2R11H.Encloses (homogeneousEntropy CA3_4_9I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R11Value CA3_4_9I2R11MassTerm_sound CA3_4_9I2R11Entropy_sound) (by decide +kernel)
def CA3_4_9I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA3_4_9I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA3_4_9I2R12Raw_sound (a : PairSlot) :
    (CA3_4_9I2R12Raw a).Encloses (CA3_4_9I2R12Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA3_4_9I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I2R12Certificates_valid :
    CA3_4_9I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R12Certificates (CA3_4_9I2R12CertificateIndex a)).input
lemma CA3_4_9I2R12P_check : ∀ a : PairSlot, contains (CA3_4_9I2R12Raw a) (CA3_4_9I2R12P a) = true := by
  decide +kernel
lemma CA3_4_9I2R12P_sound (a : PairSlot) :
    (CA3_4_9I2R12P a).Encloses (CA3_4_9I2R12Value a) :=
  contains_sound (CA3_4_9I2R12Raw_sound a) (CA3_4_9I2R12P_check a)
def CA3_4_9I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R12Certificates (CA3_4_9I2R12CertificateIndex a)).output
lemma CA3_4_9I2R12Terms_sound (a : PairSlot) :
    (CA3_4_9I2R12Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R12Certificates_valid
    (CA3_4_9I2R12CertificateIndex a) (CA3_4_9I2R12P_sound a)
def CA3_4_9I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R12Entropy_sound : CA3_4_9I2R12Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R12Value CA3_4_9I2R12Terms CA3_4_9I2R12Terms_sound) (by decide +kernel)
def CA3_4_9I2R12Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R12Mass_sound : CA3_4_9I2R12Mass.Encloses (∑ a, CA3_4_9I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R12P CA3_4_9I2R12Value CA3_4_9I2R12P_sound) (by decide +kernel)
def CA3_4_9I2R12MassTerm : Ball := .exact 0
lemma CA3_4_9I2R12MassTerm_sound : CA3_4_9I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R12Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R12Mass_sound)
def CA3_4_9I2R12H : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R12H_sound : CA3_4_9I2R12H.Encloses (homogeneousEntropy CA3_4_9I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R12Value CA3_4_9I2R12MassTerm_sound CA3_4_9I2R12Entropy_sound) (by decide +kernel)
def CA3_4_9I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA3_4_9I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA3_4_9I2R13Raw_sound (a : PairSlot) :
    (CA3_4_9I2R13Raw a).Encloses (CA3_4_9I2R13Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA3_4_9I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I2R13Certificates_valid :
    CA3_4_9I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R13Certificates (CA3_4_9I2R13CertificateIndex a)).input
lemma CA3_4_9I2R13P_check : ∀ a : PairSlot, contains (CA3_4_9I2R13Raw a) (CA3_4_9I2R13P a) = true := by
  decide +kernel
lemma CA3_4_9I2R13P_sound (a : PairSlot) :
    (CA3_4_9I2R13P a).Encloses (CA3_4_9I2R13Value a) :=
  contains_sound (CA3_4_9I2R13Raw_sound a) (CA3_4_9I2R13P_check a)
def CA3_4_9I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R13Certificates (CA3_4_9I2R13CertificateIndex a)).output
lemma CA3_4_9I2R13Terms_sound (a : PairSlot) :
    (CA3_4_9I2R13Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R13Certificates_valid
    (CA3_4_9I2R13CertificateIndex a) (CA3_4_9I2R13P_sound a)
def CA3_4_9I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R13Entropy_sound : CA3_4_9I2R13Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R13Value CA3_4_9I2R13Terms CA3_4_9I2R13Terms_sound) (by decide +kernel)
def CA3_4_9I2R13Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R13Mass_sound : CA3_4_9I2R13Mass.Encloses (∑ a, CA3_4_9I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R13P CA3_4_9I2R13Value CA3_4_9I2R13P_sound) (by decide +kernel)
def CA3_4_9I2R13MassTerm : Ball := .exact 0
lemma CA3_4_9I2R13MassTerm_sound : CA3_4_9I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R13Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R13Mass_sound)
def CA3_4_9I2R13H : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R13H_sound : CA3_4_9I2R13H.Encloses (homogeneousEntropy CA3_4_9I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R13Value CA3_4_9I2R13MassTerm_sound CA3_4_9I2R13Entropy_sound) (by decide +kernel)
def CA3_4_9I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA3_4_9I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA3_4_9I2R14Raw_sound (a : PairSlot) :
    (CA3_4_9I2R14Raw a).Encloses (CA3_4_9I2R14Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA3_4_9I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I2R14Certificates_valid :
    CA3_4_9I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R14Certificates (CA3_4_9I2R14CertificateIndex a)).input
lemma CA3_4_9I2R14P_check : ∀ a : PairSlot, contains (CA3_4_9I2R14Raw a) (CA3_4_9I2R14P a) = true := by
  decide +kernel
lemma CA3_4_9I2R14P_sound (a : PairSlot) :
    (CA3_4_9I2R14P a).Encloses (CA3_4_9I2R14Value a) :=
  contains_sound (CA3_4_9I2R14Raw_sound a) (CA3_4_9I2R14P_check a)
def CA3_4_9I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R14Certificates (CA3_4_9I2R14CertificateIndex a)).output
lemma CA3_4_9I2R14Terms_sound (a : PairSlot) :
    (CA3_4_9I2R14Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R14Certificates_valid
    (CA3_4_9I2R14CertificateIndex a) (CA3_4_9I2R14P_sound a)
def CA3_4_9I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R14Entropy_sound : CA3_4_9I2R14Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R14Value CA3_4_9I2R14Terms CA3_4_9I2R14Terms_sound) (by decide +kernel)
def CA3_4_9I2R14Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R14Mass_sound : CA3_4_9I2R14Mass.Encloses (∑ a, CA3_4_9I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R14P CA3_4_9I2R14Value CA3_4_9I2R14P_sound) (by decide +kernel)
def CA3_4_9I2R14MassTerm : Ball := .exact 0
lemma CA3_4_9I2R14MassTerm_sound : CA3_4_9I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R14Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R14Mass_sound)
def CA3_4_9I2R14H : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R14H_sound : CA3_4_9I2R14H.Encloses (homogeneousEntropy CA3_4_9I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R14Value CA3_4_9I2R14MassTerm_sound CA3_4_9I2R14Entropy_sound) (by decide +kernel)
def CA3_4_9I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA3_4_9I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA3_4_9I2R15Raw_sound (a : PairSlot) :
    (CA3_4_9I2R15Raw a).Encloses (CA3_4_9I2R15Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA3_4_9I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I2R15Certificates_valid :
    CA3_4_9I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R15Certificates (CA3_4_9I2R15CertificateIndex a)).input
lemma CA3_4_9I2R15P_check : ∀ a : PairSlot, contains (CA3_4_9I2R15Raw a) (CA3_4_9I2R15P a) = true := by
  decide +kernel
lemma CA3_4_9I2R15P_sound (a : PairSlot) :
    (CA3_4_9I2R15P a).Encloses (CA3_4_9I2R15Value a) :=
  contains_sound (CA3_4_9I2R15Raw_sound a) (CA3_4_9I2R15P_check a)
def CA3_4_9I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R15Certificates (CA3_4_9I2R15CertificateIndex a)).output
lemma CA3_4_9I2R15Terms_sound (a : PairSlot) :
    (CA3_4_9I2R15Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R15Certificates_valid
    (CA3_4_9I2R15CertificateIndex a) (CA3_4_9I2R15P_sound a)
def CA3_4_9I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R15Entropy_sound : CA3_4_9I2R15Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R15Value CA3_4_9I2R15Terms CA3_4_9I2R15Terms_sound) (by decide +kernel)
def CA3_4_9I2R15Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R15Mass_sound : CA3_4_9I2R15Mass.Encloses (∑ a, CA3_4_9I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R15P CA3_4_9I2R15Value CA3_4_9I2R15P_sound) (by decide +kernel)
def CA3_4_9I2R15MassTerm : Ball := .exact 0
lemma CA3_4_9I2R15MassTerm_sound : CA3_4_9I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R15Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R15Mass_sound)
def CA3_4_9I2R15H : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R15H_sound : CA3_4_9I2R15H.Encloses (homogeneousEntropy CA3_4_9I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R15Value CA3_4_9I2R15MassTerm_sound CA3_4_9I2R15Entropy_sound) (by decide +kernel)
def CA3_4_9I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA3_4_9I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 4 9)) A3_4_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA3_4_9I2R16Raw_sound (a : PairSlot) :
    (CA3_4_9I2R16Raw a).Encloses (CA3_4_9I2R16Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA3_4_9I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_4_9I2R16Certificates_valid :
    CA3_4_9I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_4_9I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R16Certificates (CA3_4_9I2R16CertificateIndex a)).input
lemma CA3_4_9I2R16P_check : ∀ a : PairSlot, contains (CA3_4_9I2R16Raw a) (CA3_4_9I2R16P a) = true := by
  decide +kernel
lemma CA3_4_9I2R16P_sound (a : PairSlot) :
    (CA3_4_9I2R16P a).Encloses (CA3_4_9I2R16Value a) :=
  contains_sound (CA3_4_9I2R16Raw_sound a) (CA3_4_9I2R16P_check a)
def CA3_4_9I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I2R16Certificates (CA3_4_9I2R16CertificateIndex a)).output
lemma CA3_4_9I2R16Terms_sound (a : PairSlot) :
    (CA3_4_9I2R16Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R16Certificates_valid
    (CA3_4_9I2R16CertificateIndex a) (CA3_4_9I2R16P_sound a)
def CA3_4_9I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R16Entropy_sound : CA3_4_9I2R16Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R16Value CA3_4_9I2R16Terms CA3_4_9I2R16Terms_sound) (by decide +kernel)
def CA3_4_9I2R16Mass : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R16Mass_sound : CA3_4_9I2R16Mass.Encloses (∑ a, CA3_4_9I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R16P CA3_4_9I2R16Value CA3_4_9I2R16P_sound) (by decide +kernel)
def CA3_4_9I2R16MassTerm : Ball := .exact 0
lemma CA3_4_9I2R16MassTerm_sound : CA3_4_9I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R16Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R16Mass_sound)
def CA3_4_9I2R16H : Ball := ⟨0, 0⟩
lemma CA3_4_9I2R16H_sound : CA3_4_9I2R16H.Encloses (homogeneousEntropy CA3_4_9I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R16Value CA3_4_9I2R16MassTerm_sound CA3_4_9I2R16Entropy_sound) (by decide +kernel)
def CA3_4_9I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_4_9I2R0H
  | 1 => CA3_4_9I2R1H
  | 2 => CA3_4_9I2R2H
  | 3 => CA3_4_9I2R3H
  | 4 => CA3_4_9I2R4H
  | 5 => CA3_4_9I2R5H
  | 6 => CA3_4_9I2R6H
  | 7 => CA3_4_9I2R7H
  | 8 => CA3_4_9I2R8H
  | 9 => CA3_4_9I2R9H
  | 10 => CA3_4_9I2R10H
  | 11 => CA3_4_9I2R11H
  | 12 => CA3_4_9I2R12H
  | 13 => CA3_4_9I2R13H
  | 14 => CA3_4_9I2R14H
  | 15 => CA3_4_9I2R15H
  | 16 => CA3_4_9I2R16H
  | _ => (.exact 0)
lemma CA3_4_9I2ResidualEntropies_sound (k : Fin 17) :
    (CA3_4_9I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA3_4_9I2R0H_sound
  · exact CA3_4_9I2R1H_sound
  · exact CA3_4_9I2R2H_sound
  · exact CA3_4_9I2R3H_sound
  · exact CA3_4_9I2R4H_sound
  · exact CA3_4_9I2R5H_sound
  · exact CA3_4_9I2R6H_sound
  · exact CA3_4_9I2R7H_sound
  · exact CA3_4_9I2R8H_sound
  · exact CA3_4_9I2R9H_sound
  · exact CA3_4_9I2R10H_sound
  · exact CA3_4_9I2R11H_sound
  · exact CA3_4_9I2R12H_sound
  · exact CA3_4_9I2R13H_sound
  · exact CA3_4_9I2R14H_sound
  · exact CA3_4_9I2R15H_sound
  · exact CA3_4_9I2R16H_sound
def CA3_4_9I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | 3, 0, 5 => Z3_0_5H2H
  | _, _, _ => (.exact 0)
lemma CA3_4_9I2Singles_sound (u : Shape) (hu : u ∈ below (shape 3 4 9))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA3_4_9I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A3_4_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact Z2_0_6H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact Z3_0_5H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 4 1) by decide +kernel) hd |>.elim
def CA3_4_9I2Singleton : Ball := ⟨(15375045182343300175117354668423 / 100000000000000000000000000000000), (125676761 / 1000000000000000000000000000000)⟩
lemma CA3_4_9I2Singleton_sound : CA3_4_9I2Singleton.Encloses
    (singletonEntropy (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA3_4_9I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) CA3_4_9I2Singles_sound) (by decide +kernel)
def CA3_4_9I2Group : Ball := ⟨(88183517545178379153268898808731 / 100000000000000000000000000000000), (151782191103 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I2Group_sound : CA3_4_9I2Group.Encloses
    (groupedEntropy (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA3_4_9I2Singleton_sound
    (finSumBall_sound 17 CA3_4_9I2ResidualEntropies _ CA3_4_9I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA3_4_9I2H : Ball := ⟨(52743704500292451550178385388619 / 50000000000000000000000000000000), (438248317761 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I2_sound : CA3_4_9I2H.Encloses (stageACapacity (shape 3 4 9) 2) := by
  have hb := contains_sound (Ball.add_sound CA3_4_9I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA3_4_9I2Group_sound)))
    (show contains (.add CA3_4_9I2PairH (.neg (.mul (.exact 2) CA3_4_9I2Group))) CA3_4_9I2H = true by decide +kernel)
  unfold CA3_4_9I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
