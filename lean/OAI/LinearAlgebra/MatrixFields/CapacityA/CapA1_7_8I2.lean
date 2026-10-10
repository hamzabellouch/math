import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA1_7_8I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_7_8I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA1_7_8I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA1_7_8I2R0Raw_sound (a : PairSlot) :
    (CA1_7_8I2R0Raw a).Encloses (CA1_7_8I2R0Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA1_7_8I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(20055422158842954722213457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(154649177236918223514006467 / 50000000000000000000000000000000), (101943 / 100000000000000000000000000000000)⟩ ⟨(-1542218119489740070137408646605969 / 100000000000000000000000000000000), (254112377287 / 50000000000000000000000000000000)⟩ ⟨-23, 20055422158842954722213457, 11920928955078125000000000⟩]
lemma CA1_7_8I2R0Certificates_valid :
    CA1_7_8I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_7_8I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R0Certificates (CA1_7_8I2R0CertificateIndex a)).input
lemma CA1_7_8I2R0P_check : ∀ a : PairSlot, contains (CA1_7_8I2R0Raw a) (CA1_7_8I2R0P a) = true := by
  decide +kernel
lemma CA1_7_8I2R0P_sound (a : PairSlot) :
    (CA1_7_8I2R0P a).Encloses (CA1_7_8I2R0Value a) :=
  contains_sound (CA1_7_8I2R0Raw_sound a) (CA1_7_8I2R0P_check a)
def CA1_7_8I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R0Certificates (CA1_7_8I2R0CertificateIndex a)).output
lemma CA1_7_8I2R0Terms_sound (a : PairSlot) :
    (CA1_7_8I2R0Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R0Certificates_valid
    (CA1_7_8I2R0CertificateIndex a) (CA1_7_8I2R0P_sound a)
def CA1_7_8I2R0Entropy : Ball := ⟨(154649177236918223514006467 / 50000000000000000000000000000000), (101943 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R0Entropy_sound : CA1_7_8I2R0Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R0Value CA1_7_8I2R0Terms CA1_7_8I2R0Terms_sound) (by decide +kernel)
def CA1_7_8I2R0Mass : Ball := ⟨(20055422158842954722213457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R0Mass_sound : CA1_7_8I2R0Mass.Encloses (∑ a, CA1_7_8I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R0P CA1_7_8I2R0Value CA1_7_8I2R0P_sound) (by decide +kernel)
def CA1_7_8I2R0MassTermLogWitness : LogWitness := ⟨-23, 20055422158842954722213457, 11920928955078125000000000⟩
def CA1_7_8I2R0MassTermLog : Ball := ⟨(-1542218119489740070137408646605969 / 100000000000000000000000000000000), (254112377287 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I2R0MassTermLog_sound : CA1_7_8I2R0MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I2R0Mass_sound) (w := CA1_7_8I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I2R0MassTerm : Ball := ⟨(154649177236918223514006467 / 50000000000000000000000000000000), (101943 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R0MassTerm_sound : CA1_7_8I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I2R0Mass_sound) CA1_7_8I2R0MassTermLog_sound) (by decide +kernel)
def CA1_7_8I2R0H : Ball := ⟨0, (101943 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I2R0H_sound : CA1_7_8I2R0H.Encloses (homogeneousEntropy CA1_7_8I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R0Value CA1_7_8I2R0MassTerm_sound CA1_7_8I2R0Entropy_sound) (by decide +kernel)
def CA1_7_8I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA1_7_8I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA1_7_8I2R1Raw_sound (a : PairSlot) :
    (CA1_7_8I2R1Raw a).Encloses (CA1_7_8I2R1Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA1_7_8I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(500003178829468586018862723 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(26491739363016102819996227157 / 100000000000000000000000000000000), (4499897 / 50000000000000000000000000000000)⟩ ⟨(-1059662837545734601079131994385727 / 100000000000000000000000000000000), (35998904261 / 10000000000000000000000000000000)⟩ ⟨-16, 500003178829468586018862723, 305175781250000000000000000⟩]
lemma CA1_7_8I2R1Certificates_valid :
    CA1_7_8I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_7_8I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R1Certificates (CA1_7_8I2R1CertificateIndex a)).input
lemma CA1_7_8I2R1P_check : ∀ a : PairSlot, contains (CA1_7_8I2R1Raw a) (CA1_7_8I2R1P a) = true := by
  decide +kernel
lemma CA1_7_8I2R1P_sound (a : PairSlot) :
    (CA1_7_8I2R1P a).Encloses (CA1_7_8I2R1Value a) :=
  contains_sound (CA1_7_8I2R1Raw_sound a) (CA1_7_8I2R1P_check a)
def CA1_7_8I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R1Certificates (CA1_7_8I2R1CertificateIndex a)).output
lemma CA1_7_8I2R1Terms_sound (a : PairSlot) :
    (CA1_7_8I2R1Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R1Certificates_valid
    (CA1_7_8I2R1CertificateIndex a) (CA1_7_8I2R1P_sound a)
def CA1_7_8I2R1Entropy : Ball := ⟨(26491739363016102819996227157 / 50000000000000000000000000000000), (4499897 / 25000000000000000000000000000000)⟩
lemma CA1_7_8I2R1Entropy_sound : CA1_7_8I2R1Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R1Value CA1_7_8I2R1Terms CA1_7_8I2R1Terms_sound) (by decide +kernel)
def CA1_7_8I2R1Mass : Ball := ⟨(500003178829468586018862723 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I2R1Mass_sound : CA1_7_8I2R1Mass.Encloses (∑ a, CA1_7_8I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R1P CA1_7_8I2R1Value CA1_7_8I2R1P_sound) (by decide +kernel)
def CA1_7_8I2R1MassTermLogWitness : LogWitness := ⟨-15, 500003178829468586018862723, 305175781250000000000000000⟩
def CA1_7_8I2R1MassTermLog : Ball := ⟨(-990348119489740070137408801335397 / 100000000000000000000000000000000), (338813218927 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R1MassTermLog_sound : CA1_7_8I2R1MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I2R1Mass_sound) (w := CA1_7_8I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I2R1MassTerm : Ball := ⟨(49517720789265642780224169709 / 100000000000000000000000000000000), (16940789 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R1MassTerm_sound : CA1_7_8I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I2R1Mass_sound) CA1_7_8I2R1MassTermLog_sound) (by decide +kernel)
def CA1_7_8I2R1H : Ball := ⟨(693151587353312571953656921 / 20000000000000000000000000000000), (34940377 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R1H_sound : CA1_7_8I2R1H.Encloses (homogeneousEntropy CA1_7_8I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R1Value CA1_7_8I2R1MassTerm_sound CA1_7_8I2R1Entropy_sound) (by decide +kernel)
def CA1_7_8I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA1_7_8I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA1_7_8I2R2Raw_sound (a : PairSlot) :
    (CA1_7_8I2R2Raw a).Encloses (CA1_7_8I2R2Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA1_7_8I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(6901476119098818328803909913 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(93978800260295301886260632691 / 12500000000000000000000000000000), (257214233 / 100000000000000000000000000000000)⟩ ⟨(-170215035592572034258704923374733 / 25000000000000000000000000000000), (232934062323 / 100000000000000000000000000000000)⟩ ⟨-10, 6901476119098818328803909913, 6103515625000000000000000000⟩,
   .log ⟨(6637863771029997909709427399 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(118512261706038857164985553271 / 100000000000000000000000000000000), (9839359 / 25000000000000000000000000000000)⟩ ⟨(-223174702347893505751168115009279 / 25000000000000000000000000000000), (148230769547 / 50000000000000000000000000000000)⟩ ⟨-13, 6637863771029997909709427399, 6103515625000000000000000000⟩,
   .log ⟨(26331697140349175004496990337 / 6250000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(115218307755647618049893427511 / 5000000000000000000000000000000), (802937361 / 100000000000000000000000000000000)⟩ ⟨(-273478165738635879979847070629751 / 50000000000000000000000000000000), (95291206929 / 50000000000000000000000000000000)⟩ ⟨-8, 26331697140349175004496990337, 24414062500000000000000000000⟩]
lemma CA1_7_8I2R2Certificates_valid :
    CA1_7_8I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_7_8I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R2Certificates (CA1_7_8I2R2CertificateIndex a)).input
lemma CA1_7_8I2R2P_check : ∀ a : PairSlot, contains (CA1_7_8I2R2Raw a) (CA1_7_8I2R2P a) = true := by
  decide +kernel
lemma CA1_7_8I2R2P_sound (a : PairSlot) :
    (CA1_7_8I2R2P a).Encloses (CA1_7_8I2R2Value a) :=
  contains_sound (CA1_7_8I2R2Raw_sound a) (CA1_7_8I2R2P_check a)
def CA1_7_8I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R2Certificates (CA1_7_8I2R2CertificateIndex a)).output
lemma CA1_7_8I2R2Terms_sound (a : PairSlot) :
    (CA1_7_8I2R2Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R2Certificates_valid
    (CA1_7_8I2R2CertificateIndex a) (CA1_7_8I2R2P_sound a)
def CA1_7_8I2R2Entropy : Ball := ⟨(2022525741344877452754004889909 / 50000000000000000000000000000000), (1396080699 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R2Entropy_sound : CA1_7_8I2R2Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R2Value CA1_7_8I2R2Terms CA1_7_8I2R2Terms_sound) (by decide +kernel)
def CA1_7_8I2R2Mass : Ball := ⟨(167176461285217244558128668051 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R2Mass_sound : CA1_7_8I2R2Mass.Encloses (∑ a, CA1_7_8I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R2P CA1_7_8I2R2Value CA1_7_8I2R2P_sound) (by decide +kernel)
def CA1_7_8I2R2MassTermLogWitness : LogWitness := ⟨-8, 167176461285217244558128668051, 97656250000000000000000000000⟩
def CA1_7_8I2R2MassTermLog : Ball := ⟨(-500758119489740070137408935000643 / 100000000000000000000000000000000), (47645603623 / 25000000000000000000000000000000)⟩
lemma CA1_7_8I2R2MassTermLog_sound : CA1_7_8I2R2MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I2R2Mass_sound) (w := CA1_7_8I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I2R2MassTerm : Ball := ⟨(3348598815045388870657504831627 / 100000000000000000000000000000000), (1274435791 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R2MassTerm_sound : CA1_7_8I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I2R2Mass_sound) CA1_7_8I2R2MassTermLog_sound) (by decide +kernel)
def CA1_7_8I2R2H : Ball := ⟨(696452667644366034850504948191 / 100000000000000000000000000000000), (267051649 / 10000000000000000000000000000000)⟩
lemma CA1_7_8I2R2H_sound : CA1_7_8I2R2H.Encloses (homogeneousEntropy CA1_7_8I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R2Value CA1_7_8I2R2MassTerm_sound CA1_7_8I2R2Entropy_sound) (by decide +kernel)
def CA1_7_8I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA1_7_8I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA1_7_8I2R3Raw_sound (a : PairSlot) :
    (CA1_7_8I2R3Raw a).Encloses (CA1_7_8I2R3Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA1_7_8I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(171743595120508560595316956867 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1093478216067274206814721842293 / 100000000000000000000000000000000), (80009869 / 20000000000000000000000000000000)⟩ ⟨(-636692282643789715464628421873219 / 100000000000000000000000000000000), (232934061677 / 100000000000000000000000000000000)⟩ ⟨-10, 171743595120508560595316956867, 97656250000000000000000000000⟩,
   .log ⟨(1167996827666824018164785371949 / 20000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(16588136840167857806241731428483 / 100000000000000000000000000000000), (185499713 / 2500000000000000000000000000000)⟩ ⟨(-56808842103806443701938133479403 / 20000000000000000000000000000000), (63527471169 / 50000000000000000000000000000000)⟩ ⟨-5, 1167996827666824018164785371949, 625000000000000000000000000000⟩,
   .log ⟨(141421815855210237963391325627 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(731841503094153733525420656171 / 25000000000000000000000000000000), (1078100451 / 100000000000000000000000000000000)⟩ ⟨(-51748840775982113515491899460717 / 10000000000000000000000000000000), (381164827 / 200000000000000000000000000000)⟩ ⟨-8, 141421815855210237963391325627, 97656250000000000000000000000⟩]
lemma CA1_7_8I2R3Certificates_valid :
    CA1_7_8I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_7_8I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R3Certificates (CA1_7_8I2R3CertificateIndex a)).input
lemma CA1_7_8I2R3P_check : ∀ a : PairSlot, contains (CA1_7_8I2R3Raw a) (CA1_7_8I2R3P a) = true := by
  decide +kernel
lemma CA1_7_8I2R3P_sound (a : PairSlot) :
    (CA1_7_8I2R3P a).Encloses (CA1_7_8I2R3Value a) :=
  contains_sound (CA1_7_8I2R3Raw_sound a) (CA1_7_8I2R3P_check a)
def CA1_7_8I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R3Certificates (CA1_7_8I2R3CertificateIndex a)).output
lemma CA1_7_8I2R3Terms_sound (a : PairSlot) :
    (CA1_7_8I2R3Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R3Certificates_valid
    (CA1_7_8I2R3CertificateIndex a) (CA1_7_8I2R3P_sound a)
def CA1_7_8I2R3Entropy : Ball := ⟨(1030449053430587347357906794773 / 2500000000000000000000000000000), (2224534579 / 12500000000000000000000000000000)⟩
lemma CA1_7_8I2R3Entropy_sound : CA1_7_8I2R3Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R3Value CA1_7_8I2R3Terms CA1_7_8I2R3Terms_sound) (by decide +kernel)
def CA1_7_8I2R3Mass : Ball := ⟨(82217687460943370040910113989 / 625000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
lemma CA1_7_8I2R3Mass_sound : CA1_7_8I2R3Mass.Encloses (∑ a, CA1_7_8I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R3P CA1_7_8I2R3Value CA1_7_8I2R3P_sound) (by decide +kernel)
def CA1_7_8I2R3MassTermLogWitness : LogWitness := ⟨-3, 82217687460943370040910113989, 78125000000000000000000000000⟩
def CA1_7_8I2R3MassTermLog : Ball := ⟨(-4056762389794801402748180609559 / 2000000000000000000000000000000), (16940659001 / 20000000000000000000000000000000)⟩
lemma CA1_7_8I2R3MassTermLog_sound : CA1_7_8I2R3MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I2R3Mass_sound) (w := CA1_7_8I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I2R3MassTerm : Ball := ⟨(26683009781396696269243426562597 / 100000000000000000000000000000000), (11142574531 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R3MassTerm_sound : CA1_7_8I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I2R3Mass_sound) CA1_7_8I2R3MassTermLog_sound) (by decide +kernel)
def CA1_7_8I2R3H : Ball := ⟨(14534952355826797625072845228323 / 100000000000000000000000000000000), (28938851163 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R3H_sound : CA1_7_8I2R3H.Encloses (homogeneousEntropy CA1_7_8I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R3Value CA1_7_8I2R3MassTerm_sound CA1_7_8I2R3Entropy_sound) (by decide +kernel)
def CA1_7_8I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA1_7_8I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA1_7_8I2R4Raw_sound (a : PairSlot) :
    (CA1_7_8I2R4Raw a).Encloses (CA1_7_8I2R4Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA1_7_8I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5699036240698246021355651399 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(6961820416627277872998155103 / 12500000000000000000000000000000), (9654549 / 50000000000000000000000000000000)⟩ ⟨(-30539463703139723814056889945813 / 3125000000000000000000000000000), (169406598237 / 50000000000000000000000000000000)⟩ ⟨-15, 5699036240698246021355651399, 3051757812500000000000000000⟩,
   .log ⟨(2257891568295462797970246580127 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(8559077044393300420616931473893 / 100000000000000000000000000000000), (3346889997 / 100000000000000000000000000000000)⟩ ⟨(-75814774850811419881007148354869 / 20000000000000000000000000000000), (148230766091 / 100000000000000000000000000000000)⟩ ⟨-6, 2257891568295462797970246580127, 1562500000000000000000000000000⟩,
   .log ⟨(23994122698647338646957836425373 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩ ⟨(34248281524131016482456459253889 / 100000000000000000000000000000000), (812952501 / 4000000000000000000000000000000)⟩ ⟨(-142736127318636046291139066619667 / 100000000000000000000000000000000), (21175823707 / 25000000000000000000000000000000)⟩ ⟨-3, 23994122698647338646957836425373, 12500000000000000000000000000000⟩,
   .log ⟨(311023681798977723241057577217 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(109150950650344740952208527501 / 2000000000000000000000000000000), (2107578459 / 100000000000000000000000000000000)⟩ ⟨(-109669051182664135222659014302887 / 25000000000000000000000000000000), (21175823703 / 12500000000000000000000000000000)⟩ ⟨-7, 311023681798977723241057577217, 195312500000000000000000000000⟩,
   .log ⟨(1482262599464787529958594107 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7727189516629883541337234119 / 25000000000000000000000000000000), (10671977 / 100000000000000000000000000000000)⟩ ⟨(-208524171612236643227328646315203 / 20000000000000000000000000000000), (359989036343 / 100000000000000000000000000000000)⟩ ⟨-16, 1482262599464787529958594107, 762939453125000000000000000⟩]
lemma CA1_7_8I2R4Certificates_valid :
    CA1_7_8I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA1_7_8I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R4Certificates (CA1_7_8I2R4CertificateIndex a)).input
lemma CA1_7_8I2R4P_check : ∀ a : PairSlot, contains (CA1_7_8I2R4Raw a) (CA1_7_8I2R4P a) = true := by
  decide +kernel
lemma CA1_7_8I2R4P_sound (a : PairSlot) :
    (CA1_7_8I2R4P a).Encloses (CA1_7_8I2R4Value a) :=
  contains_sound (CA1_7_8I2R4Raw_sound a) (CA1_7_8I2R4P_check a)
def CA1_7_8I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R4Certificates (CA1_7_8I2R4CertificateIndex a)).output
lemma CA1_7_8I2R4Terms_sound (a : PairSlot) :
    (CA1_7_8I2R4Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R4Certificates_valid
    (CA1_7_8I2R4CertificateIndex a) (CA1_7_8I2R4P_sound a)
def CA1_7_8I2R4Entropy : Ball := ⟨(62423828562684647399044494369899 / 100000000000000000000000000000000), (3128203961 / 10000000000000000000000000000000)⟩
lemma CA1_7_8I2R4Entropy_sound : CA1_7_8I2R4Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R4Value CA1_7_8I2R4Terms CA1_7_8I2R4Terms_sound) (by decide +kernel)
def CA1_7_8I2R4Mass : Ball := ⟨(49619932619696659353487069911 / 160000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
lemma CA1_7_8I2R4Mass_sound : CA1_7_8I2R4Mass.Encloses (∑ a, CA1_7_8I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R4P CA1_7_8I2R4Value CA1_7_8I2R4P_sound) (by decide +kernel)
def CA1_7_8I2R4MassTermLogWitness : LogWitness := ⟨-2, 49619932619696659353487069911, 40000000000000000000000000000⟩
def CA1_7_8I2R4MassTermLog : Ball := ⟨(-117078119489740070137409049573447 / 100000000000000000000000000000000), (6352747119 / 10000000000000000000000000000000)⟩
lemma CA1_7_8I2R4MassTermLog_sound : CA1_7_8I2R4MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I2R4Mass_sound) (w := CA1_7_8I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I2R4MassTerm : Ball := ⟨(36308802502010603181711095923221 / 100000000000000000000000000000000), (9850715151 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I2R4MassTerm_sound : CA1_7_8I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I2R4Mass_sound) CA1_7_8I2R4MassTermLog_sound) (by decide +kernel)
def CA1_7_8I2R4H : Ball := ⟨(13057513030337022108666699223339 / 50000000000000000000000000000000), (6372933739 / 12500000000000000000000000000000)⟩
lemma CA1_7_8I2R4H_sound : CA1_7_8I2R4H.Encloses (homogeneousEntropy CA1_7_8I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R4Value CA1_7_8I2R4MassTerm_sound CA1_7_8I2R4Entropy_sound) (by decide +kernel)
def CA1_7_8I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA1_7_8I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA1_7_8I2R5Raw_sound (a : PairSlot) :
    (CA1_7_8I2R5Raw a).Encloses (CA1_7_8I2R5Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA1_7_8I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(908997158043255639612862667 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(18583618645481023349914450091 / 50000000000000000000000000000000), (12319221 / 100000000000000000000000000000000)⟩ ⟨(-255551110378123718117001657366033 / 25000000000000000000000000000000), (33881320643 / 10000000000000000000000000000000)⟩ ⟨-15, 908997158043255639612862667, 762939453125000000000000000⟩,
   .log ⟨(2414884884244844550619283217397 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(4495934351825481781121280185721 / 50000000000000000000000000000000), (3579602409 / 100000000000000000000000000000000)⟩ ⟨(-37235185669990223567042408692579 / 10000000000000000000000000000000), (37057691559 / 25000000000000000000000000000000)⟩ ⟨-6, 2414884884244844550619283217397, 1562500000000000000000000000000⟩,
   .log ⟨(89118471959175795539073152043 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(6258753599911944504262624821 / 1000000000000000000000000000000), (45291771 / 20000000000000000000000000000000)⟩ ⟨(-702295883481823114987378298571253 / 100000000000000000000000000000000), (127054942659 / 50000000000000000000000000000000)⟩ ⟨-11, 89118471959175795539073152043, 48828125000000000000000000000⟩]
lemma CA1_7_8I2R5Certificates_valid :
    CA1_7_8I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA1_7_8I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R5Certificates (CA1_7_8I2R5CertificateIndex a)).input
lemma CA1_7_8I2R5P_check : ∀ a : PairSlot, contains (CA1_7_8I2R5Raw a) (CA1_7_8I2R5P a) = true := by
  decide +kernel
lemma CA1_7_8I2R5P_sound (a : PairSlot) :
    (CA1_7_8I2R5P a).Encloses (CA1_7_8I2R5Value a) :=
  contains_sound (CA1_7_8I2R5Raw_sound a) (CA1_7_8I2R5P_check a)
def CA1_7_8I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R5Certificates (CA1_7_8I2R5CertificateIndex a)).output
lemma CA1_7_8I2R5Terms_sound (a : PairSlot) :
    (CA1_7_8I2R5Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R5Certificates_valid
    (CA1_7_8I2R5CertificateIndex a) (CA1_7_8I2R5P_sound a)
def CA1_7_8I2R5Entropy : Ball := ⟨(2413727825233280014842162938431 / 12500000000000000000000000000000), (763676097 / 10000000000000000000000000000000)⟩
lemma CA1_7_8I2R5Entropy_sound : CA1_7_8I2R5Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R5Value CA1_7_8I2R5Terms CA1_7_8I2R5Terms_sound) (by decide +kernel)
def CA1_7_8I2R5Mass : Ball := ⟨(626909836209048342179201955027 / 12500000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I2R5Mass_sound : CA1_7_8I2R5Mass.Encloses (∑ a, CA1_7_8I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R5P CA1_7_8I2R5Value CA1_7_8I2R5P_sound) (by decide +kernel)
def CA1_7_8I2R5MassTermLogWitness : LogWitness := ⟨-5, 626909836209048342179201955027, 390625000000000000000000000000⟩
def CA1_7_8I2R5MassTermLog : Ball := ⟨(-29926811948974007013740899228697 / 10000000000000000000000000000000), (15881867827 / 12500000000000000000000000000000)⟩
lemma CA1_7_8I2R5MassTermLog_sound : CA1_7_8I2R5MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I2R5Mass_sound) (w := CA1_7_8I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I2R5MassTerm : Ball := ⟨(3752282555438057105977780971651 / 25000000000000000000000000000000), (318607977 / 5000000000000000000000000000000)⟩
lemma CA1_7_8I2R5MassTerm_sound : CA1_7_8I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I2R5Mass_sound) CA1_7_8I2R5MassTermLog_sound) (by decide +kernel)
def CA1_7_8I2R5H : Ball := ⟨(1075173095028502923706544905211 / 25000000000000000000000000000000), (1400892051 / 10000000000000000000000000000000)⟩
lemma CA1_7_8I2R5H_sound : CA1_7_8I2R5H.Encloses (homogeneousEntropy CA1_7_8I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R5Value CA1_7_8I2R5MassTerm_sound CA1_7_8I2R5Entropy_sound) (by decide +kernel)
def CA1_7_8I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA1_7_8I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA1_7_8I2R6Raw_sound (a : PairSlot) :
    (CA1_7_8I2R6Raw a).Encloses (CA1_7_8I2R6Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA1_7_8I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(267911455786341918508038917 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(15030618044618258481487988127 / 100000000000000000000000000000000), (2552967 / 50000000000000000000000000000000)⟩ ⟨(-1122058629445476432775534353488101 / 100000000000000000000000000000000), (76232980189 / 20000000000000000000000000000000)⟩ ⟨-17, 267911455786341918508038917, 152587890625000000000000000⟩,
   .log ⟨(21099356402627791633381 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(881653449804663227882189 / 50000000000000000000000000000000), (119 / 20000000000000000000000000000000)⟩ ⟨(-1044644956202146119551450304729979 / 50000000000000000000000000000000), (16970280703 / 2500000000000000000000000000000)⟩ ⟨-31, 42198712805255583266762, 23283064365386962890625⟩,
   .log ⟨(140463736612849046343823061117 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(230640616665710923698920740229 / 25000000000000000000000000000000), (327187909 / 100000000000000000000000000000000)⟩ ⟨(-656797611191023566539967400269571 / 100000000000000000000000000000000), (29116757831 / 12500000000000000000000000000000)⟩ ⟨-10, 140463736612849046343823061117, 97656250000000000000000000000⟩]
lemma CA1_7_8I2R6Certificates_valid :
    CA1_7_8I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA1_7_8I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R6Certificates (CA1_7_8I2R6CertificateIndex a)).input
lemma CA1_7_8I2R6P_check : ∀ a : PairSlot, contains (CA1_7_8I2R6Raw a) (CA1_7_8I2R6P a) = true := by
  decide +kernel
lemma CA1_7_8I2R6P_sound (a : PairSlot) :
    (CA1_7_8I2R6P a).Encloses (CA1_7_8I2R6Value a) :=
  contains_sound (CA1_7_8I2R6Raw_sound a) (CA1_7_8I2R6P_check a)
def CA1_7_8I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R6Certificates (CA1_7_8I2R6CertificateIndex a)).output
lemma CA1_7_8I2R6Terms_sound (a : PairSlot) :
    (CA1_7_8I2R6Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R6Certificates_valid
    (CA1_7_8I2R6CertificateIndex a) (CA1_7_8I2R6P_sound a)
def CA1_7_8I2R6Entropy : Ball := ⟨(476313614682939715205785232963 / 50000000000000000000000000000000), (337400967 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R6Entropy_sound : CA1_7_8I2R6Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R6Value CA1_7_8I2R6Terms CA1_7_8I2R6Terms_sound) (by decide +kernel)
def CA1_7_8I2R6Mass : Ball := ⟨(28628603993112737310247303467 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R6Mass_sound : CA1_7_8I2R6Mass.Encloses (∑ a, CA1_7_8I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R6P CA1_7_8I2R6Value CA1_7_8I2R6P_sound) (by decide +kernel)
def CA1_7_8I2R6MassTermLogWitness : LogWitness := ⟨-10, 28628603993112737310247303467, 19531250000000000000000000000⟩
def CA1_7_8I2R6MassTermLog : Ball := ⟨(-163727029872435017534352224202163 / 25000000000000000000000000000000), (232934065403 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R6MassTermLog_sound : CA1_7_8I2R6MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I2R6Mass_sound) (w := CA1_7_8I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I2R6MassTerm : Ball := ⟨(234363815059324078428978966481 / 25000000000000000000000000000000), (166714451 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I2R6MassTerm_sound : CA1_7_8I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I2R6Mass_sound) CA1_7_8I2R6MassTermLog_sound) (by decide +kernel)
def CA1_7_8I2R6H : Ball := ⟨(7585984564291558347827300001 / 50000000000000000000000000000000), (670829869 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2R6H_sound : CA1_7_8I2R6H.Encloses (homogeneousEntropy CA1_7_8I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R6Value CA1_7_8I2R6MassTerm_sound CA1_7_8I2R6Entropy_sound) (by decide +kernel)
def CA1_7_8I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA1_7_8I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA1_7_8I2R7Raw_sound (a : PairSlot) :
    (CA1_7_8I2R7Raw a).Encloses (CA1_7_8I2R7Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA1_7_8I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I2R7Certificates_valid :
    CA1_7_8I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R7Certificates (CA1_7_8I2R7CertificateIndex a)).input
lemma CA1_7_8I2R7P_check : ∀ a : PairSlot, contains (CA1_7_8I2R7Raw a) (CA1_7_8I2R7P a) = true := by
  decide +kernel
lemma CA1_7_8I2R7P_sound (a : PairSlot) :
    (CA1_7_8I2R7P a).Encloses (CA1_7_8I2R7Value a) :=
  contains_sound (CA1_7_8I2R7Raw_sound a) (CA1_7_8I2R7P_check a)
def CA1_7_8I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R7Certificates (CA1_7_8I2R7CertificateIndex a)).output
lemma CA1_7_8I2R7Terms_sound (a : PairSlot) :
    (CA1_7_8I2R7Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R7Certificates_valid
    (CA1_7_8I2R7CertificateIndex a) (CA1_7_8I2R7P_sound a)
def CA1_7_8I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R7Entropy_sound : CA1_7_8I2R7Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R7Value CA1_7_8I2R7Terms CA1_7_8I2R7Terms_sound) (by decide +kernel)
def CA1_7_8I2R7Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R7Mass_sound : CA1_7_8I2R7Mass.Encloses (∑ a, CA1_7_8I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R7P CA1_7_8I2R7Value CA1_7_8I2R7P_sound) (by decide +kernel)
def CA1_7_8I2R7MassTerm : Ball := .exact 0
lemma CA1_7_8I2R7MassTerm_sound : CA1_7_8I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R7Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I2R7Mass_sound)
def CA1_7_8I2R7H : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R7H_sound : CA1_7_8I2R7H.Encloses (homogeneousEntropy CA1_7_8I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R7Value CA1_7_8I2R7MassTerm_sound CA1_7_8I2R7Entropy_sound) (by decide +kernel)
def CA1_7_8I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA1_7_8I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA1_7_8I2R8Raw_sound (a : PairSlot) :
    (CA1_7_8I2R8Raw a).Encloses (CA1_7_8I2R8Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA1_7_8I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I2R8Certificates_valid :
    CA1_7_8I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R8Certificates (CA1_7_8I2R8CertificateIndex a)).input
lemma CA1_7_8I2R8P_check : ∀ a : PairSlot, contains (CA1_7_8I2R8Raw a) (CA1_7_8I2R8P a) = true := by
  decide +kernel
lemma CA1_7_8I2R8P_sound (a : PairSlot) :
    (CA1_7_8I2R8P a).Encloses (CA1_7_8I2R8Value a) :=
  contains_sound (CA1_7_8I2R8Raw_sound a) (CA1_7_8I2R8P_check a)
def CA1_7_8I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R8Certificates (CA1_7_8I2R8CertificateIndex a)).output
lemma CA1_7_8I2R8Terms_sound (a : PairSlot) :
    (CA1_7_8I2R8Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R8Certificates_valid
    (CA1_7_8I2R8CertificateIndex a) (CA1_7_8I2R8P_sound a)
def CA1_7_8I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R8Entropy_sound : CA1_7_8I2R8Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R8Value CA1_7_8I2R8Terms CA1_7_8I2R8Terms_sound) (by decide +kernel)
def CA1_7_8I2R8Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R8Mass_sound : CA1_7_8I2R8Mass.Encloses (∑ a, CA1_7_8I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R8P CA1_7_8I2R8Value CA1_7_8I2R8P_sound) (by decide +kernel)
def CA1_7_8I2R8MassTerm : Ball := .exact 0
lemma CA1_7_8I2R8MassTerm_sound : CA1_7_8I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R8Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I2R8Mass_sound)
def CA1_7_8I2R8H : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R8H_sound : CA1_7_8I2R8H.Encloses (homogeneousEntropy CA1_7_8I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R8Value CA1_7_8I2R8MassTerm_sound CA1_7_8I2R8Entropy_sound) (by decide +kernel)
def CA1_7_8I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA1_7_8I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA1_7_8I2R9Raw_sound (a : PairSlot) :
    (CA1_7_8I2R9Raw a).Encloses (CA1_7_8I2R9Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA1_7_8I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I2R9Certificates_valid :
    CA1_7_8I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R9Certificates (CA1_7_8I2R9CertificateIndex a)).input
lemma CA1_7_8I2R9P_check : ∀ a : PairSlot, contains (CA1_7_8I2R9Raw a) (CA1_7_8I2R9P a) = true := by
  decide +kernel
lemma CA1_7_8I2R9P_sound (a : PairSlot) :
    (CA1_7_8I2R9P a).Encloses (CA1_7_8I2R9Value a) :=
  contains_sound (CA1_7_8I2R9Raw_sound a) (CA1_7_8I2R9P_check a)
def CA1_7_8I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R9Certificates (CA1_7_8I2R9CertificateIndex a)).output
lemma CA1_7_8I2R9Terms_sound (a : PairSlot) :
    (CA1_7_8I2R9Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R9Certificates_valid
    (CA1_7_8I2R9CertificateIndex a) (CA1_7_8I2R9P_sound a)
def CA1_7_8I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R9Entropy_sound : CA1_7_8I2R9Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R9Value CA1_7_8I2R9Terms CA1_7_8I2R9Terms_sound) (by decide +kernel)
def CA1_7_8I2R9Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R9Mass_sound : CA1_7_8I2R9Mass.Encloses (∑ a, CA1_7_8I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R9P CA1_7_8I2R9Value CA1_7_8I2R9P_sound) (by decide +kernel)
def CA1_7_8I2R9MassTerm : Ball := .exact 0
lemma CA1_7_8I2R9MassTerm_sound : CA1_7_8I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R9Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I2R9Mass_sound)
def CA1_7_8I2R9H : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R9H_sound : CA1_7_8I2R9H.Encloses (homogeneousEntropy CA1_7_8I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R9Value CA1_7_8I2R9MassTerm_sound CA1_7_8I2R9Entropy_sound) (by decide +kernel)
def CA1_7_8I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA1_7_8I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA1_7_8I2R10Raw_sound (a : PairSlot) :
    (CA1_7_8I2R10Raw a).Encloses (CA1_7_8I2R10Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA1_7_8I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I2R10Certificates_valid :
    CA1_7_8I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R10Certificates (CA1_7_8I2R10CertificateIndex a)).input
lemma CA1_7_8I2R10P_check : ∀ a : PairSlot, contains (CA1_7_8I2R10Raw a) (CA1_7_8I2R10P a) = true := by
  decide +kernel
lemma CA1_7_8I2R10P_sound (a : PairSlot) :
    (CA1_7_8I2R10P a).Encloses (CA1_7_8I2R10Value a) :=
  contains_sound (CA1_7_8I2R10Raw_sound a) (CA1_7_8I2R10P_check a)
def CA1_7_8I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R10Certificates (CA1_7_8I2R10CertificateIndex a)).output
lemma CA1_7_8I2R10Terms_sound (a : PairSlot) :
    (CA1_7_8I2R10Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R10Certificates_valid
    (CA1_7_8I2R10CertificateIndex a) (CA1_7_8I2R10P_sound a)
def CA1_7_8I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R10Entropy_sound : CA1_7_8I2R10Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R10Value CA1_7_8I2R10Terms CA1_7_8I2R10Terms_sound) (by decide +kernel)
def CA1_7_8I2R10Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R10Mass_sound : CA1_7_8I2R10Mass.Encloses (∑ a, CA1_7_8I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R10P CA1_7_8I2R10Value CA1_7_8I2R10P_sound) (by decide +kernel)
def CA1_7_8I2R10MassTerm : Ball := .exact 0
lemma CA1_7_8I2R10MassTerm_sound : CA1_7_8I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R10Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I2R10Mass_sound)
def CA1_7_8I2R10H : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R10H_sound : CA1_7_8I2R10H.Encloses (homogeneousEntropy CA1_7_8I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R10Value CA1_7_8I2R10MassTerm_sound CA1_7_8I2R10Entropy_sound) (by decide +kernel)
def CA1_7_8I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA1_7_8I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA1_7_8I2R11Raw_sound (a : PairSlot) :
    (CA1_7_8I2R11Raw a).Encloses (CA1_7_8I2R11Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA1_7_8I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I2R11Certificates_valid :
    CA1_7_8I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R11Certificates (CA1_7_8I2R11CertificateIndex a)).input
lemma CA1_7_8I2R11P_check : ∀ a : PairSlot, contains (CA1_7_8I2R11Raw a) (CA1_7_8I2R11P a) = true := by
  decide +kernel
lemma CA1_7_8I2R11P_sound (a : PairSlot) :
    (CA1_7_8I2R11P a).Encloses (CA1_7_8I2R11Value a) :=
  contains_sound (CA1_7_8I2R11Raw_sound a) (CA1_7_8I2R11P_check a)
def CA1_7_8I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R11Certificates (CA1_7_8I2R11CertificateIndex a)).output
lemma CA1_7_8I2R11Terms_sound (a : PairSlot) :
    (CA1_7_8I2R11Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R11Certificates_valid
    (CA1_7_8I2R11CertificateIndex a) (CA1_7_8I2R11P_sound a)
def CA1_7_8I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R11Entropy_sound : CA1_7_8I2R11Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R11Value CA1_7_8I2R11Terms CA1_7_8I2R11Terms_sound) (by decide +kernel)
def CA1_7_8I2R11Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R11Mass_sound : CA1_7_8I2R11Mass.Encloses (∑ a, CA1_7_8I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R11P CA1_7_8I2R11Value CA1_7_8I2R11P_sound) (by decide +kernel)
def CA1_7_8I2R11MassTerm : Ball := .exact 0
lemma CA1_7_8I2R11MassTerm_sound : CA1_7_8I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R11Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I2R11Mass_sound)
def CA1_7_8I2R11H : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R11H_sound : CA1_7_8I2R11H.Encloses (homogeneousEntropy CA1_7_8I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R11Value CA1_7_8I2R11MassTerm_sound CA1_7_8I2R11Entropy_sound) (by decide +kernel)
def CA1_7_8I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA1_7_8I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA1_7_8I2R12Raw_sound (a : PairSlot) :
    (CA1_7_8I2R12Raw a).Encloses (CA1_7_8I2R12Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA1_7_8I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I2R12Certificates_valid :
    CA1_7_8I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R12Certificates (CA1_7_8I2R12CertificateIndex a)).input
lemma CA1_7_8I2R12P_check : ∀ a : PairSlot, contains (CA1_7_8I2R12Raw a) (CA1_7_8I2R12P a) = true := by
  decide +kernel
lemma CA1_7_8I2R12P_sound (a : PairSlot) :
    (CA1_7_8I2R12P a).Encloses (CA1_7_8I2R12Value a) :=
  contains_sound (CA1_7_8I2R12Raw_sound a) (CA1_7_8I2R12P_check a)
def CA1_7_8I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R12Certificates (CA1_7_8I2R12CertificateIndex a)).output
lemma CA1_7_8I2R12Terms_sound (a : PairSlot) :
    (CA1_7_8I2R12Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R12Certificates_valid
    (CA1_7_8I2R12CertificateIndex a) (CA1_7_8I2R12P_sound a)
def CA1_7_8I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R12Entropy_sound : CA1_7_8I2R12Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R12Value CA1_7_8I2R12Terms CA1_7_8I2R12Terms_sound) (by decide +kernel)
def CA1_7_8I2R12Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R12Mass_sound : CA1_7_8I2R12Mass.Encloses (∑ a, CA1_7_8I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R12P CA1_7_8I2R12Value CA1_7_8I2R12P_sound) (by decide +kernel)
def CA1_7_8I2R12MassTerm : Ball := .exact 0
lemma CA1_7_8I2R12MassTerm_sound : CA1_7_8I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R12Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I2R12Mass_sound)
def CA1_7_8I2R12H : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R12H_sound : CA1_7_8I2R12H.Encloses (homogeneousEntropy CA1_7_8I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R12Value CA1_7_8I2R12MassTerm_sound CA1_7_8I2R12Entropy_sound) (by decide +kernel)
def CA1_7_8I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA1_7_8I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA1_7_8I2R13Raw_sound (a : PairSlot) :
    (CA1_7_8I2R13Raw a).Encloses (CA1_7_8I2R13Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA1_7_8I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I2R13Certificates_valid :
    CA1_7_8I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R13Certificates (CA1_7_8I2R13CertificateIndex a)).input
lemma CA1_7_8I2R13P_check : ∀ a : PairSlot, contains (CA1_7_8I2R13Raw a) (CA1_7_8I2R13P a) = true := by
  decide +kernel
lemma CA1_7_8I2R13P_sound (a : PairSlot) :
    (CA1_7_8I2R13P a).Encloses (CA1_7_8I2R13Value a) :=
  contains_sound (CA1_7_8I2R13Raw_sound a) (CA1_7_8I2R13P_check a)
def CA1_7_8I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R13Certificates (CA1_7_8I2R13CertificateIndex a)).output
lemma CA1_7_8I2R13Terms_sound (a : PairSlot) :
    (CA1_7_8I2R13Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R13Certificates_valid
    (CA1_7_8I2R13CertificateIndex a) (CA1_7_8I2R13P_sound a)
def CA1_7_8I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R13Entropy_sound : CA1_7_8I2R13Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R13Value CA1_7_8I2R13Terms CA1_7_8I2R13Terms_sound) (by decide +kernel)
def CA1_7_8I2R13Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R13Mass_sound : CA1_7_8I2R13Mass.Encloses (∑ a, CA1_7_8I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R13P CA1_7_8I2R13Value CA1_7_8I2R13P_sound) (by decide +kernel)
def CA1_7_8I2R13MassTerm : Ball := .exact 0
lemma CA1_7_8I2R13MassTerm_sound : CA1_7_8I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R13Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I2R13Mass_sound)
def CA1_7_8I2R13H : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R13H_sound : CA1_7_8I2R13H.Encloses (homogeneousEntropy CA1_7_8I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R13Value CA1_7_8I2R13MassTerm_sound CA1_7_8I2R13Entropy_sound) (by decide +kernel)
def CA1_7_8I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA1_7_8I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA1_7_8I2R14Raw_sound (a : PairSlot) :
    (CA1_7_8I2R14Raw a).Encloses (CA1_7_8I2R14Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA1_7_8I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I2R14Certificates_valid :
    CA1_7_8I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R14Certificates (CA1_7_8I2R14CertificateIndex a)).input
lemma CA1_7_8I2R14P_check : ∀ a : PairSlot, contains (CA1_7_8I2R14Raw a) (CA1_7_8I2R14P a) = true := by
  decide +kernel
lemma CA1_7_8I2R14P_sound (a : PairSlot) :
    (CA1_7_8I2R14P a).Encloses (CA1_7_8I2R14Value a) :=
  contains_sound (CA1_7_8I2R14Raw_sound a) (CA1_7_8I2R14P_check a)
def CA1_7_8I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R14Certificates (CA1_7_8I2R14CertificateIndex a)).output
lemma CA1_7_8I2R14Terms_sound (a : PairSlot) :
    (CA1_7_8I2R14Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R14Certificates_valid
    (CA1_7_8I2R14CertificateIndex a) (CA1_7_8I2R14P_sound a)
def CA1_7_8I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R14Entropy_sound : CA1_7_8I2R14Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R14Value CA1_7_8I2R14Terms CA1_7_8I2R14Terms_sound) (by decide +kernel)
def CA1_7_8I2R14Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R14Mass_sound : CA1_7_8I2R14Mass.Encloses (∑ a, CA1_7_8I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R14P CA1_7_8I2R14Value CA1_7_8I2R14P_sound) (by decide +kernel)
def CA1_7_8I2R14MassTerm : Ball := .exact 0
lemma CA1_7_8I2R14MassTerm_sound : CA1_7_8I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R14Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I2R14Mass_sound)
def CA1_7_8I2R14H : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R14H_sound : CA1_7_8I2R14H.Encloses (homogeneousEntropy CA1_7_8I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R14Value CA1_7_8I2R14MassTerm_sound CA1_7_8I2R14Entropy_sound) (by decide +kernel)
def CA1_7_8I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA1_7_8I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA1_7_8I2R15Raw_sound (a : PairSlot) :
    (CA1_7_8I2R15Raw a).Encloses (CA1_7_8I2R15Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA1_7_8I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I2R15Certificates_valid :
    CA1_7_8I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R15Certificates (CA1_7_8I2R15CertificateIndex a)).input
lemma CA1_7_8I2R15P_check : ∀ a : PairSlot, contains (CA1_7_8I2R15Raw a) (CA1_7_8I2R15P a) = true := by
  decide +kernel
lemma CA1_7_8I2R15P_sound (a : PairSlot) :
    (CA1_7_8I2R15P a).Encloses (CA1_7_8I2R15Value a) :=
  contains_sound (CA1_7_8I2R15Raw_sound a) (CA1_7_8I2R15P_check a)
def CA1_7_8I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R15Certificates (CA1_7_8I2R15CertificateIndex a)).output
lemma CA1_7_8I2R15Terms_sound (a : PairSlot) :
    (CA1_7_8I2R15Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R15Certificates_valid
    (CA1_7_8I2R15CertificateIndex a) (CA1_7_8I2R15P_sound a)
def CA1_7_8I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R15Entropy_sound : CA1_7_8I2R15Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R15Value CA1_7_8I2R15Terms CA1_7_8I2R15Terms_sound) (by decide +kernel)
def CA1_7_8I2R15Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R15Mass_sound : CA1_7_8I2R15Mass.Encloses (∑ a, CA1_7_8I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R15P CA1_7_8I2R15Value CA1_7_8I2R15P_sound) (by decide +kernel)
def CA1_7_8I2R15MassTerm : Ball := .exact 0
lemma CA1_7_8I2R15MassTerm_sound : CA1_7_8I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R15Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I2R15Mass_sound)
def CA1_7_8I2R15H : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R15H_sound : CA1_7_8I2R15H.Encloses (homogeneousEntropy CA1_7_8I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R15Value CA1_7_8I2R15MassTerm_sound CA1_7_8I2R15Entropy_sound) (by decide +kernel)
def CA1_7_8I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA1_7_8I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA1_7_8I2R16Raw_sound (a : PairSlot) :
    (CA1_7_8I2R16Raw a).Encloses (CA1_7_8I2R16Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA1_7_8I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I2R16Certificates_valid :
    CA1_7_8I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R16Certificates (CA1_7_8I2R16CertificateIndex a)).input
lemma CA1_7_8I2R16P_check : ∀ a : PairSlot, contains (CA1_7_8I2R16Raw a) (CA1_7_8I2R16P a) = true := by
  decide +kernel
lemma CA1_7_8I2R16P_sound (a : PairSlot) :
    (CA1_7_8I2R16P a).Encloses (CA1_7_8I2R16Value a) :=
  contains_sound (CA1_7_8I2R16Raw_sound a) (CA1_7_8I2R16P_check a)
def CA1_7_8I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I2R16Certificates (CA1_7_8I2R16CertificateIndex a)).output
lemma CA1_7_8I2R16Terms_sound (a : PairSlot) :
    (CA1_7_8I2R16Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2R16Certificates_valid
    (CA1_7_8I2R16CertificateIndex a) (CA1_7_8I2R16P_sound a)
def CA1_7_8I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R16Entropy_sound : CA1_7_8I2R16Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I2R16Value CA1_7_8I2R16Terms CA1_7_8I2R16Terms_sound) (by decide +kernel)
def CA1_7_8I2R16Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R16Mass_sound : CA1_7_8I2R16Mass.Encloses (∑ a, CA1_7_8I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I2R16P CA1_7_8I2R16Value CA1_7_8I2R16P_sound) (by decide +kernel)
def CA1_7_8I2R16MassTerm : Ball := .exact 0
lemma CA1_7_8I2R16MassTerm_sound : CA1_7_8I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2R16Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I2R16Mass_sound)
def CA1_7_8I2R16H : Ball := ⟨0, 0⟩
lemma CA1_7_8I2R16H_sound : CA1_7_8I2R16H.Encloses (homogeneousEntropy CA1_7_8I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R16Value CA1_7_8I2R16MassTerm_sound CA1_7_8I2R16Entropy_sound) (by decide +kernel)
def CA1_7_8I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_7_8I2R0H
  | 1 => CA1_7_8I2R1H
  | 2 => CA1_7_8I2R2H
  | 3 => CA1_7_8I2R3H
  | 4 => CA1_7_8I2R4H
  | 5 => CA1_7_8I2R5H
  | 6 => CA1_7_8I2R6H
  | 7 => CA1_7_8I2R7H
  | 8 => CA1_7_8I2R8H
  | 9 => CA1_7_8I2R9H
  | 10 => CA1_7_8I2R10H
  | 11 => CA1_7_8I2R11H
  | 12 => CA1_7_8I2R12H
  | 13 => CA1_7_8I2R13H
  | 14 => CA1_7_8I2R14H
  | 15 => CA1_7_8I2R15H
  | 16 => CA1_7_8I2R16H
  | _ => (.exact 0)
lemma CA1_7_8I2ResidualEntropies_sound (k : Fin 17) :
    (CA1_7_8I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_7_8I2R0H_sound
  · exact CA1_7_8I2R1H_sound
  · exact CA1_7_8I2R2H_sound
  · exact CA1_7_8I2R3H_sound
  · exact CA1_7_8I2R4H_sound
  · exact CA1_7_8I2R5H_sound
  · exact CA1_7_8I2R6H_sound
  · exact CA1_7_8I2R7H_sound
  · exact CA1_7_8I2R8H_sound
  · exact CA1_7_8I2R9H_sound
  · exact CA1_7_8I2R10H_sound
  · exact CA1_7_8I2R11H_sound
  · exact CA1_7_8I2R12H_sound
  · exact CA1_7_8I2R13H_sound
  · exact CA1_7_8I2R14H_sound
  · exact CA1_7_8I2R15H_sound
  · exact CA1_7_8I2R16H_sound
def CA1_7_8I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 0, 6, 2 => Z0_6_2H2H
  | 0, 7, 1 => Z0_7_1H2H
  | 1, 0, 7 => Z1_0_7H2H
  | _, _, _ => (.exact 0)
lemma CA1_7_8I2Singles_sound (u : Shape) (hu : u ∈ below (shape 1 7 8))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA1_7_8I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A1_7_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z0_5_3H2H_sound
  · exact Z0_6_2H2H_sound
  · exact Z0_7_1H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 6 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 7 0) by decide +kernel) hd |>.elim
def CA1_7_8I2Singleton : Ball := ⟨(30157846868231622175255511891177 / 50000000000000000000000000000000), (50537614749 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I2Singleton_sound : CA1_7_8I2Singleton.Encloses
    (singletonEntropy (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA1_7_8I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_7_8Law_sound u) CA1_7_8I2Singles_sound) (by decide +kernel)
def CA1_7_8I2Group : Ball := ⟨(105981454927787813602149374910997 / 100000000000000000000000000000000), (36961336739 / 25000000000000000000000000000000)⟩
lemma CA1_7_8I2Group_sound : CA1_7_8I2Group.Encloses
    (groupedEntropy (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_7_8I2Singleton_sound
    (finSumBall_sound 17 CA1_7_8I2ResidualEntropies _ CA1_7_8I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA1_7_8I2H : Ball := ⟨(102374380155238156114601489213779 / 100000000000000000000000000000000), (88327499021 / 20000000000000000000000000000000)⟩
lemma CA1_7_8I2_sound : CA1_7_8I2H.Encloses (stageACapacity (shape 1 7 8) 2) := by
  have hb := contains_sound (Ball.add_sound CA1_7_8I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_7_8I2Group_sound)))
    (show contains (.add CA1_7_8I2PairH (.neg (.mul (.exact 2) CA1_7_8I2Group))) CA1_7_8I2H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false]
  change CA1_7_8I2H.Encloses (homogeneousEntropy CA1_7_8I2PairValue - _)
  simpa only [sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
