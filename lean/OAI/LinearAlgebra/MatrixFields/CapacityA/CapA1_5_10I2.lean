import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA1_5_10I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_5_10I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA1_5_10I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA1_5_10I2R0Raw_sound (a : PairSlot) :
    (CA1_5_10I2R0Raw a).Encloses (CA1_5_10I2R0Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA1_5_10I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R0Certificates_valid :
    CA1_5_10I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R0Certificates (CA1_5_10I2R0CertificateIndex a)).input
lemma CA1_5_10I2R0P_check : ∀ a : PairSlot, contains (CA1_5_10I2R0Raw a) (CA1_5_10I2R0P a) = true := by
  decide +kernel
lemma CA1_5_10I2R0P_sound (a : PairSlot) :
    (CA1_5_10I2R0P a).Encloses (CA1_5_10I2R0Value a) :=
  contains_sound (CA1_5_10I2R0Raw_sound a) (CA1_5_10I2R0P_check a)
def CA1_5_10I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R0Certificates (CA1_5_10I2R0CertificateIndex a)).output
lemma CA1_5_10I2R0Terms_sound (a : PairSlot) :
    (CA1_5_10I2R0Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R0Certificates_valid
    (CA1_5_10I2R0CertificateIndex a) (CA1_5_10I2R0P_sound a)
def CA1_5_10I2R0Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R0Entropy_sound : CA1_5_10I2R0Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R0Value CA1_5_10I2R0Terms CA1_5_10I2R0Terms_sound) (by decide +kernel)
def CA1_5_10I2R0Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R0Mass_sound : CA1_5_10I2R0Mass.Encloses (∑ a, CA1_5_10I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R0P CA1_5_10I2R0Value CA1_5_10I2R0P_sound) (by decide +kernel)
def CA1_5_10I2R0MassTerm : Ball := .exact 0
lemma CA1_5_10I2R0MassTerm_sound : CA1_5_10I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R0Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R0Mass_sound)
def CA1_5_10I2R0H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R0H_sound : CA1_5_10I2R0H.Encloses (homogeneousEntropy CA1_5_10I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R0Value CA1_5_10I2R0MassTerm_sound CA1_5_10I2R0Entropy_sound) (by decide +kernel)
def CA1_5_10I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA1_5_10I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA1_5_10I2R1Raw_sound (a : PairSlot) :
    (CA1_5_10I2R1Raw a).Encloses (CA1_5_10I2R1Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA1_5_10I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R1Certificates_valid :
    CA1_5_10I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R1Certificates (CA1_5_10I2R1CertificateIndex a)).input
lemma CA1_5_10I2R1P_check : ∀ a : PairSlot, contains (CA1_5_10I2R1Raw a) (CA1_5_10I2R1P a) = true := by
  decide +kernel
lemma CA1_5_10I2R1P_sound (a : PairSlot) :
    (CA1_5_10I2R1P a).Encloses (CA1_5_10I2R1Value a) :=
  contains_sound (CA1_5_10I2R1Raw_sound a) (CA1_5_10I2R1P_check a)
def CA1_5_10I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R1Certificates (CA1_5_10I2R1CertificateIndex a)).output
lemma CA1_5_10I2R1Terms_sound (a : PairSlot) :
    (CA1_5_10I2R1Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R1Certificates_valid
    (CA1_5_10I2R1CertificateIndex a) (CA1_5_10I2R1P_sound a)
def CA1_5_10I2R1Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R1Entropy_sound : CA1_5_10I2R1Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R1Value CA1_5_10I2R1Terms CA1_5_10I2R1Terms_sound) (by decide +kernel)
def CA1_5_10I2R1Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R1Mass_sound : CA1_5_10I2R1Mass.Encloses (∑ a, CA1_5_10I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R1P CA1_5_10I2R1Value CA1_5_10I2R1P_sound) (by decide +kernel)
def CA1_5_10I2R1MassTerm : Ball := .exact 0
lemma CA1_5_10I2R1MassTerm_sound : CA1_5_10I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R1Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R1Mass_sound)
def CA1_5_10I2R1H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R1H_sound : CA1_5_10I2R1H.Encloses (homogeneousEntropy CA1_5_10I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R1Value CA1_5_10I2R1MassTerm_sound CA1_5_10I2R1Entropy_sound) (by decide +kernel)
def CA1_5_10I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA1_5_10I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA1_5_10I2R2Raw_sound (a : PairSlot) :
    (CA1_5_10I2R2Raw a).Encloses (CA1_5_10I2R2Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA1_5_10I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(447236789237316840707946291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(688610068444994029318992737 / 12500000000000000000000000000000), (179943 / 10000000000000000000000000000000)⟩ ⟨(-615879627987935948080324132652163 / 50000000000000000000000000000000), (402340873571 / 100000000000000000000000000000000)⟩ ⟨-18, 447236789237316840707946291, 381469726562500000000000000⟩,
   .log ⟨(53769237716673631681010297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(194052899722326233188264489 / 25000000000000000000000000000000), (25051 / 10000000000000000000000000000000)⟩ ⟨(-180449740374644722766312628984091 / 12500000000000000000000000000000), (18634799233 / 4000000000000000000000000000000)⟩ ⟨-21, 53769237716673631681010297, 47683715820312500000000000⟩,
   .log ⟨(1706374619138283140882338411 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(18733526669721479089924408983 / 100000000000000000000000000000000), (3071387 / 50000000000000000000000000000000)⟩ ⟨(-137231930635356939885690339142263 / 12500000000000000000000000000000), (179994530607 / 50000000000000000000000000000000)⟩ ⟨-16, 1706374619138283140882338411, 1525878906250000000000000000⟩]
lemma CA1_5_10I2R2Certificates_valid :
    CA1_5_10I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_5_10I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R2Certificates (CA1_5_10I2R2CertificateIndex a)).input
lemma CA1_5_10I2R2P_check : ∀ a : PairSlot, contains (CA1_5_10I2R2Raw a) (CA1_5_10I2R2P a) = true := by
  decide +kernel
lemma CA1_5_10I2R2P_sound (a : PairSlot) :
    (CA1_5_10I2R2P a).Encloses (CA1_5_10I2R2Value a) :=
  contains_sound (CA1_5_10I2R2Raw_sound a) (CA1_5_10I2R2P_check a)
def CA1_5_10I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R2Certificates (CA1_5_10I2R2CertificateIndex a)).output
lemma CA1_5_10I2R2Terms_sound (a : PairSlot) :
    (CA1_5_10I2R2Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R2Certificates_valid
    (CA1_5_10I2R2CertificateIndex a) (CA1_5_10I2R2P_sound a)
def CA1_5_10I2R2Entropy : Ball := ⟨(31303710962619993424534408687 / 100000000000000000000000000000000), (5121327 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I2R2Entropy_sound : CA1_5_10I2R2Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R2Value CA1_5_10I2R2Terms CA1_5_10I2R2Terms_sound) (by decide +kernel)
def CA1_5_10I2R2Mass : Ball := ⟨(2708386673046264085660251587 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma CA1_5_10I2R2Mass_sound : CA1_5_10I2R2Mass.Encloses (∑ a, CA1_5_10I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R2P CA1_5_10I2R2Value CA1_5_10I2R2P_sound) (by decide +kernel)
def CA1_5_10I2R2MassTermLogWitness : LogWitness := ⟨-16, 2708386673046264085660251587, 1525878906250000000000000000⟩
def CA1_5_10I2R2MassTermLog : Ball := ⟨(-262914308273830957315809376714093 / 25000000000000000000000000000000), (359989187223 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R2MassTermLog_sound : CA1_5_10I2R2MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I2R2Mass_sound) (w := CA1_5_10I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I2R2MassTerm : Ball := ⟨(28482944347280835581130251043 / 100000000000000000000000000000000), (9749953 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R2MassTerm_sound : CA1_5_10I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I2R2Mass_sound) CA1_5_10I2R2MassTermLog_sound) (by decide +kernel)
def CA1_5_10I2R2H : Ball := ⟨(705191653834789460851039411 / 25000000000000000000000000000000), (19992607 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R2H_sound : CA1_5_10I2R2H.Encloses (homogeneousEntropy CA1_5_10I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R2Value CA1_5_10I2R2MassTerm_sound CA1_5_10I2R2Entropy_sound) (by decide +kernel)
def CA1_5_10I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA1_5_10I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA1_5_10I2R3Raw_sound (a : PairSlot) :
    (CA1_5_10I2R3Raw a).Encloses (CA1_5_10I2R3Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA1_5_10I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(7545199268018009738646353009 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(71619136801824455550077378629 / 100000000000000000000000000000000), (23966383 / 100000000000000000000000000000000)⟩ ⟨(-949201396249373474590457070135581 / 100000000000000000000000000000000), (158818684249 / 50000000000000000000000000000000)⟩ ⟨-14, 7545199268018009738646353009, 6103515625000000000000000000⟩,
   .log ⟨(16035475738875733852218175097 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(191320327118919030770614562963 / 12500000000000000000000000000000), (271651533 / 50000000000000000000000000000000)⟩ ⟨(-149138331031153994408879828874169 / 25000000000000000000000000000000), (211758237609 / 100000000000000000000000000000000)⟩ ⟨-9, 16035475738875733852218175097, 12207031250000000000000000000⟩,
   .log ⟨(24852298700834377326952470709 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(206273463219252053923611048123 / 100000000000000000000000000000000), (17103709 / 25000000000000000000000000000000)⟩ ⟨(-829997521365404894280747642876339 / 100000000000000000000000000000000), (137642855951 / 50000000000000000000000000000000)⟩ ⟨-12, 24852298700834377326952470709, 24414062500000000000000000000⟩]
lemma CA1_5_10I2R3Certificates_valid :
    CA1_5_10I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_5_10I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R3Certificates (CA1_5_10I2R3CertificateIndex a)).input
lemma CA1_5_10I2R3P_check : ∀ a : PairSlot, contains (CA1_5_10I2R3Raw a) (CA1_5_10I2R3P a) = true := by
  decide +kernel
lemma CA1_5_10I2R3P_sound (a : PairSlot) :
    (CA1_5_10I2R3P a).Encloses (CA1_5_10I2R3Value a) :=
  contains_sound (CA1_5_10I2R3Raw_sound a) (CA1_5_10I2R3P_check a)
def CA1_5_10I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R3Certificates (CA1_5_10I2R3CertificateIndex a)).output
lemma CA1_5_10I2R3Terms_sound (a : PairSlot) :
    (CA1_5_10I2R3Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R3Certificates_valid
    (CA1_5_10I2R3CertificateIndex a) (CA1_5_10I2R3P_sound a)
def CA1_5_10I2R3Entropy : Ball := ⟨(226056902121553594454825616307 / 6250000000000000000000000000000), (127136857 / 10000000000000000000000000000000)⟩
lemma CA1_5_10I2R3Entropy_sound : CA1_5_10I2R3Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R3Value CA1_5_10I2R3Terms CA1_5_10I2R3Terms_sound) (by decide +kernel)
def CA1_5_10I2R3Mass : Ball := ⟨(28896510979086412870108962527 / 5000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
lemma CA1_5_10I2R3Mass_sound : CA1_5_10I2R3Mass.Encloses (∑ a, CA1_5_10I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R3P CA1_5_10I2R3Value CA1_5_10I2R3P_sound) (by decide +kernel)
def CA1_5_10I2R3MassTermLogWitness : LogWitness := ⟨-8, 28896510979086412870108962527, 19531250000000000000000000000⟩
def CA1_5_10I2R3MassTermLog : Ball := ⟨(-128836808273830957315809414912993 / 25000000000000000000000000000000), (190582414531 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R3MassTermLog_sound : CA1_5_10I2R3MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I2R3Mass_sound) (w := CA1_5_10I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I2R3MassTerm : Ball := ⟨(2978347395836165963875989593137 / 100000000000000000000000000000000), (1101433409 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R3MassTerm_sound : CA1_5_10I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I2R3Mass_sound) CA1_5_10I2R3MassTermLog_sound) (by decide +kernel)
def CA1_5_10I2R3H : Ball := ⟨(25542521524347661896048810711 / 4000000000000000000000000000000), (2372801979 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R3H_sound : CA1_5_10I2R3H.Encloses (homogeneousEntropy CA1_5_10I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R3Value CA1_5_10I2R3MassTerm_sound CA1_5_10I2R3Entropy_sound) (by decide +kernel)
def CA1_5_10I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA1_5_10I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA1_5_10I2R4Raw_sound (a : PairSlot) :
    (CA1_5_10I2R4Raw a).Encloses (CA1_5_10I2R4Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA1_5_10I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(632871159398230728670782241 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(13396767985006072636062921341 / 50000000000000000000000000000000), (9113079 / 100000000000000000000000000000000)⟩ ⟨(-105841195210605492117564918365433 / 10000000000000000000000000000000), (359989042113 / 100000000000000000000000000000000)⟩ ⟨-16, 632871159398230728670782241, 381469726562500000000000000⟩,
   .log ⟨(20058892686705406523311807527 / 2000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(1153945440678932638698219878697 / 25000000000000000000000000000000), (212381791 / 12500000000000000000000000000000)⟩ ⟨(-115055746964910214632716111832649 / 25000000000000000000000000000000), (84703294981 / 50000000000000000000000000000000)⟩ ⟨-7, 20058892686705406523311807527, 15625000000000000000000000000⟩,
   .log ⟨(1065807453028293525913333569141 / 10000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(5965463960001714492232909133471 / 25000000000000000000000000000000), (5642337719 / 50000000000000000000000000000000)⟩ ⟨(-223885240924219805416967771004573 / 100000000000000000000000000000000), (105879118659 / 100000000000000000000000000000000)⟩ ⟨-4, 1065807453028293525913333569141, 625000000000000000000000000000⟩,
   .log ⟨(3453880792944542478296706953 / 625000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(359082936537564572837174392869 / 12500000000000000000000000000000), (1053198311 / 100000000000000000000000000000000)⟩ ⟨(-6497816479203003750205809534597 / 1250000000000000000000000000000), (190582413509 / 100000000000000000000000000000000)⟩ ⟨-8, 3453880792944542478296706953, 2441406250000000000000000000⟩,
   .log ⟨(1316827912981976963120678709 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(3699529166154410349622448903 / 25000000000000000000000000000000), (2509649 / 50000000000000000000000000000000)⟩ ⟨(-224753994333353395052494386894243 / 20000000000000000000000000000000), (190582451117 / 50000000000000000000000000000000)⟩ ⟨-17, 1316827912981976963120678709, 762939453125000000000000000⟩]
lemma CA1_5_10I2R4Certificates_valid :
    CA1_5_10I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA1_5_10I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R4Certificates (CA1_5_10I2R4CertificateIndex a)).input
lemma CA1_5_10I2R4P_check : ∀ a : PairSlot, contains (CA1_5_10I2R4Raw a) (CA1_5_10I2R4P a) = true := by
  decide +kernel
lemma CA1_5_10I2R4P_sound (a : PairSlot) :
    (CA1_5_10I2R4P a).Encloses (CA1_5_10I2R4Value a) :=
  contains_sound (CA1_5_10I2R4Raw_sound a) (CA1_5_10I2R4P_check a)
def CA1_5_10I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R4Certificates (CA1_5_10I2R4CertificateIndex a)).output
lemma CA1_5_10I2R4Terms_sound (a : PairSlot) :
    (CA1_5_10I2R4Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R4Certificates_valid
    (CA1_5_10I2R4CertificateIndex a) (CA1_5_10I2R4P_sound a)
def CA1_5_10I2R4Entropy : Ball := ⟨(1945356576932199708792746366517 / 5000000000000000000000000000000), (4203106543 / 25000000000000000000000000000000)⟩
lemma CA1_5_10I2R4Entropy_sound : CA1_5_10I2R4Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R4Value CA1_5_10I2R4Terms CA1_5_10I2R4Terms_sound) (by decide +kernel)
def CA1_5_10I2R4Mass : Ball := ⟨(13775585449883897327311949605707 / 100000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R4Mass_sound : CA1_5_10I2R4Mass.Encloses (∑ a, CA1_5_10I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R4P CA1_5_10I2R4Value CA1_5_10I2R4P_sound) (by decide +kernel)
def CA1_5_10I2R4MassTermLogWitness : LogWitness := ⟨-3, 13775585449883897327311949605707, 12500000000000000000000000000000⟩
def CA1_5_10I2R4MassTermLog : Ball := ⟨(-39645446619064765852647551025943 / 20000000000000000000000000000000), (84703295043 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R4MassTermLog_sound : CA1_5_10I2R4MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I2R4Mass_sound) (w := CA1_5_10I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I2R4MassTerm : Ball := ⟨(1365348093999343346937508993141 / 5000000000000000000000000000000), (11668374873 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R4MassTerm_sound : CA1_5_10I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I2R4Mass_sound) CA1_5_10I2R4MassTermLog_sound) (by decide +kernel)
def CA1_5_10I2R4H : Ball := ⟨(9062632545825880653988083959 / 78125000000000000000000000000), (5696160209 / 20000000000000000000000000000000)⟩
lemma CA1_5_10I2R4H_sound : CA1_5_10I2R4H.Encloses (homogeneousEntropy CA1_5_10I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R4Value CA1_5_10I2R4MassTerm_sound CA1_5_10I2R4Entropy_sound) (by decide +kernel)
def CA1_5_10I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA1_5_10I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA1_5_10I2R5Raw_sound (a : PairSlot) :
    (CA1_5_10I2R5Raw a).Encloses (CA1_5_10I2R5Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA1_5_10I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1258098169685637449695465587 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(171317453113904513126502808813 / 100000000000000000000000000000000), (14919111 / 25000000000000000000000000000000)⟩ ⟨(-851073555118078631593835392303337 / 100000000000000000000000000000000), (29646153653 / 10000000000000000000000000000000)⟩ ⟨-13, 1258098169685637449695465587, 762939453125000000000000000⟩,
   .log ⟨(6684646318168966297530337967463 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩ ⟨(13450910182909538526533189477777 / 50000000000000000000000000000000), (11324231421 / 100000000000000000000000000000000)⟩ ⟨(-50305242576371498699063217216007 / 25000000000000000000000000000000), (42351647459 / 50000000000000000000000000000000)⟩ ⟨-3, 6684646318168966297530337967463, 6250000000000000000000000000000⟩,
   .log ⟨(493377940579587723437131807133 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(524130184741895029846388666731 / 20000000000000000000000000000000), (470145799 / 50000000000000000000000000000000)⟩ ⟨(-531164997087406874113207080480883 / 100000000000000000000000000000000), (11911400847 / 6250000000000000000000000000000)⟩ ⟨-8, 493377940579587723437131807133, 390625000000000000000000000000⟩]
lemma CA1_5_10I2R5Certificates_valid :
    CA1_5_10I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA1_5_10I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R5Certificates (CA1_5_10I2R5CertificateIndex a)).input
lemma CA1_5_10I2R5P_check : ∀ a : PairSlot, contains (CA1_5_10I2R5Raw a) (CA1_5_10I2R5P a) = true := by
  decide +kernel
lemma CA1_5_10I2R5P_sound (a : PairSlot) :
    (CA1_5_10I2R5P a).Encloses (CA1_5_10I2R5Value a) :=
  contains_sound (CA1_5_10I2R5Raw_sound a) (CA1_5_10I2R5P_check a)
def CA1_5_10I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R5Certificates (CA1_5_10I2R5CertificateIndex a)).output
lemma CA1_5_10I2R5Terms_sound (a : PairSlot) :
    (CA1_5_10I2R5Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R5Certificates_valid
    (CA1_5_10I2R5CertificateIndex a) (CA1_5_10I2R5P_sound a)
def CA1_5_10I2R5Entropy : Ball := ⟨(14846894371321228357712412549011 / 25000000000000000000000000000000), (12324199463 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I2R5Entropy_sound : CA1_5_10I2R5Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R5Value CA1_5_10I2R5Terms CA1_5_10I2R5Terms_sound) (by decide +kernel)
def CA1_5_10I2R5Mass : Ball := ⟨(13882800147632490517692935191451 / 50000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
lemma CA1_5_10I2R5Mass_sound : CA1_5_10I2R5Mass.Encloses (∑ a, CA1_5_10I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R5P CA1_5_10I2R5Value CA1_5_10I2R5P_sound) (by decide +kernel)
def CA1_5_10I2R5MassTermLogWitness : LogWitness := ⟨-2, 13882800147632490517692935191451, 12500000000000000000000000000000⟩
def CA1_5_10I2R5MassTermLog : Ball := ⟨(-32034308273830957315809443556301 / 25000000000000000000000000000000), (50821977 / 80000000000000000000000000000)⟩
lemma CA1_5_10I2R5MassTermLog_sound : CA1_5_10I2R5MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I2R5Mass_sound) (w := CA1_5_10I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I2R5MassTerm : Ball := ⟨(35578071970659610136089639018193 / 100000000000000000000000000000000), (17638783817 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R5MassTerm_sound : CA1_5_10I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I2R5Mass_sound) CA1_5_10I2R5MassTermLog_sound) (by decide +kernel)
def CA1_5_10I2R5H : Ball := ⟨(23809505514625303294760011177851 / 100000000000000000000000000000000), (42287182743 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R5H_sound : CA1_5_10I2R5H.Encloses (homogeneousEntropy CA1_5_10I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R5Value CA1_5_10I2R5MassTerm_sound CA1_5_10I2R5Entropy_sound) (by decide +kernel)
def CA1_5_10I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA1_5_10I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA1_5_10I2R6Raw_sound (a : PairSlot) :
    (CA1_5_10I2R6Raw a).Encloses (CA1_5_10I2R6Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA1_5_10I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(35687513078880597433602857623 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(103422090723016740293707659229 / 20000000000000000000000000000000), (36274201 / 20000000000000000000000000000000)⟩ ⟨(-362248871525530095950681596372239 / 50000000000000000000000000000000), (63527471399 / 25000000000000000000000000000000)⟩ ⟨-11, 35687513078880597433602857623, 24414062500000000000000000000⟩,
   .log ⟨(2248454976633005517664593 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7607553095292825842435907 / 10000000000000000000000000000000), (12389 / 50000000000000000000000000000000)⟩ ⟨(-845864513004937999114364798625629 / 50000000000000000000000000000000), (2202374613 / 400000000000000000000000000000)⟩ ⟨-25, 2248454976633005517664593, 1490116119384765625000000⟩,
   .log ⟨(3742132954163165391913878812327 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩ ⟨(19401965815814233651433897567907 / 100000000000000000000000000000000), (3962137431 / 50000000000000000000000000000000)⟩ ⟨(-64809181199151831416449059873581 / 25000000000000000000000000000000), (4235164751 / 4000000000000000000000000000000)⟩ ⟨-4, 3742132954163165391913878812327, 3125000000000000000000000000000⟩]
lemma CA1_5_10I2R6Certificates_valid :
    CA1_5_10I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA1_5_10I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R6Certificates (CA1_5_10I2R6CertificateIndex a)).input
lemma CA1_5_10I2R6P_check : ∀ a : PairSlot, contains (CA1_5_10I2R6Raw a) (CA1_5_10I2R6P a) = true := by
  decide +kernel
lemma CA1_5_10I2R6P_sound (a : PairSlot) :
    (CA1_5_10I2R6P a).Encloses (CA1_5_10I2R6Value a) :=
  contains_sound (CA1_5_10I2R6Raw_sound a) (CA1_5_10I2R6P_check a)
def CA1_5_10I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R6Certificates (CA1_5_10I2R6CertificateIndex a)).output
lemma CA1_5_10I2R6Terms_sound (a : PairSlot) :
    (CA1_5_10I2R6Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R6Certificates_valid
    (CA1_5_10I2R6CertificateIndex a) (CA1_5_10I2R6P_sound a)
def CA1_5_10I2R6Entropy : Ball := ⟨(20436338874106306910887822878337 / 100000000000000000000000000000000), (2071766607 / 25000000000000000000000000000000)⟩
lemma CA1_5_10I2R6Entropy_sound : CA1_5_10I2R6Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R6Value CA1_5_10I2R6Terms CA1_5_10I2R6Terms_sound) (by decide +kernel)
def CA1_5_10I2R6Mass : Ball := ⟨(3813512477230879852792119856759 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R6Mass_sound : CA1_5_10I2R6Mass.Encloses (∑ a, CA1_5_10I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R6P CA1_5_10I2R6Value CA1_5_10I2R6P_sound) (by decide +kernel)
def CA1_5_10I2R6MassTermLogWitness : LogWitness := ⟨-4, 3813512477230879852792119856759, 3125000000000000000000000000000⟩
def CA1_5_10I2R6MassTermLog : Ball := ⟨(-257347233095323829263237736034197 / 100000000000000000000000000000000), (105879118821 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2R6MassTermLog_sound : CA1_5_10I2R6MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I2R6Mass_sound) (w := CA1_5_10I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I2R6MassTerm : Ball := ⟨(1226746105487326305680353180991 / 6250000000000000000000000000000), (4037713447 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I2R6MassTerm_sound : CA1_5_10I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I2R6Mass_sound) CA1_5_10I2R6MassTermLog_sound) (by decide +kernel)
def CA1_5_10I2R6H : Ball := ⟨(808401186309086020002171982481 / 100000000000000000000000000000000), (8181246661 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I2R6H_sound : CA1_5_10I2R6H.Encloses (homogeneousEntropy CA1_5_10I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R6Value CA1_5_10I2R6MassTerm_sound CA1_5_10I2R6Entropy_sound) (by decide +kernel)
def CA1_5_10I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA1_5_10I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA1_5_10I2R7Raw_sound (a : PairSlot) :
    (CA1_5_10I2R7Raw a).Encloses (CA1_5_10I2R7Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA1_5_10I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R7Certificates_valid :
    CA1_5_10I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R7Certificates (CA1_5_10I2R7CertificateIndex a)).input
lemma CA1_5_10I2R7P_check : ∀ a : PairSlot, contains (CA1_5_10I2R7Raw a) (CA1_5_10I2R7P a) = true := by
  decide +kernel
lemma CA1_5_10I2R7P_sound (a : PairSlot) :
    (CA1_5_10I2R7P a).Encloses (CA1_5_10I2R7Value a) :=
  contains_sound (CA1_5_10I2R7Raw_sound a) (CA1_5_10I2R7P_check a)
def CA1_5_10I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R7Certificates (CA1_5_10I2R7CertificateIndex a)).output
lemma CA1_5_10I2R7Terms_sound (a : PairSlot) :
    (CA1_5_10I2R7Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R7Certificates_valid
    (CA1_5_10I2R7CertificateIndex a) (CA1_5_10I2R7P_sound a)
def CA1_5_10I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R7Entropy_sound : CA1_5_10I2R7Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R7Value CA1_5_10I2R7Terms CA1_5_10I2R7Terms_sound) (by decide +kernel)
def CA1_5_10I2R7Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R7Mass_sound : CA1_5_10I2R7Mass.Encloses (∑ a, CA1_5_10I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R7P CA1_5_10I2R7Value CA1_5_10I2R7P_sound) (by decide +kernel)
def CA1_5_10I2R7MassTerm : Ball := .exact 0
lemma CA1_5_10I2R7MassTerm_sound : CA1_5_10I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R7Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R7Mass_sound)
def CA1_5_10I2R7H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R7H_sound : CA1_5_10I2R7H.Encloses (homogeneousEntropy CA1_5_10I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R7Value CA1_5_10I2R7MassTerm_sound CA1_5_10I2R7Entropy_sound) (by decide +kernel)
def CA1_5_10I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA1_5_10I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA1_5_10I2R8Raw_sound (a : PairSlot) :
    (CA1_5_10I2R8Raw a).Encloses (CA1_5_10I2R8Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA1_5_10I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R8Certificates_valid :
    CA1_5_10I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R8Certificates (CA1_5_10I2R8CertificateIndex a)).input
lemma CA1_5_10I2R8P_check : ∀ a : PairSlot, contains (CA1_5_10I2R8Raw a) (CA1_5_10I2R8P a) = true := by
  decide +kernel
lemma CA1_5_10I2R8P_sound (a : PairSlot) :
    (CA1_5_10I2R8P a).Encloses (CA1_5_10I2R8Value a) :=
  contains_sound (CA1_5_10I2R8Raw_sound a) (CA1_5_10I2R8P_check a)
def CA1_5_10I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R8Certificates (CA1_5_10I2R8CertificateIndex a)).output
lemma CA1_5_10I2R8Terms_sound (a : PairSlot) :
    (CA1_5_10I2R8Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R8Certificates_valid
    (CA1_5_10I2R8CertificateIndex a) (CA1_5_10I2R8P_sound a)
def CA1_5_10I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R8Entropy_sound : CA1_5_10I2R8Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R8Value CA1_5_10I2R8Terms CA1_5_10I2R8Terms_sound) (by decide +kernel)
def CA1_5_10I2R8Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R8Mass_sound : CA1_5_10I2R8Mass.Encloses (∑ a, CA1_5_10I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R8P CA1_5_10I2R8Value CA1_5_10I2R8P_sound) (by decide +kernel)
def CA1_5_10I2R8MassTerm : Ball := .exact 0
lemma CA1_5_10I2R8MassTerm_sound : CA1_5_10I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R8Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R8Mass_sound)
def CA1_5_10I2R8H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R8H_sound : CA1_5_10I2R8H.Encloses (homogeneousEntropy CA1_5_10I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R8Value CA1_5_10I2R8MassTerm_sound CA1_5_10I2R8Entropy_sound) (by decide +kernel)
def CA1_5_10I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA1_5_10I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA1_5_10I2R9Raw_sound (a : PairSlot) :
    (CA1_5_10I2R9Raw a).Encloses (CA1_5_10I2R9Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA1_5_10I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R9Certificates_valid :
    CA1_5_10I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R9Certificates (CA1_5_10I2R9CertificateIndex a)).input
lemma CA1_5_10I2R9P_check : ∀ a : PairSlot, contains (CA1_5_10I2R9Raw a) (CA1_5_10I2R9P a) = true := by
  decide +kernel
lemma CA1_5_10I2R9P_sound (a : PairSlot) :
    (CA1_5_10I2R9P a).Encloses (CA1_5_10I2R9Value a) :=
  contains_sound (CA1_5_10I2R9Raw_sound a) (CA1_5_10I2R9P_check a)
def CA1_5_10I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R9Certificates (CA1_5_10I2R9CertificateIndex a)).output
lemma CA1_5_10I2R9Terms_sound (a : PairSlot) :
    (CA1_5_10I2R9Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R9Certificates_valid
    (CA1_5_10I2R9CertificateIndex a) (CA1_5_10I2R9P_sound a)
def CA1_5_10I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R9Entropy_sound : CA1_5_10I2R9Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R9Value CA1_5_10I2R9Terms CA1_5_10I2R9Terms_sound) (by decide +kernel)
def CA1_5_10I2R9Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R9Mass_sound : CA1_5_10I2R9Mass.Encloses (∑ a, CA1_5_10I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R9P CA1_5_10I2R9Value CA1_5_10I2R9P_sound) (by decide +kernel)
def CA1_5_10I2R9MassTerm : Ball := .exact 0
lemma CA1_5_10I2R9MassTerm_sound : CA1_5_10I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R9Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R9Mass_sound)
def CA1_5_10I2R9H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R9H_sound : CA1_5_10I2R9H.Encloses (homogeneousEntropy CA1_5_10I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R9Value CA1_5_10I2R9MassTerm_sound CA1_5_10I2R9Entropy_sound) (by decide +kernel)
def CA1_5_10I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA1_5_10I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA1_5_10I2R10Raw_sound (a : PairSlot) :
    (CA1_5_10I2R10Raw a).Encloses (CA1_5_10I2R10Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA1_5_10I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R10Certificates_valid :
    CA1_5_10I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R10Certificates (CA1_5_10I2R10CertificateIndex a)).input
lemma CA1_5_10I2R10P_check : ∀ a : PairSlot, contains (CA1_5_10I2R10Raw a) (CA1_5_10I2R10P a) = true := by
  decide +kernel
lemma CA1_5_10I2R10P_sound (a : PairSlot) :
    (CA1_5_10I2R10P a).Encloses (CA1_5_10I2R10Value a) :=
  contains_sound (CA1_5_10I2R10Raw_sound a) (CA1_5_10I2R10P_check a)
def CA1_5_10I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R10Certificates (CA1_5_10I2R10CertificateIndex a)).output
lemma CA1_5_10I2R10Terms_sound (a : PairSlot) :
    (CA1_5_10I2R10Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R10Certificates_valid
    (CA1_5_10I2R10CertificateIndex a) (CA1_5_10I2R10P_sound a)
def CA1_5_10I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R10Entropy_sound : CA1_5_10I2R10Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R10Value CA1_5_10I2R10Terms CA1_5_10I2R10Terms_sound) (by decide +kernel)
def CA1_5_10I2R10Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R10Mass_sound : CA1_5_10I2R10Mass.Encloses (∑ a, CA1_5_10I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R10P CA1_5_10I2R10Value CA1_5_10I2R10P_sound) (by decide +kernel)
def CA1_5_10I2R10MassTerm : Ball := .exact 0
lemma CA1_5_10I2R10MassTerm_sound : CA1_5_10I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R10Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R10Mass_sound)
def CA1_5_10I2R10H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R10H_sound : CA1_5_10I2R10H.Encloses (homogeneousEntropy CA1_5_10I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R10Value CA1_5_10I2R10MassTerm_sound CA1_5_10I2R10Entropy_sound) (by decide +kernel)
def CA1_5_10I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA1_5_10I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA1_5_10I2R11Raw_sound (a : PairSlot) :
    (CA1_5_10I2R11Raw a).Encloses (CA1_5_10I2R11Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA1_5_10I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R11Certificates_valid :
    CA1_5_10I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R11Certificates (CA1_5_10I2R11CertificateIndex a)).input
lemma CA1_5_10I2R11P_check : ∀ a : PairSlot, contains (CA1_5_10I2R11Raw a) (CA1_5_10I2R11P a) = true := by
  decide +kernel
lemma CA1_5_10I2R11P_sound (a : PairSlot) :
    (CA1_5_10I2R11P a).Encloses (CA1_5_10I2R11Value a) :=
  contains_sound (CA1_5_10I2R11Raw_sound a) (CA1_5_10I2R11P_check a)
def CA1_5_10I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R11Certificates (CA1_5_10I2R11CertificateIndex a)).output
lemma CA1_5_10I2R11Terms_sound (a : PairSlot) :
    (CA1_5_10I2R11Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R11Certificates_valid
    (CA1_5_10I2R11CertificateIndex a) (CA1_5_10I2R11P_sound a)
def CA1_5_10I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R11Entropy_sound : CA1_5_10I2R11Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R11Value CA1_5_10I2R11Terms CA1_5_10I2R11Terms_sound) (by decide +kernel)
def CA1_5_10I2R11Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R11Mass_sound : CA1_5_10I2R11Mass.Encloses (∑ a, CA1_5_10I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R11P CA1_5_10I2R11Value CA1_5_10I2R11P_sound) (by decide +kernel)
def CA1_5_10I2R11MassTerm : Ball := .exact 0
lemma CA1_5_10I2R11MassTerm_sound : CA1_5_10I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R11Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R11Mass_sound)
def CA1_5_10I2R11H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R11H_sound : CA1_5_10I2R11H.Encloses (homogeneousEntropy CA1_5_10I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R11Value CA1_5_10I2R11MassTerm_sound CA1_5_10I2R11Entropy_sound) (by decide +kernel)
def CA1_5_10I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA1_5_10I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA1_5_10I2R12Raw_sound (a : PairSlot) :
    (CA1_5_10I2R12Raw a).Encloses (CA1_5_10I2R12Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA1_5_10I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R12Certificates_valid :
    CA1_5_10I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R12Certificates (CA1_5_10I2R12CertificateIndex a)).input
lemma CA1_5_10I2R12P_check : ∀ a : PairSlot, contains (CA1_5_10I2R12Raw a) (CA1_5_10I2R12P a) = true := by
  decide +kernel
lemma CA1_5_10I2R12P_sound (a : PairSlot) :
    (CA1_5_10I2R12P a).Encloses (CA1_5_10I2R12Value a) :=
  contains_sound (CA1_5_10I2R12Raw_sound a) (CA1_5_10I2R12P_check a)
def CA1_5_10I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R12Certificates (CA1_5_10I2R12CertificateIndex a)).output
lemma CA1_5_10I2R12Terms_sound (a : PairSlot) :
    (CA1_5_10I2R12Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R12Certificates_valid
    (CA1_5_10I2R12CertificateIndex a) (CA1_5_10I2R12P_sound a)
def CA1_5_10I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R12Entropy_sound : CA1_5_10I2R12Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R12Value CA1_5_10I2R12Terms CA1_5_10I2R12Terms_sound) (by decide +kernel)
def CA1_5_10I2R12Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R12Mass_sound : CA1_5_10I2R12Mass.Encloses (∑ a, CA1_5_10I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R12P CA1_5_10I2R12Value CA1_5_10I2R12P_sound) (by decide +kernel)
def CA1_5_10I2R12MassTerm : Ball := .exact 0
lemma CA1_5_10I2R12MassTerm_sound : CA1_5_10I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R12Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R12Mass_sound)
def CA1_5_10I2R12H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R12H_sound : CA1_5_10I2R12H.Encloses (homogeneousEntropy CA1_5_10I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R12Value CA1_5_10I2R12MassTerm_sound CA1_5_10I2R12Entropy_sound) (by decide +kernel)
def CA1_5_10I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA1_5_10I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA1_5_10I2R13Raw_sound (a : PairSlot) :
    (CA1_5_10I2R13Raw a).Encloses (CA1_5_10I2R13Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA1_5_10I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R13Certificates_valid :
    CA1_5_10I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R13Certificates (CA1_5_10I2R13CertificateIndex a)).input
lemma CA1_5_10I2R13P_check : ∀ a : PairSlot, contains (CA1_5_10I2R13Raw a) (CA1_5_10I2R13P a) = true := by
  decide +kernel
lemma CA1_5_10I2R13P_sound (a : PairSlot) :
    (CA1_5_10I2R13P a).Encloses (CA1_5_10I2R13Value a) :=
  contains_sound (CA1_5_10I2R13Raw_sound a) (CA1_5_10I2R13P_check a)
def CA1_5_10I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R13Certificates (CA1_5_10I2R13CertificateIndex a)).output
lemma CA1_5_10I2R13Terms_sound (a : PairSlot) :
    (CA1_5_10I2R13Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R13Certificates_valid
    (CA1_5_10I2R13CertificateIndex a) (CA1_5_10I2R13P_sound a)
def CA1_5_10I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R13Entropy_sound : CA1_5_10I2R13Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R13Value CA1_5_10I2R13Terms CA1_5_10I2R13Terms_sound) (by decide +kernel)
def CA1_5_10I2R13Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R13Mass_sound : CA1_5_10I2R13Mass.Encloses (∑ a, CA1_5_10I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R13P CA1_5_10I2R13Value CA1_5_10I2R13P_sound) (by decide +kernel)
def CA1_5_10I2R13MassTerm : Ball := .exact 0
lemma CA1_5_10I2R13MassTerm_sound : CA1_5_10I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R13Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R13Mass_sound)
def CA1_5_10I2R13H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R13H_sound : CA1_5_10I2R13H.Encloses (homogeneousEntropy CA1_5_10I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R13Value CA1_5_10I2R13MassTerm_sound CA1_5_10I2R13Entropy_sound) (by decide +kernel)
def CA1_5_10I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA1_5_10I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA1_5_10I2R14Raw_sound (a : PairSlot) :
    (CA1_5_10I2R14Raw a).Encloses (CA1_5_10I2R14Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA1_5_10I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R14Certificates_valid :
    CA1_5_10I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R14Certificates (CA1_5_10I2R14CertificateIndex a)).input
lemma CA1_5_10I2R14P_check : ∀ a : PairSlot, contains (CA1_5_10I2R14Raw a) (CA1_5_10I2R14P a) = true := by
  decide +kernel
lemma CA1_5_10I2R14P_sound (a : PairSlot) :
    (CA1_5_10I2R14P a).Encloses (CA1_5_10I2R14Value a) :=
  contains_sound (CA1_5_10I2R14Raw_sound a) (CA1_5_10I2R14P_check a)
def CA1_5_10I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R14Certificates (CA1_5_10I2R14CertificateIndex a)).output
lemma CA1_5_10I2R14Terms_sound (a : PairSlot) :
    (CA1_5_10I2R14Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R14Certificates_valid
    (CA1_5_10I2R14CertificateIndex a) (CA1_5_10I2R14P_sound a)
def CA1_5_10I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R14Entropy_sound : CA1_5_10I2R14Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R14Value CA1_5_10I2R14Terms CA1_5_10I2R14Terms_sound) (by decide +kernel)
def CA1_5_10I2R14Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R14Mass_sound : CA1_5_10I2R14Mass.Encloses (∑ a, CA1_5_10I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R14P CA1_5_10I2R14Value CA1_5_10I2R14P_sound) (by decide +kernel)
def CA1_5_10I2R14MassTerm : Ball := .exact 0
lemma CA1_5_10I2R14MassTerm_sound : CA1_5_10I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R14Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R14Mass_sound)
def CA1_5_10I2R14H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R14H_sound : CA1_5_10I2R14H.Encloses (homogeneousEntropy CA1_5_10I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R14Value CA1_5_10I2R14MassTerm_sound CA1_5_10I2R14Entropy_sound) (by decide +kernel)
def CA1_5_10I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA1_5_10I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA1_5_10I2R15Raw_sound (a : PairSlot) :
    (CA1_5_10I2R15Raw a).Encloses (CA1_5_10I2R15Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA1_5_10I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R15Certificates_valid :
    CA1_5_10I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R15Certificates (CA1_5_10I2R15CertificateIndex a)).input
lemma CA1_5_10I2R15P_check : ∀ a : PairSlot, contains (CA1_5_10I2R15Raw a) (CA1_5_10I2R15P a) = true := by
  decide +kernel
lemma CA1_5_10I2R15P_sound (a : PairSlot) :
    (CA1_5_10I2R15P a).Encloses (CA1_5_10I2R15Value a) :=
  contains_sound (CA1_5_10I2R15Raw_sound a) (CA1_5_10I2R15P_check a)
def CA1_5_10I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R15Certificates (CA1_5_10I2R15CertificateIndex a)).output
lemma CA1_5_10I2R15Terms_sound (a : PairSlot) :
    (CA1_5_10I2R15Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R15Certificates_valid
    (CA1_5_10I2R15CertificateIndex a) (CA1_5_10I2R15P_sound a)
def CA1_5_10I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R15Entropy_sound : CA1_5_10I2R15Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R15Value CA1_5_10I2R15Terms CA1_5_10I2R15Terms_sound) (by decide +kernel)
def CA1_5_10I2R15Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R15Mass_sound : CA1_5_10I2R15Mass.Encloses (∑ a, CA1_5_10I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R15P CA1_5_10I2R15Value CA1_5_10I2R15P_sound) (by decide +kernel)
def CA1_5_10I2R15MassTerm : Ball := .exact 0
lemma CA1_5_10I2R15MassTerm_sound : CA1_5_10I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R15Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R15Mass_sound)
def CA1_5_10I2R15H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R15H_sound : CA1_5_10I2R15H.Encloses (homogeneousEntropy CA1_5_10I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R15Value CA1_5_10I2R15MassTerm_sound CA1_5_10I2R15Entropy_sound) (by decide +kernel)
def CA1_5_10I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA1_5_10I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA1_5_10I2R16Raw_sound (a : PairSlot) :
    (CA1_5_10I2R16Raw a).Encloses (CA1_5_10I2R16Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA1_5_10I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I2R16Certificates_valid :
    CA1_5_10I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R16Certificates (CA1_5_10I2R16CertificateIndex a)).input
lemma CA1_5_10I2R16P_check : ∀ a : PairSlot, contains (CA1_5_10I2R16Raw a) (CA1_5_10I2R16P a) = true := by
  decide +kernel
lemma CA1_5_10I2R16P_sound (a : PairSlot) :
    (CA1_5_10I2R16P a).Encloses (CA1_5_10I2R16Value a) :=
  contains_sound (CA1_5_10I2R16Raw_sound a) (CA1_5_10I2R16P_check a)
def CA1_5_10I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R16Certificates (CA1_5_10I2R16CertificateIndex a)).output
lemma CA1_5_10I2R16Terms_sound (a : PairSlot) :
    (CA1_5_10I2R16Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I2R16Certificates_valid
    (CA1_5_10I2R16CertificateIndex a) (CA1_5_10I2R16P_sound a)
def CA1_5_10I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R16Entropy_sound : CA1_5_10I2R16Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I2R16Value CA1_5_10I2R16Terms CA1_5_10I2R16Terms_sound) (by decide +kernel)
def CA1_5_10I2R16Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R16Mass_sound : CA1_5_10I2R16Mass.Encloses (∑ a, CA1_5_10I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I2R16P CA1_5_10I2R16Value CA1_5_10I2R16P_sound) (by decide +kernel)
def CA1_5_10I2R16MassTerm : Ball := .exact 0
lemma CA1_5_10I2R16MassTerm_sound : CA1_5_10I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I2R16Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I2R16Mass_sound)
def CA1_5_10I2R16H : Ball := ⟨0, 0⟩
lemma CA1_5_10I2R16H_sound : CA1_5_10I2R16H.Encloses (homogeneousEntropy CA1_5_10I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I2R16Value CA1_5_10I2R16MassTerm_sound CA1_5_10I2R16Entropy_sound) (by decide +kernel)
def CA1_5_10I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_5_10I2R0H
  | 1 => CA1_5_10I2R1H
  | 2 => CA1_5_10I2R2H
  | 3 => CA1_5_10I2R3H
  | 4 => CA1_5_10I2R4H
  | 5 => CA1_5_10I2R5H
  | 6 => CA1_5_10I2R6H
  | 7 => CA1_5_10I2R7H
  | 8 => CA1_5_10I2R8H
  | 9 => CA1_5_10I2R9H
  | 10 => CA1_5_10I2R10H
  | 11 => CA1_5_10I2R11H
  | 12 => CA1_5_10I2R12H
  | 13 => CA1_5_10I2R13H
  | 14 => CA1_5_10I2R14H
  | 15 => CA1_5_10I2R15H
  | 16 => CA1_5_10I2R16H
  | _ => (.exact 0)
lemma CA1_5_10I2ResidualEntropies_sound (k : Fin 17) :
    (CA1_5_10I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_5_10I2R0H_sound
  · exact CA1_5_10I2R1H_sound
  · exact CA1_5_10I2R2H_sound
  · exact CA1_5_10I2R3H_sound
  · exact CA1_5_10I2R4H_sound
  · exact CA1_5_10I2R5H_sound
  · exact CA1_5_10I2R6H_sound
  · exact CA1_5_10I2R7H_sound
  · exact CA1_5_10I2R8H_sound
  · exact CA1_5_10I2R9H_sound
  · exact CA1_5_10I2R10H_sound
  · exact CA1_5_10I2R11H_sound
  · exact CA1_5_10I2R12H_sound
  · exact CA1_5_10I2R13H_sound
  · exact CA1_5_10I2R14H_sound
  · exact CA1_5_10I2R15H_sound
  · exact CA1_5_10I2R16H_sound
def CA1_5_10I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 1, 0, 7 => Z1_0_7H2H
  | _, _, _ => (.exact 0)
lemma CA1_5_10I2Singles_sound (u : Shape) (hu : u ∈ below (shape 1 5 10))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA1_5_10I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A1_5_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def CA1_5_10I2Singleton : Ball := ⟨(58076349994733647690213708595139 / 100000000000000000000000000000000), (4925097331 / 10000000000000000000000000000000)⟩
lemma CA1_5_10I2Singleton_sound : CA1_5_10I2Singleton.Encloses
    (singletonEntropy (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA1_5_10I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) CA1_5_10I2Singles_sound) (by decide +kernel)
def CA1_5_10I2Group : Ball := ⟨(9493581015904919494732526364841 / 10000000000000000000000000000000), (69387122503 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I2Group_sound : CA1_5_10I2Group.Encloses
    (groupedEntropy (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_5_10I2Singleton_sound
    (finSumBall_sound 17 CA1_5_10I2ResidualEntropies _ CA1_5_10I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA1_5_10I2H : Ball := ⟨(22944437233655845349730535613301 / 20000000000000000000000000000000), (449433388731 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I2_sound : CA1_5_10I2H.Encloses (stageACapacity (shape 1 5 10) 2) := by
  have hb := contains_sound (Ball.add_sound CA1_5_10I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_5_10I2Group_sound)))
    (show contains (.add CA1_5_10I2PairH (.neg (.mul (.exact 2) CA1_5_10I2Group))) CA1_5_10I2H = true by decide +kernel)
  unfold CA1_5_10I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
