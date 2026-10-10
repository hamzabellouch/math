import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA3_5_8I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_5_8I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA3_5_8I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA3_5_8I2R0Raw_sound (a : PairSlot) :
    (CA3_5_8I2R0Raw a).Encloses (CA3_5_8I2R0Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA3_5_8I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5617321274602978972531421 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(11722525042486881302899449 / 12500000000000000000000000000000), (15473 / 50000000000000000000000000000000)⟩ ⟨(-834741291760308362723103481718601 / 50000000000000000000000000000000), (550589217837 / 100000000000000000000000000000000)⟩ ⟨-25, 5617321274602978972531421, 2980232238769531250000000⟩]
lemma CA3_5_8I2R0Certificates_valid :
    CA3_5_8I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA3_5_8I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R0Certificates (CA3_5_8I2R0CertificateIndex a)).input
lemma CA3_5_8I2R0P_check : ∀ a : PairSlot, contains (CA3_5_8I2R0Raw a) (CA3_5_8I2R0P a) = true := by
  decide +kernel
lemma CA3_5_8I2R0P_sound (a : PairSlot) :
    (CA3_5_8I2R0P a).Encloses (CA3_5_8I2R0Value a) :=
  contains_sound (CA3_5_8I2R0Raw_sound a) (CA3_5_8I2R0P_check a)
def CA3_5_8I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R0Certificates (CA3_5_8I2R0CertificateIndex a)).output
lemma CA3_5_8I2R0Terms_sound (a : PairSlot) :
    (CA3_5_8I2R0Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R0Certificates_valid
    (CA3_5_8I2R0CertificateIndex a) (CA3_5_8I2R0P_sound a)
def CA3_5_8I2R0Entropy : Ball := ⟨(11722525042486881302899449 / 12500000000000000000000000000000), (15473 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I2R0Entropy_sound : CA3_5_8I2R0Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R0Value CA3_5_8I2R0Terms CA3_5_8I2R0Terms_sound) (by decide +kernel)
def CA3_5_8I2R0Mass : Ball := ⟨(5617321274602978972531421 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2R0Mass_sound : CA3_5_8I2R0Mass.Encloses (∑ a, CA3_5_8I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R0P CA3_5_8I2R0Value CA3_5_8I2R0P_sound) (by decide +kernel)
def CA3_5_8I2R0MassTermLogWitness : LogWitness := ⟨-25, 5617321274602978972531421, 2980232238769531250000000⟩
def CA3_5_8I2R0MassTermLog : Ball := ⟨(-834741291760308362723103481718601 / 50000000000000000000000000000000), (550589217837 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2R0MassTermLog_sound : CA3_5_8I2R0MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I2R0Mass_sound) (w := CA3_5_8I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I2R0MassTerm : Ball := ⟨(11722525042486881302899449 / 12500000000000000000000000000000), (15473 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I2R0MassTerm_sound : CA3_5_8I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I2R0Mass_sound) CA3_5_8I2R0MassTermLog_sound) (by decide +kernel)
def CA3_5_8I2R0H : Ball := ⟨0, (15473 / 25000000000000000000000000000000)⟩
lemma CA3_5_8I2R0H_sound : CA3_5_8I2R0H.Encloses (homogeneousEntropy CA3_5_8I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R0Value CA3_5_8I2R0MassTerm_sound CA3_5_8I2R0Entropy_sound) (by decide +kernel)
def CA3_5_8I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA3_5_8I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA3_5_8I2R1Raw_sound (a : PairSlot) :
    (CA3_5_8I2R1Raw a).Encloses (CA3_5_8I2R1Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA3_5_8I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(819643483877255325795700097 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(33852970621212845371812639747 / 100000000000000000000000000000000), (1388533 / 12500000000000000000000000000000)⟩ ⟨(-516275845643800271607790499417917 / 50000000000000000000000000000000), (338813239929 / 100000000000000000000000000000000)⟩ ⟨-15, 819643483877255325795700097, 762939453125000000000000000⟩]
lemma CA3_5_8I2R1Certificates_valid :
    CA3_5_8I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA3_5_8I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R1Certificates (CA3_5_8I2R1CertificateIndex a)).input
lemma CA3_5_8I2R1P_check : ∀ a : PairSlot, contains (CA3_5_8I2R1Raw a) (CA3_5_8I2R1P a) = true := by
  decide +kernel
lemma CA3_5_8I2R1P_sound (a : PairSlot) :
    (CA3_5_8I2R1P a).Encloses (CA3_5_8I2R1Value a) :=
  contains_sound (CA3_5_8I2R1Raw_sound a) (CA3_5_8I2R1P_check a)
def CA3_5_8I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R1Certificates (CA3_5_8I2R1CertificateIndex a)).output
lemma CA3_5_8I2R1Terms_sound (a : PairSlot) :
    (CA3_5_8I2R1Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R1Certificates_valid
    (CA3_5_8I2R1CertificateIndex a) (CA3_5_8I2R1P_sound a)
def CA3_5_8I2R1Entropy : Ball := ⟨(33852970621212845371812639747 / 50000000000000000000000000000000), (1388533 / 6250000000000000000000000000000)⟩
lemma CA3_5_8I2R1Entropy_sound : CA3_5_8I2R1Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R1Value CA3_5_8I2R1Terms CA3_5_8I2R1Terms_sound) (by decide +kernel)
def CA3_5_8I2R1Mass : Ball := ⟨(819643483877255325795700097 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma CA3_5_8I2R1Mass_sound : CA3_5_8I2R1Mass.Encloses (∑ a, CA3_5_8I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R1P CA3_5_8I2R1Value CA3_5_8I2R1P_sound) (by decide +kernel)
def CA3_5_8I2R1MassTermLogWitness : LogWitness := ⟨-14, 819643483877255325795700097, 762939453125000000000000000⟩
def CA3_5_8I2R1MassTermLog : Ball := ⟨(-30101155413487687883558056430797 / 3125000000000000000000000000000), (158818708123 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I2R1MassTermLog_sound : CA3_5_8I2R1MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I2R1Mass_sound) (w := CA3_5_8I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I2R1MassTerm : Ball := ⟨(63160872683114886588371371791 / 100000000000000000000000000000000), (10413997 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I2R1MassTerm_sound : CA3_5_8I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I2R1Mass_sound) CA3_5_8I2R1MassTermLog_sound) (by decide +kernel)
def CA3_5_8I2R1H : Ball := ⟨(4545068559310804155253907703 / 100000000000000000000000000000000), (21522261 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I2R1H_sound : CA3_5_8I2R1H.Encloses (homogeneousEntropy CA3_5_8I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R1Value CA3_5_8I2R1MassTerm_sound CA3_5_8I2R1Entropy_sound) (by decide +kernel)
def CA3_5_8I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA3_5_8I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA3_5_8I2R2Raw_sound (a : PairSlot) :
    (CA3_5_8I2R2Raw a).Encloses (CA3_5_8I2R2Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA3_5_8I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(73061871263674035466020477951 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(953964710580137564315522468887 / 100000000000000000000000000000000), (340371983 / 100000000000000000000000000000000)⟩ ⟨(-6528471650673718944305571000311 / 1000000000000000000000000000000), (232934061881 / 100000000000000000000000000000000)⟩ ⟨-10, 73061871263674035466020477951, 48828125000000000000000000000⟩,
   .log ⟨(1336872593667894027129692273 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(48892911551732387697467706271 / 50000000000000000000000000000000), (6794253 / 20000000000000000000000000000000)⟩ ⟨(-11428938653006742649771550946379 / 1250000000000000000000000000000), (63527472919 / 20000000000000000000000000000000)⟩ ⟨-14, 1336872593667894027129692273, 762939453125000000000000000⟩,
   .log ⟨(267631277469984174023431040809 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(2799513130100671885848869370833 / 100000000000000000000000000000000), (510058163 / 50000000000000000000000000000000)⟩ ⟨(-20920672326235467868866129270777 / 4000000000000000000000000000000), (148892511 / 78125000000000000000000000000)⟩ ⟨-8, 267631277469984174023431040809, 195312500000000000000000000000⟩]
lemma CA3_5_8I2R2Certificates_valid :
    CA3_5_8I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA3_5_8I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R2Certificates (CA3_5_8I2R2CertificateIndex a)).input
lemma CA3_5_8I2R2P_check : ∀ a : PairSlot, contains (CA3_5_8I2R2Raw a) (CA3_5_8I2R2P a) = true := by
  decide +kernel
lemma CA3_5_8I2R2P_sound (a : PairSlot) :
    (CA3_5_8I2R2P a).Encloses (CA3_5_8I2R2Value a) :=
  contains_sound (CA3_5_8I2R2Raw_sound a) (CA3_5_8I2R2P_check a)
def CA3_5_8I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R2Certificates (CA3_5_8I2R2CertificateIndex a)).output
lemma CA3_5_8I2R2Terms_sound (a : PairSlot) :
    (CA3_5_8I2R2Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R2Certificates_valid
    (CA3_5_8I2R2CertificateIndex a) (CA3_5_8I2R2P_sound a)
def CA3_5_8I2R2Entropy : Ball := ⟨(4903014197467876565269785133691 / 100000000000000000000000000000000), (884401411 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I2R2Entropy_sound : CA3_5_8I2R2Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R2Value CA3_5_8I2R2Terms CA3_5_8I2R2Terms_sound) (by decide +kernel)
def CA3_5_8I2R2Mass : Ball := ⟨(84890000149335079434501906979 / 10000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2R2Mass_sound : CA3_5_8I2R2Mass.Encloses (∑ a, CA3_5_8I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R2P CA3_5_8I2R2Value CA3_5_8I2R2P_sound) (by decide +kernel)
def CA3_5_8I2R2MassTermLogWitness : LogWitness := ⟨-7, 84890000149335079434501906979, 78125000000000000000000000000⟩
def CA3_5_8I2R2MassTermLog : Ball := ⟨(-238449203473357323046087830923007 / 50000000000000000000000000000000), (169406590759 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2R2MassTermLog_sound : CA3_5_8I2R2MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I2R2Mass_sound) (w := CA3_5_8I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I2R2MassTerm : Ball := ⟨(4048390583692426779033983965233 / 100000000000000000000000000000000), (287618521 / 20000000000000000000000000000000)⟩
lemma CA3_5_8I2R2MassTerm_sound : CA3_5_8I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I2R2Mass_sound) CA3_5_8I2R2MassTermLog_sound) (by decide +kernel)
def CA3_5_8I2R2H : Ball := ⟨(427311806887724893117900584229 / 50000000000000000000000000000000), (3206895427 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2R2H_sound : CA3_5_8I2R2H.Encloses (homogeneousEntropy CA3_5_8I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R2Value CA3_5_8I2R2MassTerm_sound CA3_5_8I2R2Entropy_sound) (by decide +kernel)
def CA3_5_8I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA3_5_8I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA3_5_8I2R3Raw_sound (a : PairSlot) :
    (CA3_5_8I2R3Raw a).Encloses (CA3_5_8I2R3Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA3_5_8I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(114432923476017216855001848883 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(278291232547230390018297663339 / 20000000000000000000000000000000), (484642297 / 100000000000000000000000000000000)⟩ ⟨(-60797894542464105366859956245389 / 10000000000000000000000000000000), (211758237703 / 100000000000000000000000000000000)⟩ ⟨-9, 114432923476017216855001848883, 97656250000000000000000000000⟩,
   .log ⟨(2015811315541798639738563494089 / 25000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩ ⟨(10151037460539537534979681725353 / 50000000000000000000000000000000), (1707458621 / 20000000000000000000000000000000)⟩ ⟨(-251785407252047241134671699626059 / 100000000000000000000000000000000), (105879118787 / 100000000000000000000000000000000)⟩ ⟨-4, 2015811315541798639738563494089, 1562500000000000000000000000000⟩,
   .log ⟨(434457685864110007470395693047 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(472588030698096616469765039973 / 20000000000000000000000000000000), (413999981 / 50000000000000000000000000000000)⟩ ⟨(-543882691082041354570493676746759 / 100000000000000000000000000000000), (190582413837 / 100000000000000000000000000000000)⟩ ⟨-8, 434457685864110007470395693047, 390625000000000000000000000000⟩]
lemma CA3_5_8I2R3Certificates_valid :
    CA3_5_8I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA3_5_8I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R3Certificates (CA3_5_8I2R3CertificateIndex a)).input
lemma CA3_5_8I2R3P_check : ∀ a : PairSlot, contains (CA3_5_8I2R3Raw a) (CA3_5_8I2R3P a) = true := by
  decide +kernel
lemma CA3_5_8I2R3P_sound (a : PairSlot) :
    (CA3_5_8I2R3P a).Encloses (CA3_5_8I2R3Value a) :=
  contains_sound (CA3_5_8I2R3Raw_sound a) (CA3_5_8I2R3P_check a)
def CA3_5_8I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R3Certificates (CA3_5_8I2R3CertificateIndex a)).output
lemma CA3_5_8I2R3Terms_sound (a : PairSlot) :
    (CA3_5_8I2R3Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R3Certificates_valid
    (CA3_5_8I2R3CertificateIndex a) (CA3_5_8I2R3P_sound a)
def CA3_5_8I2R3Entropy : Ball := ⟨(12028235618652855051199838483633 / 25000000000000000000000000000000), (2462483841 / 12500000000000000000000000000000)⟩
lemma CA3_5_8I2R3Entropy_sound : CA3_5_8I2R3Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R3Value CA3_5_8I2R3Terms CA3_5_8I2R3Terms_sound) (by decide +kernel)
def CA3_5_8I2R3Mass : Ball := ⟨(8726568794983339000134653367169 / 50000000000000000000000000000000), (7 / 10000000000000000000000000000000)⟩
lemma CA3_5_8I2R3Mass_sound : CA3_5_8I2R3Mass.Encloses (∑ a, CA3_5_8I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R3P CA3_5_8I2R3Value CA3_5_8I2R3P_sound) (by decide +kernel)
def CA3_5_8I2R3MassTermLogWitness : LogWitness := ⟨-3, 8726568794983339000134653367169, 6250000000000000000000000000000⟩
def CA3_5_8I2R3MassTermLog : Ball := ⟨(-174565074891994409889667767275929 / 100000000000000000000000000000000), (21175823783 / 25000000000000000000000000000000)⟩
lemma CA3_5_8I2R3MassTermLog_sound : CA3_5_8I2R3MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I2R3Mass_sound) (w := CA3_5_8I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I2R3MassTerm : Ball := ⟨(7616770676232039919841721935443 / 25000000000000000000000000000000), (7391691383 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I2R3MassTerm_sound : CA3_5_8I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I2R3Mass_sound) CA3_5_8I2R3MassTermLog_sound) (by decide +kernel)
def CA3_5_8I2R3H : Ball := ⟨(441146494242081513135811654819 / 2500000000000000000000000000000), (17241626747 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I2R3H_sound : CA3_5_8I2R3H.Encloses (homogeneousEntropy CA3_5_8I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R3Value CA3_5_8I2R3MassTerm_sound CA3_5_8I2R3Entropy_sound) (by decide +kernel)
def CA3_5_8I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA3_5_8I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA3_5_8I2R4Raw_sound (a : PairSlot) :
    (CA3_5_8I2R4Raw a).Encloses (CA3_5_8I2R4Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA3_5_8I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(12022196877875889184523436251 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(54257201109417207674614979791 / 50000000000000000000000000000000), (38186999 / 100000000000000000000000000000000)⟩ ⟨(-902617078402121479264179184702111 / 100000000000000000000000000000000), (158818681781 / 50000000000000000000000000000000)⟩ ⟨-14, 12022196877875889184523436251, 6103515625000000000000000000⟩,
   .log ⟨(4313474067026207097462872240937 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩ ⟨(6779544470890384077944803063867 / 50000000000000000000000000000000), (5480482053 / 100000000000000000000000000000000)⟩ ⟨(-19646415990754796262843556271099 / 6250000000000000000000000000000), (25410988503 / 20000000000000000000000000000000)⟩ ⟨-5, 4313474067026207097462872240937, 3125000000000000000000000000000⟩,
   .log ⟨(45177057741556546528261888037303 / 100000000000000000000000000000000), (101 / 100000000000000000000000000000000)⟩ ⟨(17948411343172564815437949038557 / 50000000000000000000000000000000), (28699842459 / 100000000000000000000000000000000)⟩ ⟨(-79458080009768089968269588345363 / 100000000000000000000000000000000), (7940933909 / 12500000000000000000000000000000)⟩ ⟨-2, 45177057741556546528261888037303, 25000000000000000000000000000000⟩,
   .log ⟨(2125556867426515782967876968221 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(1023226167887011655843502466643 / 12500000000000000000000000000000), (393841157 / 12500000000000000000000000000000)⟩ ⟨(-24069602266766602361450619164371 / 6250000000000000000000000000000), (14823076611 / 10000000000000000000000000000000)⟩ ⟨-6, 2125556867426515782967876968221, 1562500000000000000000000000000⟩,
   .log ⟨(2214285087953012365889331869 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(311289353354744148483942266479 / 50000000000000000000000000000000), (56267177 / 25000000000000000000000000000000)⟩ ⟨(-702911641884637438998422078641927 / 100000000000000000000000000000000), (127054943227 / 50000000000000000000000000000000)⟩ ⟨-11, 2214285087953012365889331869, 1220703125000000000000000000⟩]
lemma CA3_5_8I2R4Certificates_valid :
    CA3_5_8I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA3_5_8I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R4Certificates (CA3_5_8I2R4CertificateIndex a)).input
lemma CA3_5_8I2R4P_check : ∀ a : PairSlot, contains (CA3_5_8I2R4Raw a) (CA3_5_8I2R4P a) = true := by
  decide +kernel
lemma CA3_5_8I2R4P_sound (a : PairSlot) :
    (CA3_5_8I2R4P a).Encloses (CA3_5_8I2R4Value a) :=
  contains_sound (CA3_5_8I2R4Raw_sound a) (CA3_5_8I2R4P_check a)
def CA3_5_8I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R4Certificates (CA3_5_8I2R4CertificateIndex a)).output
lemma CA3_5_8I2R4Terms_sound (a : PairSlot) :
    (CA3_5_8I2R4Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R4Certificates_valid
    (CA3_5_8I2R4CertificateIndex a) (CA3_5_8I2R4P_sound a)
def CA3_5_8I2R4Entropy : Ball := ⟨(5014139172952875597738593390687 / 6250000000000000000000000000000), (46263707783 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2R4Entropy_sound : CA3_5_8I2R4Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R4Value CA3_5_8I2R4Terms CA3_5_8I2R4Terms_sound) (by decide +kernel)
def CA3_5_8I2R4Mass : Ball := ⟨(58167735407735864562128006602881 / 100000000000000000000000000000000), (31 / 20000000000000000000000000000000)⟩
lemma CA3_5_8I2R4Mass_sound : CA3_5_8I2R4Mass.Encloses (∑ a, CA3_5_8I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R4P CA3_5_8I2R4Value CA3_5_8I2R4P_sound) (by decide +kernel)
def CA3_5_8I2R4MassTermLogWitness : LogWitness := ⟨-1, 58167735407735864562128006602881, 50000000000000000000000000000000⟩
def CA3_5_8I2R4MassTermLog : Ball := ⟨(-27091967970527579926082113059819 / 50000000000000000000000000000000), (2646977977 / 6250000000000000000000000000000)⟩
lemma CA3_5_8I2R4MassTermLog_sound : CA3_5_8I2R4MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I2R4Mass_sound) (w := CA3_5_8I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I2R4MassTerm : Ball := ⟨(3151756849169006124968414455831 / 10000000000000000000000000000000), (1231749721 / 5000000000000000000000000000000)⟩
lemma CA3_5_8I2R4MassTerm_sound : CA3_5_8I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I2R4Mass_sound) CA3_5_8I2R4MassTermLog_sound) (by decide +kernel)
def CA3_5_8I2R4H : Ball := ⟨(24354329137777974157066674846341 / 50000000000000000000000000000000), (70898702203 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2R4H_sound : CA3_5_8I2R4H.Encloses (homogeneousEntropy CA3_5_8I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R4Value CA3_5_8I2R4MassTerm_sound CA3_5_8I2R4Entropy_sound) (by decide +kernel)
def CA3_5_8I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA3_5_8I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA3_5_8I2R5Raw_sound (a : PairSlot) :
    (CA3_5_8I2R5Raw a).Encloses (CA3_5_8I2R5Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA3_5_8I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(9942282739469559574436285509 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(9162935847997859206549044161 / 10000000000000000000000000000000), (6316083 / 20000000000000000000000000000000)⟩ ⟨(-57600805117559953438689508166951 / 6250000000000000000000000000000), (317637365303 / 100000000000000000000000000000000)⟩ ⟨-14, 9942282739469559574436285509, 6103515625000000000000000000⟩,
   .log ⟨(6181633525742884277323392971037 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩ ⟨(3441423716775335459622773796143 / 20000000000000000000000000000000), (1570814197 / 20000000000000000000000000000000)⟩ ⟨(-278358762489220740678403150827949 / 100000000000000000000000000000000), (12705494247 / 10000000000000000000000000000000)⟩ ⟨-5, 6181633525742884277323392971037, 3125000000000000000000000000000⟩,
   .log ⟨(115092730158440709709968830601 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1398155723714242694181480175331 / 100000000000000000000000000000000), (487436687 / 100000000000000000000000000000000)⟩ ⟨(-303702006588403158829656558252789 / 50000000000000000000000000000000), (105879118849 / 50000000000000000000000000000000)⟩ ⟨-9, 115092730158440709709968830601, 97656250000000000000000000000⟩]
lemma CA3_5_8I2R5Certificates_valid :
    CA3_5_8I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA3_5_8I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R5Certificates (CA3_5_8I2R5CertificateIndex a)).input
lemma CA3_5_8I2R5P_check : ∀ a : PairSlot, contains (CA3_5_8I2R5Raw a) (CA3_5_8I2R5P a) = true := by
  decide +kernel
lemma CA3_5_8I2R5P_sound (a : PairSlot) :
    (CA3_5_8I2R5P a).Encloses (CA3_5_8I2R5Value a) :=
  contains_sound (CA3_5_8I2R5Raw_sound a) (CA3_5_8I2R5P_check a)
def CA3_5_8I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R5Certificates (CA3_5_8I2R5CertificateIndex a)).output
lemma CA3_5_8I2R5Terms_sound (a : PairSlot) :
    (CA3_5_8I2R5Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R5Certificates_valid
    (CA3_5_8I2R5CertificateIndex a) (CA3_5_8I2R5P_sound a)
def CA3_5_8I2R5Entropy : Ball := ⟨(2337112958258862323045104949707 / 6250000000000000000000000000000), (8373088087 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I2R5Entropy_sound : CA3_5_8I2R5Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R5Value CA3_5_8I2R5Terms CA3_5_8I2R5Terms_sound) (by decide +kernel)
def CA3_5_8I2R5Mass : Ball := ⟨(1605440317199808814079441729437 / 12500000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
lemma CA3_5_8I2R5Mass_sound : CA3_5_8I2R5Mass.Encloses (∑ a, CA3_5_8I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R5P CA3_5_8I2R5Value CA3_5_8I2R5P_sound) (by decide +kernel)
def CA3_5_8I2R5MassTermLogWitness : LogWitness := ⟨-3, 1605440317199808814079441729437, 1562500000000000000000000000000⟩
def CA3_5_8I2R5MassTermLog : Ball := ⟨(-25654132305205111739328766222689 / 12500000000000000000000000000000), (2646977973 / 3125000000000000000000000000000)⟩
lemma CA3_5_8I2R5MassTermLog_sound : CA3_5_8I2R5MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I2R5Mass_sound) (w := CA3_5_8I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I2R5MassTerm : Ball := ⟨(26359154115554788539487055265713 / 100000000000000000000000000000000), (2719721727 / 25000000000000000000000000000000)⟩
lemma CA3_5_8I2R5MassTerm_sound : CA3_5_8I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I2R5Mass_sound) CA3_5_8I2R5MassTermLog_sound) (by decide +kernel)
def CA3_5_8I2R5H : Ball := ⟨(11034653216587008629234623929599 / 100000000000000000000000000000000), (13812531541 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I2R5H_sound : CA3_5_8I2R5H.Encloses (homogeneousEntropy CA3_5_8I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R5Value CA3_5_8I2R5MassTerm_sound CA3_5_8I2R5Entropy_sound) (by decide +kernel)
def CA3_5_8I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA3_5_8I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA3_5_8I2R6Raw_sound (a : PairSlot) :
    (CA3_5_8I2R6Raw a).Encloses (CA3_5_8I2R6Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA3_5_8I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3201740378379992765626809327 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(6627110113802342717611462361 / 20000000000000000000000000000000), (10847931 / 100000000000000000000000000000000)⟩ ⟨(-1034923093476353088084332758064927 / 100000000000000000000000000000000), (4235165127 / 1250000000000000000000000000000)⟩ ⟨-15, 3201740378379992765626809327, 3051757812500000000000000000⟩,
   .log ⟨(40344470469227470177519 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1972066848508867464967 / 48828125000000000000000000000), (1303 / 100000000000000000000000000000000)⟩ ⟨(-2002154376435168894411699120477917 / 100000000000000000000000000000000), (635770441373 / 100000000000000000000000000000000)⟩ ⟨-29, 40344470469227470177519, 37252902984619140625000⟩,
   .log ⟨(335729142967404254620887392339 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1912521602952815363567260599791 / 100000000000000000000000000000000), (142186827 / 20000000000000000000000000000000)⟩ ⟨(-569662075221900221848765785723993 / 100000000000000000000000000000000), (211758237723 / 100000000000000000000000000000000)⟩ ⟨-9, 335729142967404254620887392339, 195312500000000000000000000000⟩]
lemma CA3_5_8I2R6Certificates_valid :
    CA3_5_8I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA3_5_8I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R6Certificates (CA3_5_8I2R6CertificateIndex a)).input
lemma CA3_5_8I2R6P_check : ∀ a : PairSlot, contains (CA3_5_8I2R6Raw a) (CA3_5_8I2R6P a) = true := by
  decide +kernel
lemma CA3_5_8I2R6P_sound (a : PairSlot) :
    (CA3_5_8I2R6P a).Encloses (CA3_5_8I2R6Value a) :=
  contains_sound (CA3_5_8I2R6Raw_sound a) (CA3_5_8I2R6P_check a)
def CA3_5_8I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R6Certificates (CA3_5_8I2R6CertificateIndex a)).output
lemma CA3_5_8I2R6Terms_sound (a : PairSlot) :
    (CA3_5_8I2R6Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R6Certificates_valid
    (CA3_5_8I2R6CertificateIndex a) (CA3_5_8I2R6P_sound a)
def CA3_5_8I2R6Entropy : Ball := ⟨(1978800781676650283064511728233 / 100000000000000000000000000000000), (732632603 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2R6Entropy_sound : CA3_5_8I2R6Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R6Value CA3_5_8I2R6Terms CA3_5_8I2R6Terms_sound) (by decide +kernel)
def CA3_5_8I2R6Mass : Ball := ⟨(342133027168868932426842786183 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2R6Mass_sound : CA3_5_8I2R6Mass.Encloses (∑ a, CA3_5_8I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R6P CA3_5_8I2R6Value CA3_5_8I2R6P_sound) (by decide +kernel)
def CA3_5_8I2R6MassTermLogWitness : LogWitness := ⟨-9, 342133027168868932426842786183, 195312500000000000000000000000⟩
def CA3_5_8I2R6MassTermLog : Ball := ⟨(-283886291760308362723103641132293 / 50000000000000000000000000000000), (52939559719 / 25000000000000000000000000000000)⟩
lemma CA3_5_8I2R6MassTermLog_sound : CA3_5_8I2R6MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I2R6Mass_sound) (w := CA3_5_8I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I2R6MassTerm : Ball := ⟨(1942537527433980672240958010263 / 100000000000000000000000000000000), (724494913 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2R6MassTerm_sound : CA3_5_8I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I2R6Mass_sound) CA3_5_8I2R6MassTermLog_sound) (by decide +kernel)
def CA3_5_8I2R6H : Ball := ⟨(3626325424266961082355371797 / 10000000000000000000000000000000), (364281879 / 25000000000000000000000000000000)⟩
lemma CA3_5_8I2R6H_sound : CA3_5_8I2R6H.Encloses (homogeneousEntropy CA3_5_8I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R6Value CA3_5_8I2R6MassTerm_sound CA3_5_8I2R6Entropy_sound) (by decide +kernel)
def CA3_5_8I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA3_5_8I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA3_5_8I2R7Raw_sound (a : PairSlot) :
    (CA3_5_8I2R7Raw a).Encloses (CA3_5_8I2R7Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA3_5_8I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I2R7Certificates_valid :
    CA3_5_8I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R7Certificates (CA3_5_8I2R7CertificateIndex a)).input
lemma CA3_5_8I2R7P_check : ∀ a : PairSlot, contains (CA3_5_8I2R7Raw a) (CA3_5_8I2R7P a) = true := by
  decide +kernel
lemma CA3_5_8I2R7P_sound (a : PairSlot) :
    (CA3_5_8I2R7P a).Encloses (CA3_5_8I2R7Value a) :=
  contains_sound (CA3_5_8I2R7Raw_sound a) (CA3_5_8I2R7P_check a)
def CA3_5_8I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R7Certificates (CA3_5_8I2R7CertificateIndex a)).output
lemma CA3_5_8I2R7Terms_sound (a : PairSlot) :
    (CA3_5_8I2R7Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R7Certificates_valid
    (CA3_5_8I2R7CertificateIndex a) (CA3_5_8I2R7P_sound a)
def CA3_5_8I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R7Entropy_sound : CA3_5_8I2R7Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R7Value CA3_5_8I2R7Terms CA3_5_8I2R7Terms_sound) (by decide +kernel)
def CA3_5_8I2R7Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R7Mass_sound : CA3_5_8I2R7Mass.Encloses (∑ a, CA3_5_8I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R7P CA3_5_8I2R7Value CA3_5_8I2R7P_sound) (by decide +kernel)
def CA3_5_8I2R7MassTerm : Ball := .exact 0
lemma CA3_5_8I2R7MassTerm_sound : CA3_5_8I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R7Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I2R7Mass_sound)
def CA3_5_8I2R7H : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R7H_sound : CA3_5_8I2R7H.Encloses (homogeneousEntropy CA3_5_8I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R7Value CA3_5_8I2R7MassTerm_sound CA3_5_8I2R7Entropy_sound) (by decide +kernel)
def CA3_5_8I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA3_5_8I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA3_5_8I2R8Raw_sound (a : PairSlot) :
    (CA3_5_8I2R8Raw a).Encloses (CA3_5_8I2R8Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA3_5_8I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I2R8Certificates_valid :
    CA3_5_8I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R8Certificates (CA3_5_8I2R8CertificateIndex a)).input
lemma CA3_5_8I2R8P_check : ∀ a : PairSlot, contains (CA3_5_8I2R8Raw a) (CA3_5_8I2R8P a) = true := by
  decide +kernel
lemma CA3_5_8I2R8P_sound (a : PairSlot) :
    (CA3_5_8I2R8P a).Encloses (CA3_5_8I2R8Value a) :=
  contains_sound (CA3_5_8I2R8Raw_sound a) (CA3_5_8I2R8P_check a)
def CA3_5_8I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R8Certificates (CA3_5_8I2R8CertificateIndex a)).output
lemma CA3_5_8I2R8Terms_sound (a : PairSlot) :
    (CA3_5_8I2R8Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R8Certificates_valid
    (CA3_5_8I2R8CertificateIndex a) (CA3_5_8I2R8P_sound a)
def CA3_5_8I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R8Entropy_sound : CA3_5_8I2R8Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R8Value CA3_5_8I2R8Terms CA3_5_8I2R8Terms_sound) (by decide +kernel)
def CA3_5_8I2R8Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R8Mass_sound : CA3_5_8I2R8Mass.Encloses (∑ a, CA3_5_8I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R8P CA3_5_8I2R8Value CA3_5_8I2R8P_sound) (by decide +kernel)
def CA3_5_8I2R8MassTerm : Ball := .exact 0
lemma CA3_5_8I2R8MassTerm_sound : CA3_5_8I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R8Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I2R8Mass_sound)
def CA3_5_8I2R8H : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R8H_sound : CA3_5_8I2R8H.Encloses (homogeneousEntropy CA3_5_8I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R8Value CA3_5_8I2R8MassTerm_sound CA3_5_8I2R8Entropy_sound) (by decide +kernel)
def CA3_5_8I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA3_5_8I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA3_5_8I2R9Raw_sound (a : PairSlot) :
    (CA3_5_8I2R9Raw a).Encloses (CA3_5_8I2R9Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA3_5_8I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I2R9Certificates_valid :
    CA3_5_8I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R9Certificates (CA3_5_8I2R9CertificateIndex a)).input
lemma CA3_5_8I2R9P_check : ∀ a : PairSlot, contains (CA3_5_8I2R9Raw a) (CA3_5_8I2R9P a) = true := by
  decide +kernel
lemma CA3_5_8I2R9P_sound (a : PairSlot) :
    (CA3_5_8I2R9P a).Encloses (CA3_5_8I2R9Value a) :=
  contains_sound (CA3_5_8I2R9Raw_sound a) (CA3_5_8I2R9P_check a)
def CA3_5_8I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R9Certificates (CA3_5_8I2R9CertificateIndex a)).output
lemma CA3_5_8I2R9Terms_sound (a : PairSlot) :
    (CA3_5_8I2R9Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R9Certificates_valid
    (CA3_5_8I2R9CertificateIndex a) (CA3_5_8I2R9P_sound a)
def CA3_5_8I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R9Entropy_sound : CA3_5_8I2R9Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R9Value CA3_5_8I2R9Terms CA3_5_8I2R9Terms_sound) (by decide +kernel)
def CA3_5_8I2R9Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R9Mass_sound : CA3_5_8I2R9Mass.Encloses (∑ a, CA3_5_8I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R9P CA3_5_8I2R9Value CA3_5_8I2R9P_sound) (by decide +kernel)
def CA3_5_8I2R9MassTerm : Ball := .exact 0
lemma CA3_5_8I2R9MassTerm_sound : CA3_5_8I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R9Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I2R9Mass_sound)
def CA3_5_8I2R9H : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R9H_sound : CA3_5_8I2R9H.Encloses (homogeneousEntropy CA3_5_8I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R9Value CA3_5_8I2R9MassTerm_sound CA3_5_8I2R9Entropy_sound) (by decide +kernel)
def CA3_5_8I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA3_5_8I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA3_5_8I2R10Raw_sound (a : PairSlot) :
    (CA3_5_8I2R10Raw a).Encloses (CA3_5_8I2R10Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA3_5_8I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I2R10Certificates_valid :
    CA3_5_8I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R10Certificates (CA3_5_8I2R10CertificateIndex a)).input
lemma CA3_5_8I2R10P_check : ∀ a : PairSlot, contains (CA3_5_8I2R10Raw a) (CA3_5_8I2R10P a) = true := by
  decide +kernel
lemma CA3_5_8I2R10P_sound (a : PairSlot) :
    (CA3_5_8I2R10P a).Encloses (CA3_5_8I2R10Value a) :=
  contains_sound (CA3_5_8I2R10Raw_sound a) (CA3_5_8I2R10P_check a)
def CA3_5_8I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R10Certificates (CA3_5_8I2R10CertificateIndex a)).output
lemma CA3_5_8I2R10Terms_sound (a : PairSlot) :
    (CA3_5_8I2R10Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R10Certificates_valid
    (CA3_5_8I2R10CertificateIndex a) (CA3_5_8I2R10P_sound a)
def CA3_5_8I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R10Entropy_sound : CA3_5_8I2R10Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R10Value CA3_5_8I2R10Terms CA3_5_8I2R10Terms_sound) (by decide +kernel)
def CA3_5_8I2R10Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R10Mass_sound : CA3_5_8I2R10Mass.Encloses (∑ a, CA3_5_8I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R10P CA3_5_8I2R10Value CA3_5_8I2R10P_sound) (by decide +kernel)
def CA3_5_8I2R10MassTerm : Ball := .exact 0
lemma CA3_5_8I2R10MassTerm_sound : CA3_5_8I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R10Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I2R10Mass_sound)
def CA3_5_8I2R10H : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R10H_sound : CA3_5_8I2R10H.Encloses (homogeneousEntropy CA3_5_8I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R10Value CA3_5_8I2R10MassTerm_sound CA3_5_8I2R10Entropy_sound) (by decide +kernel)
def CA3_5_8I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA3_5_8I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA3_5_8I2R11Raw_sound (a : PairSlot) :
    (CA3_5_8I2R11Raw a).Encloses (CA3_5_8I2R11Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA3_5_8I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I2R11Certificates_valid :
    CA3_5_8I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R11Certificates (CA3_5_8I2R11CertificateIndex a)).input
lemma CA3_5_8I2R11P_check : ∀ a : PairSlot, contains (CA3_5_8I2R11Raw a) (CA3_5_8I2R11P a) = true := by
  decide +kernel
lemma CA3_5_8I2R11P_sound (a : PairSlot) :
    (CA3_5_8I2R11P a).Encloses (CA3_5_8I2R11Value a) :=
  contains_sound (CA3_5_8I2R11Raw_sound a) (CA3_5_8I2R11P_check a)
def CA3_5_8I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R11Certificates (CA3_5_8I2R11CertificateIndex a)).output
lemma CA3_5_8I2R11Terms_sound (a : PairSlot) :
    (CA3_5_8I2R11Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R11Certificates_valid
    (CA3_5_8I2R11CertificateIndex a) (CA3_5_8I2R11P_sound a)
def CA3_5_8I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R11Entropy_sound : CA3_5_8I2R11Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R11Value CA3_5_8I2R11Terms CA3_5_8I2R11Terms_sound) (by decide +kernel)
def CA3_5_8I2R11Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R11Mass_sound : CA3_5_8I2R11Mass.Encloses (∑ a, CA3_5_8I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R11P CA3_5_8I2R11Value CA3_5_8I2R11P_sound) (by decide +kernel)
def CA3_5_8I2R11MassTerm : Ball := .exact 0
lemma CA3_5_8I2R11MassTerm_sound : CA3_5_8I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R11Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I2R11Mass_sound)
def CA3_5_8I2R11H : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R11H_sound : CA3_5_8I2R11H.Encloses (homogeneousEntropy CA3_5_8I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R11Value CA3_5_8I2R11MassTerm_sound CA3_5_8I2R11Entropy_sound) (by decide +kernel)
def CA3_5_8I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA3_5_8I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA3_5_8I2R12Raw_sound (a : PairSlot) :
    (CA3_5_8I2R12Raw a).Encloses (CA3_5_8I2R12Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA3_5_8I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I2R12Certificates_valid :
    CA3_5_8I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R12Certificates (CA3_5_8I2R12CertificateIndex a)).input
lemma CA3_5_8I2R12P_check : ∀ a : PairSlot, contains (CA3_5_8I2R12Raw a) (CA3_5_8I2R12P a) = true := by
  decide +kernel
lemma CA3_5_8I2R12P_sound (a : PairSlot) :
    (CA3_5_8I2R12P a).Encloses (CA3_5_8I2R12Value a) :=
  contains_sound (CA3_5_8I2R12Raw_sound a) (CA3_5_8I2R12P_check a)
def CA3_5_8I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R12Certificates (CA3_5_8I2R12CertificateIndex a)).output
lemma CA3_5_8I2R12Terms_sound (a : PairSlot) :
    (CA3_5_8I2R12Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R12Certificates_valid
    (CA3_5_8I2R12CertificateIndex a) (CA3_5_8I2R12P_sound a)
def CA3_5_8I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R12Entropy_sound : CA3_5_8I2R12Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R12Value CA3_5_8I2R12Terms CA3_5_8I2R12Terms_sound) (by decide +kernel)
def CA3_5_8I2R12Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R12Mass_sound : CA3_5_8I2R12Mass.Encloses (∑ a, CA3_5_8I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R12P CA3_5_8I2R12Value CA3_5_8I2R12P_sound) (by decide +kernel)
def CA3_5_8I2R12MassTerm : Ball := .exact 0
lemma CA3_5_8I2R12MassTerm_sound : CA3_5_8I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R12Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I2R12Mass_sound)
def CA3_5_8I2R12H : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R12H_sound : CA3_5_8I2R12H.Encloses (homogeneousEntropy CA3_5_8I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R12Value CA3_5_8I2R12MassTerm_sound CA3_5_8I2R12Entropy_sound) (by decide +kernel)
def CA3_5_8I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA3_5_8I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA3_5_8I2R13Raw_sound (a : PairSlot) :
    (CA3_5_8I2R13Raw a).Encloses (CA3_5_8I2R13Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA3_5_8I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I2R13Certificates_valid :
    CA3_5_8I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R13Certificates (CA3_5_8I2R13CertificateIndex a)).input
lemma CA3_5_8I2R13P_check : ∀ a : PairSlot, contains (CA3_5_8I2R13Raw a) (CA3_5_8I2R13P a) = true := by
  decide +kernel
lemma CA3_5_8I2R13P_sound (a : PairSlot) :
    (CA3_5_8I2R13P a).Encloses (CA3_5_8I2R13Value a) :=
  contains_sound (CA3_5_8I2R13Raw_sound a) (CA3_5_8I2R13P_check a)
def CA3_5_8I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R13Certificates (CA3_5_8I2R13CertificateIndex a)).output
lemma CA3_5_8I2R13Terms_sound (a : PairSlot) :
    (CA3_5_8I2R13Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R13Certificates_valid
    (CA3_5_8I2R13CertificateIndex a) (CA3_5_8I2R13P_sound a)
def CA3_5_8I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R13Entropy_sound : CA3_5_8I2R13Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R13Value CA3_5_8I2R13Terms CA3_5_8I2R13Terms_sound) (by decide +kernel)
def CA3_5_8I2R13Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R13Mass_sound : CA3_5_8I2R13Mass.Encloses (∑ a, CA3_5_8I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R13P CA3_5_8I2R13Value CA3_5_8I2R13P_sound) (by decide +kernel)
def CA3_5_8I2R13MassTerm : Ball := .exact 0
lemma CA3_5_8I2R13MassTerm_sound : CA3_5_8I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R13Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I2R13Mass_sound)
def CA3_5_8I2R13H : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R13H_sound : CA3_5_8I2R13H.Encloses (homogeneousEntropy CA3_5_8I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R13Value CA3_5_8I2R13MassTerm_sound CA3_5_8I2R13Entropy_sound) (by decide +kernel)
def CA3_5_8I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA3_5_8I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA3_5_8I2R14Raw_sound (a : PairSlot) :
    (CA3_5_8I2R14Raw a).Encloses (CA3_5_8I2R14Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA3_5_8I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I2R14Certificates_valid :
    CA3_5_8I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R14Certificates (CA3_5_8I2R14CertificateIndex a)).input
lemma CA3_5_8I2R14P_check : ∀ a : PairSlot, contains (CA3_5_8I2R14Raw a) (CA3_5_8I2R14P a) = true := by
  decide +kernel
lemma CA3_5_8I2R14P_sound (a : PairSlot) :
    (CA3_5_8I2R14P a).Encloses (CA3_5_8I2R14Value a) :=
  contains_sound (CA3_5_8I2R14Raw_sound a) (CA3_5_8I2R14P_check a)
def CA3_5_8I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R14Certificates (CA3_5_8I2R14CertificateIndex a)).output
lemma CA3_5_8I2R14Terms_sound (a : PairSlot) :
    (CA3_5_8I2R14Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R14Certificates_valid
    (CA3_5_8I2R14CertificateIndex a) (CA3_5_8I2R14P_sound a)
def CA3_5_8I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R14Entropy_sound : CA3_5_8I2R14Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R14Value CA3_5_8I2R14Terms CA3_5_8I2R14Terms_sound) (by decide +kernel)
def CA3_5_8I2R14Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R14Mass_sound : CA3_5_8I2R14Mass.Encloses (∑ a, CA3_5_8I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R14P CA3_5_8I2R14Value CA3_5_8I2R14P_sound) (by decide +kernel)
def CA3_5_8I2R14MassTerm : Ball := .exact 0
lemma CA3_5_8I2R14MassTerm_sound : CA3_5_8I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R14Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I2R14Mass_sound)
def CA3_5_8I2R14H : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R14H_sound : CA3_5_8I2R14H.Encloses (homogeneousEntropy CA3_5_8I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R14Value CA3_5_8I2R14MassTerm_sound CA3_5_8I2R14Entropy_sound) (by decide +kernel)
def CA3_5_8I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA3_5_8I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA3_5_8I2R15Raw_sound (a : PairSlot) :
    (CA3_5_8I2R15Raw a).Encloses (CA3_5_8I2R15Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA3_5_8I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I2R15Certificates_valid :
    CA3_5_8I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R15Certificates (CA3_5_8I2R15CertificateIndex a)).input
lemma CA3_5_8I2R15P_check : ∀ a : PairSlot, contains (CA3_5_8I2R15Raw a) (CA3_5_8I2R15P a) = true := by
  decide +kernel
lemma CA3_5_8I2R15P_sound (a : PairSlot) :
    (CA3_5_8I2R15P a).Encloses (CA3_5_8I2R15Value a) :=
  contains_sound (CA3_5_8I2R15Raw_sound a) (CA3_5_8I2R15P_check a)
def CA3_5_8I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R15Certificates (CA3_5_8I2R15CertificateIndex a)).output
lemma CA3_5_8I2R15Terms_sound (a : PairSlot) :
    (CA3_5_8I2R15Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R15Certificates_valid
    (CA3_5_8I2R15CertificateIndex a) (CA3_5_8I2R15P_sound a)
def CA3_5_8I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R15Entropy_sound : CA3_5_8I2R15Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R15Value CA3_5_8I2R15Terms CA3_5_8I2R15Terms_sound) (by decide +kernel)
def CA3_5_8I2R15Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R15Mass_sound : CA3_5_8I2R15Mass.Encloses (∑ a, CA3_5_8I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R15P CA3_5_8I2R15Value CA3_5_8I2R15P_sound) (by decide +kernel)
def CA3_5_8I2R15MassTerm : Ball := .exact 0
lemma CA3_5_8I2R15MassTerm_sound : CA3_5_8I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R15Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I2R15Mass_sound)
def CA3_5_8I2R15H : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R15H_sound : CA3_5_8I2R15H.Encloses (homogeneousEntropy CA3_5_8I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R15Value CA3_5_8I2R15MassTerm_sound CA3_5_8I2R15Entropy_sound) (by decide +kernel)
def CA3_5_8I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA3_5_8I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA3_5_8I2R16Raw_sound (a : PairSlot) :
    (CA3_5_8I2R16Raw a).Encloses (CA3_5_8I2R16Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA3_5_8I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I2R16Certificates_valid :
    CA3_5_8I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R16Certificates (CA3_5_8I2R16CertificateIndex a)).input
lemma CA3_5_8I2R16P_check : ∀ a : PairSlot, contains (CA3_5_8I2R16Raw a) (CA3_5_8I2R16P a) = true := by
  decide +kernel
lemma CA3_5_8I2R16P_sound (a : PairSlot) :
    (CA3_5_8I2R16P a).Encloses (CA3_5_8I2R16Value a) :=
  contains_sound (CA3_5_8I2R16Raw_sound a) (CA3_5_8I2R16P_check a)
def CA3_5_8I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I2R16Certificates (CA3_5_8I2R16CertificateIndex a)).output
lemma CA3_5_8I2R16Terms_sound (a : PairSlot) :
    (CA3_5_8I2R16Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I2R16Certificates_valid
    (CA3_5_8I2R16CertificateIndex a) (CA3_5_8I2R16P_sound a)
def CA3_5_8I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R16Entropy_sound : CA3_5_8I2R16Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I2R16Value CA3_5_8I2R16Terms CA3_5_8I2R16Terms_sound) (by decide +kernel)
def CA3_5_8I2R16Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R16Mass_sound : CA3_5_8I2R16Mass.Encloses (∑ a, CA3_5_8I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I2R16P CA3_5_8I2R16Value CA3_5_8I2R16P_sound) (by decide +kernel)
def CA3_5_8I2R16MassTerm : Ball := .exact 0
lemma CA3_5_8I2R16MassTerm_sound : CA3_5_8I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R16Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I2R16Mass_sound)
def CA3_5_8I2R16H : Ball := ⟨0, 0⟩
lemma CA3_5_8I2R16H_sound : CA3_5_8I2R16H.Encloses (homogeneousEntropy CA3_5_8I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I2R16Value CA3_5_8I2R16MassTerm_sound CA3_5_8I2R16Entropy_sound) (by decide +kernel)
def CA3_5_8I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_5_8I2R0H
  | 1 => CA3_5_8I2R1H
  | 2 => CA3_5_8I2R2H
  | 3 => CA3_5_8I2R3H
  | 4 => CA3_5_8I2R4H
  | 5 => CA3_5_8I2R5H
  | 6 => CA3_5_8I2R6H
  | 7 => CA3_5_8I2R7H
  | 8 => CA3_5_8I2R8H
  | 9 => CA3_5_8I2R9H
  | 10 => CA3_5_8I2R10H
  | 11 => CA3_5_8I2R11H
  | 12 => CA3_5_8I2R12H
  | 13 => CA3_5_8I2R13H
  | 14 => CA3_5_8I2R14H
  | 15 => CA3_5_8I2R15H
  | 16 => CA3_5_8I2R16H
  | _ => (.exact 0)
lemma CA3_5_8I2ResidualEntropies_sound (k : Fin 17) :
    (CA3_5_8I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA3_5_8I2R0H_sound
  · exact CA3_5_8I2R1H_sound
  · exact CA3_5_8I2R2H_sound
  · exact CA3_5_8I2R3H_sound
  · exact CA3_5_8I2R4H_sound
  · exact CA3_5_8I2R5H_sound
  · exact CA3_5_8I2R6H_sound
  · exact CA3_5_8I2R7H_sound
  · exact CA3_5_8I2R8H_sound
  · exact CA3_5_8I2R9H_sound
  · exact CA3_5_8I2R10H_sound
  · exact CA3_5_8I2R11H_sound
  · exact CA3_5_8I2R12H_sound
  · exact CA3_5_8I2R13H_sound
  · exact CA3_5_8I2R14H_sound
  · exact CA3_5_8I2R15H_sound
  · exact CA3_5_8I2R16H_sound
def CA3_5_8I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | 3, 0, 5 => Z3_0_5H2H
  | _, _, _ => (.exact 0)
lemma CA3_5_8I2Singles_sound (u : Shape) (hu : u ∈ below (shape 3 5 8))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA3_5_8I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A3_5_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact Z3_0_5H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 4 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 5 0) by decide +kernel) hd |>.elim
def CA3_5_8I2Singleton : Ball := ⟨(6211276669360813360008105642437 / 50000000000000000000000000000000), (10316298947 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2Singleton_sound : CA3_5_8I2Singleton.Encloses
    (singletonEntropy (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA3_5_8I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_5_8Law_sound u) CA3_5_8I2Singles_sound) (by decide +kernel)
def CA3_5_8I2Group : Ball := ⟨(45353578268562637195015629947023 / 50000000000000000000000000000000), (148030447083 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I2Group_sound : CA3_5_8I2Group.Encloses
    (groupedEntropy (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA3_5_8I2Singleton_sound
    (finSumBall_sound 17 CA3_5_8I2ResidualEntropies _ CA3_5_8I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA3_5_8I2H : Ball := ⟨(50128905296283211989447316523337 / 50000000000000000000000000000000), (216418519571 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I2_sound : CA3_5_8I2H.Encloses (stageACapacity (shape 3 5 8) 2) := by
  have hb := contains_sound (Ball.add_sound CA3_5_8I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA3_5_8I2Group_sound)))
    (show contains (.add CA3_5_8I2PairH (.neg (.mul (.exact 2) CA3_5_8I2Group))) CA3_5_8I2H = true by decide +kernel)
  unfold CA3_5_8I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
