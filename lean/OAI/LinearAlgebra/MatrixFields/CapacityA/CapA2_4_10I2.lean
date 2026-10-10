import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA2_4_10I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_4_10I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA2_4_10I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA2_4_10I2R0Raw_sound (a : PairSlot) :
    (CA2_4_10I2R0Raw a).Encloses (CA2_4_10I2R0Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA2_4_10I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R0Certificates_valid :
    CA2_4_10I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R0Certificates (CA2_4_10I2R0CertificateIndex a)).input
lemma CA2_4_10I2R0P_check : ∀ a : PairSlot, contains (CA2_4_10I2R0Raw a) (CA2_4_10I2R0P a) = true := by
  decide +kernel
lemma CA2_4_10I2R0P_sound (a : PairSlot) :
    (CA2_4_10I2R0P a).Encloses (CA2_4_10I2R0Value a) :=
  contains_sound (CA2_4_10I2R0Raw_sound a) (CA2_4_10I2R0P_check a)
def CA2_4_10I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R0Certificates (CA2_4_10I2R0CertificateIndex a)).output
lemma CA2_4_10I2R0Terms_sound (a : PairSlot) :
    (CA2_4_10I2R0Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R0Certificates_valid
    (CA2_4_10I2R0CertificateIndex a) (CA2_4_10I2R0P_sound a)
def CA2_4_10I2R0Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R0Entropy_sound : CA2_4_10I2R0Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R0Value CA2_4_10I2R0Terms CA2_4_10I2R0Terms_sound) (by decide +kernel)
def CA2_4_10I2R0Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R0Mass_sound : CA2_4_10I2R0Mass.Encloses (∑ a, CA2_4_10I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R0P CA2_4_10I2R0Value CA2_4_10I2R0P_sound) (by decide +kernel)
def CA2_4_10I2R0MassTerm : Ball := .exact 0
lemma CA2_4_10I2R0MassTerm_sound : CA2_4_10I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R0Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R0Mass_sound)
def CA2_4_10I2R0H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R0H_sound : CA2_4_10I2R0H.Encloses (homogeneousEntropy CA2_4_10I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R0Value CA2_4_10I2R0MassTerm_sound CA2_4_10I2R0Entropy_sound) (by decide +kernel)
def CA2_4_10I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA2_4_10I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA2_4_10I2R1Raw_sound (a : PairSlot) :
    (CA2_4_10I2R1Raw a).Encloses (CA2_4_10I2R1Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA2_4_10I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R1Certificates_valid :
    CA2_4_10I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R1Certificates (CA2_4_10I2R1CertificateIndex a)).input
lemma CA2_4_10I2R1P_check : ∀ a : PairSlot, contains (CA2_4_10I2R1Raw a) (CA2_4_10I2R1P a) = true := by
  decide +kernel
lemma CA2_4_10I2R1P_sound (a : PairSlot) :
    (CA2_4_10I2R1P a).Encloses (CA2_4_10I2R1Value a) :=
  contains_sound (CA2_4_10I2R1Raw_sound a) (CA2_4_10I2R1P_check a)
def CA2_4_10I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R1Certificates (CA2_4_10I2R1CertificateIndex a)).output
lemma CA2_4_10I2R1Terms_sound (a : PairSlot) :
    (CA2_4_10I2R1Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R1Certificates_valid
    (CA2_4_10I2R1CertificateIndex a) (CA2_4_10I2R1P_sound a)
def CA2_4_10I2R1Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R1Entropy_sound : CA2_4_10I2R1Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R1Value CA2_4_10I2R1Terms CA2_4_10I2R1Terms_sound) (by decide +kernel)
def CA2_4_10I2R1Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R1Mass_sound : CA2_4_10I2R1Mass.Encloses (∑ a, CA2_4_10I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R1P CA2_4_10I2R1Value CA2_4_10I2R1P_sound) (by decide +kernel)
def CA2_4_10I2R1MassTerm : Ball := .exact 0
lemma CA2_4_10I2R1MassTerm_sound : CA2_4_10I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R1Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R1Mass_sound)
def CA2_4_10I2R1H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R1H_sound : CA2_4_10I2R1H.Encloses (homogeneousEntropy CA2_4_10I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R1Value CA2_4_10I2R1MassTerm_sound CA2_4_10I2R1Entropy_sound) (by decide +kernel)
def CA2_4_10I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA2_4_10I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA2_4_10I2R2Raw_sound (a : PairSlot) :
    (CA2_4_10I2R2Raw a).Encloses (CA2_4_10I2R2Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA2_4_10I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(108119627934249078776977417 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(5341606149681540320740204679 / 100000000000000000000000000000000), (1740051 / 100000000000000000000000000000000)⟩ ⟨(-1235114810265980979972407199390463 / 100000000000000000000000000000000), (402340881201 / 100000000000000000000000000000000)⟩ ⟨-18, 108119627934249078776977417, 95367431640625000000000000⟩,
   .log ⟨(43499240461398851725860779 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(318587072713131070978388603 / 50000000000000000000000000000000), (211877 / 100000000000000000000000000000000)⟩ ⟨(-1464793726666766377904242428224319 / 100000000000000000000000000000000), (487046243599 / 100000000000000000000000000000000)⟩ ⟨-22, 43499240461398851725860779, 23841857910156250000000000⟩,
   .log ⟨(1272072156411299444786029 / 78125000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(224402040018928237480642147 / 1250000000000000000000000000000), (2930771 / 50000000000000000000000000000000)⟩ ⟨(-1102541819699122984308435758302303 / 100000000000000000000000000000000), (179994532013 / 50000000000000000000000000000000)⟩ ⟨-16, 1272072156411299444786029, 1192092895507812500000000⟩]
lemma CA2_4_10I2R2Certificates_valid :
    CA2_4_10I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA2_4_10I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R2Certificates (CA2_4_10I2R2CertificateIndex a)).input
lemma CA2_4_10I2R2P_check : ∀ a : PairSlot, contains (CA2_4_10I2R2Raw a) (CA2_4_10I2R2P a) = true := by
  decide +kernel
lemma CA2_4_10I2R2P_sound (a : PairSlot) :
    (CA2_4_10I2R2P a).Encloses (CA2_4_10I2R2Value a) :=
  contains_sound (CA2_4_10I2R2Raw_sound a) (CA2_4_10I2R2P_check a)
def CA2_4_10I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R2Certificates (CA2_4_10I2R2CertificateIndex a)).output
lemma CA2_4_10I2R2Terms_sound (a : PairSlot) :
    (CA2_4_10I2R2Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R2Certificates_valid
    (CA2_4_10I2R2CertificateIndex a) (CA2_4_10I2R2P_sound a)
def CA2_4_10I2R2Entropy : Ball := ⟨(2990972379172986392384533553 / 10000000000000000000000000000000), (4882699 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I2R2Entropy_sound : CA2_4_10I2R2Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R2Value CA2_4_10I2R2Terms CA2_4_10I2R2Terms_sound) (by decide +kernel)
def CA2_4_10I2R2Mass : Ball := ⟨(1290103932301626811496829007 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma CA2_4_10I2R2Mass_sound : CA2_4_10I2R2Mass.Encloses (∑ a, CA2_4_10I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R2P CA2_4_10I2R2Value CA2_4_10I2R2P_sound) (by decide +kernel)
def CA2_4_10I2R2MassTermLogWitness : LogWitness := ⟨-16, 1290103932301626811496829007, 762939453125000000000000000⟩
def CA2_4_10I2R2MassTermLog : Ball := ⟨(-1056505550160642353212106317084283 / 100000000000000000000000000000000), (179994598197 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I2R2MassTermLog_sound : CA2_4_10I2R2MassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I2R2Mass_sound) (w := CA2_4_10I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I2R2MassTerm : Ball := ⟨(1090401571808590665558663107 / 4000000000000000000000000000000), (9288523 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I2R2MassTerm_sound : CA2_4_10I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I2R2Mass_sound) CA2_4_10I2R2MassTermLog_sound) (by decide +kernel)
def CA2_4_10I2R2H : Ball := ⟨(529936899303019456975751571 / 20000000000000000000000000000000), (19053921 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I2R2H_sound : CA2_4_10I2R2H.Encloses (homogeneousEntropy CA2_4_10I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R2Value CA2_4_10I2R2MassTerm_sound CA2_4_10I2R2Entropy_sound) (by decide +kernel)
def CA2_4_10I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA2_4_10I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA2_4_10I2R3Raw_sound (a : PairSlot) :
    (CA2_4_10I2R3Raw a).Encloses (CA2_4_10I2R3Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA2_4_10I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5101330045191344185451166313 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(23441318054895785431659789537 / 25000000000000000000000000000000), (32407471 / 100000000000000000000000000000000)⟩ ⟨(-91902769855058583647193445625611 / 10000000000000000000000000000000), (158818682523 / 50000000000000000000000000000000)⟩ ⟨-14, 5101330045191344185451166313, 3051757812500000000000000000⟩,
   .log ⟨(7153688662319837610093422047 / 2000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2014934538545397049488255840941 / 100000000000000000000000000000000), (189356569 / 25000000000000000000000000000000)⟩ ⟨(-14083185847593086092627204564871 / 2500000000000000000000000000000), (52939559487 / 25000000000000000000000000000000)⟩ ⟨-9, 7153688662319837610093422047, 3906250000000000000000000000⟩,
   .log ⟨(4340734698819895454048905001 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(91540060453156114599892195539 / 50000000000000000000000000000000), (64343053 / 100000000000000000000000000000000)⟩ ⟨(-33741775733234423723495425326571 / 4000000000000000000000000000000), (296461536169 / 100000000000000000000000000000000)⟩ ⟨-13, 4340734698819895454048905001, 2441406250000000000000000000⟩]
lemma CA2_4_10I2R3Certificates_valid :
    CA2_4_10I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA2_4_10I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R3Certificates (CA2_4_10I2R3CertificateIndex a)).input
lemma CA2_4_10I2R3P_check : ∀ a : PairSlot, contains (CA2_4_10I2R3Raw a) (CA2_4_10I2R3P a) = true := by
  decide +kernel
lemma CA2_4_10I2R3P_sound (a : PairSlot) :
    (CA2_4_10I2R3P a).Encloses (CA2_4_10I2R3Value a) :=
  contains_sound (CA2_4_10I2R3Raw_sound a) (CA2_4_10I2R3P_check a)
def CA2_4_10I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R3Certificates (CA2_4_10I2R3CertificateIndex a)).output
lemma CA2_4_10I2R3Terms_sound (a : PairSlot) :
    (CA2_4_10I2R3Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R3Certificates_valid
    (CA2_4_10I2R3CertificateIndex a) (CA2_4_10I2R3P_sound a)
def CA2_4_10I2R3Entropy : Ball := ⟨(2291779931671292420414679390167 / 50000000000000000000000000000000), (1067721 / 62500000000000000000000000000)⟩
lemma CA2_4_10I2R3Entropy_sound : CA2_4_10I2R3Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R3Value CA2_4_10I2R3Terms CA2_4_10I2R3Terms_sound) (by decide +kernel)
def CA2_4_10I2R3Mass : Ball := ⟨(389590766700474046145817959981 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
lemma CA2_4_10I2R3Mass_sound : CA2_4_10I2R3Mass.Encloses (∑ a, CA2_4_10I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R3P CA2_4_10I2R3Value CA2_4_10I2R3P_sound) (by decide +kernel)
def CA2_4_10I2R3MassTermLogWitness : LogWitness := ⟨-8, 389590766700474046145817959981, 195312500000000000000000000000⟩
def CA2_4_10I2R3MassTermLog : Ball := ⟨(-6068351765446050781817188320967 / 1250000000000000000000000000000), (190582414687 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I2R3MassTermLog_sound : CA2_4_10I2R3MassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I2R3Mass_sound) (w := CA2_4_10I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I2R3MassTerm : Ball := ⟨(3782678107053283472545872209083 / 100000000000000000000000000000000), (1160143 / 78125000000000000000000000000)⟩
lemma CA2_4_10I2R3MassTerm_sound : CA2_4_10I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I2R3Mass_sound) CA2_4_10I2R3MassTermLog_sound) (by decide +kernel)
def CA2_4_10I2R3H : Ball := ⟨(800881756289301368283486571251 / 100000000000000000000000000000000), (9979177 / 312500000000000000000000000000)⟩
lemma CA2_4_10I2R3H_sound : CA2_4_10I2R3H.Encloses (homogeneousEntropy CA2_4_10I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R3Value CA2_4_10I2R3MassTerm_sound CA2_4_10I2R3Entropy_sound) (by decide +kernel)
def CA2_4_10I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA2_4_10I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA2_4_10I2R4Raw_sound (a : PairSlot) :
    (CA2_4_10I2R4Raw a).Encloses (CA2_4_10I2R4Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA2_4_10I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(972062729000252664061250893 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(19742528012137973035621483893 / 50000000000000000000000000000000), (6586959 / 50000000000000000000000000000000)⟩ ⟨(-1015496604444590398738360364393069 / 100000000000000000000000000000000), (169406602323 / 50000000000000000000000000000000)⟩ ⟨-15, 972062729000252664061250893, 762939453125000000000000000⟩,
   .log ⟨(282887429788319230324036160949 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(3011646811541868877798144773663 / 50000000000000000000000000000000), (2396149793 / 100000000000000000000000000000000)⟩ ⟨(-106460962715644266364444384953511 / 25000000000000000000000000000000), (169406590241 / 100000000000000000000000000000000)⟩ ⟨-7, 282887429788319230324036160949, 156250000000000000000000000000⟩,
   .log ⟨(2973873107602243992170166476157 / 20000000000000000000000000000000), (17 / 20000000000000000000000000000000)⟩ ⟨(28339034482721266653792374925983 / 100000000000000000000000000000000), (3148710691 / 25000000000000000000000000000000)⟩ ⟨(-190586709367504170503864919298769 / 100000000000000000000000000000000), (84703295303 / 100000000000000000000000000000000)⟩ ⟨-3, 2973873107602243992170166476157, 2500000000000000000000000000000⟩,
   .log ⟨(688444784950710917538417309189 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(3427415715746421544076009068661 / 100000000000000000000000000000000), (262410943 / 20000000000000000000000000000000)⟩ ⟨(-2489245173083711256003230900169 / 500000000000000000000000000000), (190582413873 / 100000000000000000000000000000000)⟩ ⟨-8, 688444784950710917538417309189, 390625000000000000000000000000⟩,
   .log ⟨(3244754126435935260381470661 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(130330429511940918756764107249 / 50000000000000000000000000000000), (44661727 / 50000000000000000000000000000000)⟩ ⟨(-401665039733216825528248804145889 / 50000000000000000000000000000000), (3441071387 / 1250000000000000000000000000000)⟩ ⟨-12, 3244754126435935260381470661, 2441406250000000000000000000⟩]
lemma CA2_4_10I2R4Certificates_valid :
    CA2_4_10I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA2_4_10I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R4Certificates (CA2_4_10I2R4CertificateIndex a)).input
lemma CA2_4_10I2R4P_check : ∀ a : PairSlot, contains (CA2_4_10I2R4Raw a) (CA2_4_10I2R4P a) = true := by
  decide +kernel
lemma CA2_4_10I2R4P_sound (a : PairSlot) :
    (CA2_4_10I2R4P a).Encloses (CA2_4_10I2R4Value a) :=
  contains_sound (CA2_4_10I2R4Raw_sound a) (CA2_4_10I2R4P_check a)
def CA2_4_10I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R4Certificates (CA2_4_10I2R4CertificateIndex a)).output
lemma CA2_4_10I2R4Terms_sound (a : PairSlot) :
    (CA2_4_10I2R4Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R4Certificates_valid
    (CA2_4_10I2R4CertificateIndex a) (CA2_4_10I2R4P_sound a)
def CA2_4_10I2R4Entropy : Ball := ⟨(47580084131454018982792986308027 / 100000000000000000000000000000000), (2012692307 / 10000000000000000000000000000000)⟩
lemma CA2_4_10I2R4Entropy_sound : CA2_4_10I2R4Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R4Value CA2_4_10I2R4Terms CA2_4_10I2R4Terms_sound) (by decide +kernel)
def CA2_4_10I2R4Mass : Ball := ⟨(19115353448892195473084333322407 / 100000000000000000000000000000000), (3 / 2500000000000000000000000000000)⟩
lemma CA2_4_10I2R4Mass_sound : CA2_4_10I2R4Mass.Encloses (∑ a, CA2_4_10I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R4P CA2_4_10I2R4Value CA2_4_10I2R4P_sound) (by decide +kernel)
def CA2_4_10I2R4MassTermLogWitness : LogWitness := ⟨-3, 19115353448892195473084333322407, 12500000000000000000000000000000⟩
def CA2_4_10I2R4MassTermLog : Ball := ⟨(-165467832835452117553219578152353 / 100000000000000000000000000000000), (84703295359 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I2R4MassTermLog_sound : CA2_4_10I2R4MassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I2R4Mass_sound) (w := CA2_4_10I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I2R4MassTerm : Ball := ⟨(15814880545359384516533513860097 / 50000000000000000000000000000000), (1619133449 / 10000000000000000000000000000000)⟩
lemma CA2_4_10I2R4MassTerm_sound : CA2_4_10I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I2R4Mass_sound) CA2_4_10I2R4MassTermLog_sound) (by decide +kernel)
def CA2_4_10I2R4H : Ball := ⟨(15950323040735249949725958587833 / 100000000000000000000000000000000), (907956439 / 2500000000000000000000000000000)⟩
lemma CA2_4_10I2R4H_sound : CA2_4_10I2R4H.Encloses (homogeneousEntropy CA2_4_10I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R4Value CA2_4_10I2R4MassTerm_sound CA2_4_10I2R4Entropy_sound) (by decide +kernel)
def CA2_4_10I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA2_4_10I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA2_4_10I2R5Raw_sound (a : PairSlot) :
    (CA2_4_10I2R5Raw a).Encloses (CA2_4_10I2R5Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA2_4_10I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(16566491413379707340906706941 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(6636864657885305316815959311 / 2500000000000000000000000000000), (11401297 / 12500000000000000000000000000000)⟩ ⟨(-801239621870099723292720346396909 / 100000000000000000000000000000000), (17205356931 / 6250000000000000000000000000000)⟩ ⟨-12, 16566491413379707340906706941, 12207031250000000000000000000⟩,
   .log ⟨(2035480733178375986788837663423 / 10000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩ ⟨(1012558204054107071425207125407 / 3125000000000000000000000000000), (4310298161 / 25000000000000000000000000000000)⟩ ⟨(-159185306947790906280698291000047 / 100000000000000000000000000000000), (16940659021 / 20000000000000000000000000000000)⟩ ⟨-3, 2035480733178375986788837663423, 1250000000000000000000000000000⟩,
   .log ⟨(759233811713028272251009164257 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(185276422413761041348577490497 / 5000000000000000000000000000000), (11304423 / 781250000000000000000000000000)⟩ ⟨(-61007696033626785148893640778559 / 12500000000000000000000000000000), (95291206837 / 50000000000000000000000000000000)⟩ ⟨-8, 759233811713028272251009164257, 390625000000000000000000000000⟩]
lemma CA2_4_10I2R5Certificates_valid :
    CA2_4_10I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA2_4_10I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R5Certificates (CA2_4_10I2R5CertificateIndex a)).input
lemma CA2_4_10I2R5P_check : ∀ a : PairSlot, contains (CA2_4_10I2R5Raw a) (CA2_4_10I2R5P a) = true := by
  decide +kernel
lemma CA2_4_10I2R5P_sound (a : PairSlot) :
    (CA2_4_10I2R5P a).Encloses (CA2_4_10I2R5Value a) :=
  contains_sound (CA2_4_10I2R5Raw_sound a) (CA2_4_10I2R5P_check a)
def CA2_4_10I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R5Certificates (CA2_4_10I2R5CertificateIndex a)).output
lemma CA2_4_10I2R5Terms_sound (a : PairSlot) :
    (CA2_4_10I2R5Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R5Certificates_valid
    (CA2_4_10I2R5CertificateIndex a) (CA2_4_10I2R5P_sound a)
def CA2_4_10I2R5Entropy : Ball := ⟨(9093216391080514831312704048851 / 12500000000000000000000000000000), (4694842291 / 12500000000000000000000000000000)⟩
lemma CA2_4_10I2R5Entropy_sound : CA2_4_10I2R5Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R5Value CA2_4_10I2R5Terms CA2_4_10I2R5Terms_sound) (by decide +kernel)
def CA2_4_10I2R5Mass : Ball := ⟨(21147174126323547554821199212369 / 50000000000000000000000000000000), (81 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I2R5Mass_sound : CA2_4_10I2R5Mass.Encloses (∑ a, CA2_4_10I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R5P CA2_4_10I2R5Value CA2_4_10I2R5P_sound) (by decide +kernel)
def CA2_4_10I2R5MassTermLogWitness : LogWitness := ⟨-2, 21147174126323547554821199212369, 12500000000000000000000000000000⟩
def CA2_4_10I2R5MassTermLog : Ball := ⟨(-17210334398222848168988098648769 / 20000000000000000000000000000000), (63527471431 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I2R5MassTermLog_sound : CA2_4_10I2R5MassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I2R5Mass_sound) (w := CA2_4_10I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I2R5MassTerm : Ball := ⟨(909874845728685891983629432179 / 2500000000000000000000000000000), (26868530143 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I2R5MassTerm_sound : CA2_4_10I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I2R5Mass_sound) CA2_4_10I2R5MassTermLog_sound) (by decide +kernel)
def CA2_4_10I2R5H : Ball := ⟨(1135960540609271342848639221989 / 3125000000000000000000000000000), (64427268471 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I2R5H_sound : CA2_4_10I2R5H.Encloses (homogeneousEntropy CA2_4_10I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R5Value CA2_4_10I2R5MassTerm_sound CA2_4_10I2R5Entropy_sound) (by decide +kernel)
def CA2_4_10I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA2_4_10I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA2_4_10I2R6Raw_sound (a : PairSlot) :
    (CA2_4_10I2R6Raw a).Encloses (CA2_4_10I2R6Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA2_4_10I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(43134264585488101866709234377 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(608664208686171475410771811939 / 100000000000000000000000000000000), (54804219 / 25000000000000000000000000000000)⟩ ⟨(-88193257514547339481279000366791 / 12500000000000000000000000000000), (127054943257 / 50000000000000000000000000000000)⟩ ⟨-11, 43134264585488101866709234377, 24414062500000000000000000000⟩,
   .log ⟨(5435259759136326423770061 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(45459896894057929252170797 / 50000000000000000000000000000000), (29943 / 100000000000000000000000000000000)⟩ ⟨(-26137145985549914409024975199461 / 1562500000000000000000000000000), (275294907071 / 50000000000000000000000000000000)⟩ ⟨-25, 5435259759136326423770061, 2980232238769531250000000⟩,
   .log ⟨(1809194746657434931160869249031 / 20000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩ ⟨(21736121771847904225995996957063 / 100000000000000000000000000000000), (1915559477 / 20000000000000000000000000000000)⟩ ⟨(-6007126046548146240366626242057 / 2500000000000000000000000000000), (105879118879 / 100000000000000000000000000000000)⟩ ⟨-4, 1809194746657434931160869249031, 1250000000000000000000000000000⟩]
lemma CA2_4_10I2R6Certificates_valid :
    CA2_4_10I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA2_4_10I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R6Certificates (CA2_4_10I2R6CertificateIndex a)).input
lemma CA2_4_10I2R6P_check : ∀ a : PairSlot, contains (CA2_4_10I2R6Raw a) (CA2_4_10I2R6P a) = true := by
  decide +kernel
lemma CA2_4_10I2R6P_sound (a : PairSlot) :
    (CA2_4_10I2R6P a).Encloses (CA2_4_10I2R6Value a) :=
  contains_sound (CA2_4_10I2R6Raw_sound a) (CA2_4_10I2R6P_check a)
def CA2_4_10I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R6Certificates (CA2_4_10I2R6CertificateIndex a)).output
lemma CA2_4_10I2R6Terms_sound (a : PairSlot) :
    (CA2_4_10I2R6Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R6Certificates_valid
    (CA2_4_10I2R6CertificateIndex a) (CA2_4_10I2R6P_sound a)
def CA2_4_10I2R6Entropy : Ball := ⟨(22953632028807823408534549264129 / 100000000000000000000000000000000), (10016291023 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I2R6Entropy_sound : CA2_4_10I2R6Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R6Value CA2_4_10I2R6Terms CA2_4_10I2R6Terms_sound) (by decide +kernel)
def CA2_4_10I2R6Mass : Ball := ⟨(1843704332429729067184806144557 / 20000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
lemma CA2_4_10I2R6Mass_sound : CA2_4_10I2R6Mass.Encloses (∑ a, CA2_4_10I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R6P CA2_4_10I2R6Value CA2_4_10I2R6P_sound) (by decide +kernel)
def CA2_4_10I2R6MassTermLogWitness : LogWitness := ⟨-4, 1843704332429729067184806144557, 1250000000000000000000000000000⟩
def CA2_4_10I2R6MassTermLog : Ball := ⟨(-238395550160642353212106546222153 / 100000000000000000000000000000000), (21175823787 / 20000000000000000000000000000000)⟩
lemma CA2_4_10I2R6MassTermLog_sound : CA2_4_10I2R6MassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I2R6Mass_sound) (w := CA2_4_10I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I2R6MassTerm : Ball := ⟨(2197654543315725499556882275933 / 10000000000000000000000000000000), (976048963 / 10000000000000000000000000000000)⟩
lemma CA2_4_10I2R6MassTerm_sound : CA2_4_10I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I2R6Mass_sound) CA2_4_10I2R6MassTermLog_sound) (by decide +kernel)
def CA2_4_10I2R6H : Ball := ⟨(977086595650568412965726504799 / 100000000000000000000000000000000), (19776780653 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I2R6H_sound : CA2_4_10I2R6H.Encloses (homogeneousEntropy CA2_4_10I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R6Value CA2_4_10I2R6MassTerm_sound CA2_4_10I2R6Entropy_sound) (by decide +kernel)
def CA2_4_10I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA2_4_10I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA2_4_10I2R7Raw_sound (a : PairSlot) :
    (CA2_4_10I2R7Raw a).Encloses (CA2_4_10I2R7Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA2_4_10I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R7Certificates_valid :
    CA2_4_10I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R7Certificates (CA2_4_10I2R7CertificateIndex a)).input
lemma CA2_4_10I2R7P_check : ∀ a : PairSlot, contains (CA2_4_10I2R7Raw a) (CA2_4_10I2R7P a) = true := by
  decide +kernel
lemma CA2_4_10I2R7P_sound (a : PairSlot) :
    (CA2_4_10I2R7P a).Encloses (CA2_4_10I2R7Value a) :=
  contains_sound (CA2_4_10I2R7Raw_sound a) (CA2_4_10I2R7P_check a)
def CA2_4_10I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R7Certificates (CA2_4_10I2R7CertificateIndex a)).output
lemma CA2_4_10I2R7Terms_sound (a : PairSlot) :
    (CA2_4_10I2R7Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R7Certificates_valid
    (CA2_4_10I2R7CertificateIndex a) (CA2_4_10I2R7P_sound a)
def CA2_4_10I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R7Entropy_sound : CA2_4_10I2R7Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R7Value CA2_4_10I2R7Terms CA2_4_10I2R7Terms_sound) (by decide +kernel)
def CA2_4_10I2R7Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R7Mass_sound : CA2_4_10I2R7Mass.Encloses (∑ a, CA2_4_10I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R7P CA2_4_10I2R7Value CA2_4_10I2R7P_sound) (by decide +kernel)
def CA2_4_10I2R7MassTerm : Ball := .exact 0
lemma CA2_4_10I2R7MassTerm_sound : CA2_4_10I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R7Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R7Mass_sound)
def CA2_4_10I2R7H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R7H_sound : CA2_4_10I2R7H.Encloses (homogeneousEntropy CA2_4_10I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R7Value CA2_4_10I2R7MassTerm_sound CA2_4_10I2R7Entropy_sound) (by decide +kernel)
def CA2_4_10I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA2_4_10I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA2_4_10I2R8Raw_sound (a : PairSlot) :
    (CA2_4_10I2R8Raw a).Encloses (CA2_4_10I2R8Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA2_4_10I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R8Certificates_valid :
    CA2_4_10I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R8Certificates (CA2_4_10I2R8CertificateIndex a)).input
lemma CA2_4_10I2R8P_check : ∀ a : PairSlot, contains (CA2_4_10I2R8Raw a) (CA2_4_10I2R8P a) = true := by
  decide +kernel
lemma CA2_4_10I2R8P_sound (a : PairSlot) :
    (CA2_4_10I2R8P a).Encloses (CA2_4_10I2R8Value a) :=
  contains_sound (CA2_4_10I2R8Raw_sound a) (CA2_4_10I2R8P_check a)
def CA2_4_10I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R8Certificates (CA2_4_10I2R8CertificateIndex a)).output
lemma CA2_4_10I2R8Terms_sound (a : PairSlot) :
    (CA2_4_10I2R8Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R8Certificates_valid
    (CA2_4_10I2R8CertificateIndex a) (CA2_4_10I2R8P_sound a)
def CA2_4_10I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R8Entropy_sound : CA2_4_10I2R8Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R8Value CA2_4_10I2R8Terms CA2_4_10I2R8Terms_sound) (by decide +kernel)
def CA2_4_10I2R8Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R8Mass_sound : CA2_4_10I2R8Mass.Encloses (∑ a, CA2_4_10I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R8P CA2_4_10I2R8Value CA2_4_10I2R8P_sound) (by decide +kernel)
def CA2_4_10I2R8MassTerm : Ball := .exact 0
lemma CA2_4_10I2R8MassTerm_sound : CA2_4_10I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R8Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R8Mass_sound)
def CA2_4_10I2R8H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R8H_sound : CA2_4_10I2R8H.Encloses (homogeneousEntropy CA2_4_10I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R8Value CA2_4_10I2R8MassTerm_sound CA2_4_10I2R8Entropy_sound) (by decide +kernel)
def CA2_4_10I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA2_4_10I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA2_4_10I2R9Raw_sound (a : PairSlot) :
    (CA2_4_10I2R9Raw a).Encloses (CA2_4_10I2R9Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA2_4_10I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R9Certificates_valid :
    CA2_4_10I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R9Certificates (CA2_4_10I2R9CertificateIndex a)).input
lemma CA2_4_10I2R9P_check : ∀ a : PairSlot, contains (CA2_4_10I2R9Raw a) (CA2_4_10I2R9P a) = true := by
  decide +kernel
lemma CA2_4_10I2R9P_sound (a : PairSlot) :
    (CA2_4_10I2R9P a).Encloses (CA2_4_10I2R9Value a) :=
  contains_sound (CA2_4_10I2R9Raw_sound a) (CA2_4_10I2R9P_check a)
def CA2_4_10I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R9Certificates (CA2_4_10I2R9CertificateIndex a)).output
lemma CA2_4_10I2R9Terms_sound (a : PairSlot) :
    (CA2_4_10I2R9Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R9Certificates_valid
    (CA2_4_10I2R9CertificateIndex a) (CA2_4_10I2R9P_sound a)
def CA2_4_10I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R9Entropy_sound : CA2_4_10I2R9Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R9Value CA2_4_10I2R9Terms CA2_4_10I2R9Terms_sound) (by decide +kernel)
def CA2_4_10I2R9Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R9Mass_sound : CA2_4_10I2R9Mass.Encloses (∑ a, CA2_4_10I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R9P CA2_4_10I2R9Value CA2_4_10I2R9P_sound) (by decide +kernel)
def CA2_4_10I2R9MassTerm : Ball := .exact 0
lemma CA2_4_10I2R9MassTerm_sound : CA2_4_10I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R9Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R9Mass_sound)
def CA2_4_10I2R9H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R9H_sound : CA2_4_10I2R9H.Encloses (homogeneousEntropy CA2_4_10I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R9Value CA2_4_10I2R9MassTerm_sound CA2_4_10I2R9Entropy_sound) (by decide +kernel)
def CA2_4_10I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA2_4_10I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA2_4_10I2R10Raw_sound (a : PairSlot) :
    (CA2_4_10I2R10Raw a).Encloses (CA2_4_10I2R10Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA2_4_10I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R10Certificates_valid :
    CA2_4_10I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R10Certificates (CA2_4_10I2R10CertificateIndex a)).input
lemma CA2_4_10I2R10P_check : ∀ a : PairSlot, contains (CA2_4_10I2R10Raw a) (CA2_4_10I2R10P a) = true := by
  decide +kernel
lemma CA2_4_10I2R10P_sound (a : PairSlot) :
    (CA2_4_10I2R10P a).Encloses (CA2_4_10I2R10Value a) :=
  contains_sound (CA2_4_10I2R10Raw_sound a) (CA2_4_10I2R10P_check a)
def CA2_4_10I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R10Certificates (CA2_4_10I2R10CertificateIndex a)).output
lemma CA2_4_10I2R10Terms_sound (a : PairSlot) :
    (CA2_4_10I2R10Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R10Certificates_valid
    (CA2_4_10I2R10CertificateIndex a) (CA2_4_10I2R10P_sound a)
def CA2_4_10I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R10Entropy_sound : CA2_4_10I2R10Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R10Value CA2_4_10I2R10Terms CA2_4_10I2R10Terms_sound) (by decide +kernel)
def CA2_4_10I2R10Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R10Mass_sound : CA2_4_10I2R10Mass.Encloses (∑ a, CA2_4_10I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R10P CA2_4_10I2R10Value CA2_4_10I2R10P_sound) (by decide +kernel)
def CA2_4_10I2R10MassTerm : Ball := .exact 0
lemma CA2_4_10I2R10MassTerm_sound : CA2_4_10I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R10Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R10Mass_sound)
def CA2_4_10I2R10H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R10H_sound : CA2_4_10I2R10H.Encloses (homogeneousEntropy CA2_4_10I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R10Value CA2_4_10I2R10MassTerm_sound CA2_4_10I2R10Entropy_sound) (by decide +kernel)
def CA2_4_10I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA2_4_10I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA2_4_10I2R11Raw_sound (a : PairSlot) :
    (CA2_4_10I2R11Raw a).Encloses (CA2_4_10I2R11Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA2_4_10I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R11Certificates_valid :
    CA2_4_10I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R11Certificates (CA2_4_10I2R11CertificateIndex a)).input
lemma CA2_4_10I2R11P_check : ∀ a : PairSlot, contains (CA2_4_10I2R11Raw a) (CA2_4_10I2R11P a) = true := by
  decide +kernel
lemma CA2_4_10I2R11P_sound (a : PairSlot) :
    (CA2_4_10I2R11P a).Encloses (CA2_4_10I2R11Value a) :=
  contains_sound (CA2_4_10I2R11Raw_sound a) (CA2_4_10I2R11P_check a)
def CA2_4_10I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R11Certificates (CA2_4_10I2R11CertificateIndex a)).output
lemma CA2_4_10I2R11Terms_sound (a : PairSlot) :
    (CA2_4_10I2R11Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R11Certificates_valid
    (CA2_4_10I2R11CertificateIndex a) (CA2_4_10I2R11P_sound a)
def CA2_4_10I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R11Entropy_sound : CA2_4_10I2R11Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R11Value CA2_4_10I2R11Terms CA2_4_10I2R11Terms_sound) (by decide +kernel)
def CA2_4_10I2R11Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R11Mass_sound : CA2_4_10I2R11Mass.Encloses (∑ a, CA2_4_10I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R11P CA2_4_10I2R11Value CA2_4_10I2R11P_sound) (by decide +kernel)
def CA2_4_10I2R11MassTerm : Ball := .exact 0
lemma CA2_4_10I2R11MassTerm_sound : CA2_4_10I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R11Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R11Mass_sound)
def CA2_4_10I2R11H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R11H_sound : CA2_4_10I2R11H.Encloses (homogeneousEntropy CA2_4_10I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R11Value CA2_4_10I2R11MassTerm_sound CA2_4_10I2R11Entropy_sound) (by decide +kernel)
def CA2_4_10I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA2_4_10I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA2_4_10I2R12Raw_sound (a : PairSlot) :
    (CA2_4_10I2R12Raw a).Encloses (CA2_4_10I2R12Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA2_4_10I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R12Certificates_valid :
    CA2_4_10I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R12Certificates (CA2_4_10I2R12CertificateIndex a)).input
lemma CA2_4_10I2R12P_check : ∀ a : PairSlot, contains (CA2_4_10I2R12Raw a) (CA2_4_10I2R12P a) = true := by
  decide +kernel
lemma CA2_4_10I2R12P_sound (a : PairSlot) :
    (CA2_4_10I2R12P a).Encloses (CA2_4_10I2R12Value a) :=
  contains_sound (CA2_4_10I2R12Raw_sound a) (CA2_4_10I2R12P_check a)
def CA2_4_10I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R12Certificates (CA2_4_10I2R12CertificateIndex a)).output
lemma CA2_4_10I2R12Terms_sound (a : PairSlot) :
    (CA2_4_10I2R12Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R12Certificates_valid
    (CA2_4_10I2R12CertificateIndex a) (CA2_4_10I2R12P_sound a)
def CA2_4_10I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R12Entropy_sound : CA2_4_10I2R12Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R12Value CA2_4_10I2R12Terms CA2_4_10I2R12Terms_sound) (by decide +kernel)
def CA2_4_10I2R12Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R12Mass_sound : CA2_4_10I2R12Mass.Encloses (∑ a, CA2_4_10I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R12P CA2_4_10I2R12Value CA2_4_10I2R12P_sound) (by decide +kernel)
def CA2_4_10I2R12MassTerm : Ball := .exact 0
lemma CA2_4_10I2R12MassTerm_sound : CA2_4_10I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R12Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R12Mass_sound)
def CA2_4_10I2R12H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R12H_sound : CA2_4_10I2R12H.Encloses (homogeneousEntropy CA2_4_10I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R12Value CA2_4_10I2R12MassTerm_sound CA2_4_10I2R12Entropy_sound) (by decide +kernel)
def CA2_4_10I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA2_4_10I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA2_4_10I2R13Raw_sound (a : PairSlot) :
    (CA2_4_10I2R13Raw a).Encloses (CA2_4_10I2R13Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA2_4_10I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R13Certificates_valid :
    CA2_4_10I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R13Certificates (CA2_4_10I2R13CertificateIndex a)).input
lemma CA2_4_10I2R13P_check : ∀ a : PairSlot, contains (CA2_4_10I2R13Raw a) (CA2_4_10I2R13P a) = true := by
  decide +kernel
lemma CA2_4_10I2R13P_sound (a : PairSlot) :
    (CA2_4_10I2R13P a).Encloses (CA2_4_10I2R13Value a) :=
  contains_sound (CA2_4_10I2R13Raw_sound a) (CA2_4_10I2R13P_check a)
def CA2_4_10I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R13Certificates (CA2_4_10I2R13CertificateIndex a)).output
lemma CA2_4_10I2R13Terms_sound (a : PairSlot) :
    (CA2_4_10I2R13Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R13Certificates_valid
    (CA2_4_10I2R13CertificateIndex a) (CA2_4_10I2R13P_sound a)
def CA2_4_10I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R13Entropy_sound : CA2_4_10I2R13Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R13Value CA2_4_10I2R13Terms CA2_4_10I2R13Terms_sound) (by decide +kernel)
def CA2_4_10I2R13Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R13Mass_sound : CA2_4_10I2R13Mass.Encloses (∑ a, CA2_4_10I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R13P CA2_4_10I2R13Value CA2_4_10I2R13P_sound) (by decide +kernel)
def CA2_4_10I2R13MassTerm : Ball := .exact 0
lemma CA2_4_10I2R13MassTerm_sound : CA2_4_10I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R13Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R13Mass_sound)
def CA2_4_10I2R13H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R13H_sound : CA2_4_10I2R13H.Encloses (homogeneousEntropy CA2_4_10I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R13Value CA2_4_10I2R13MassTerm_sound CA2_4_10I2R13Entropy_sound) (by decide +kernel)
def CA2_4_10I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA2_4_10I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA2_4_10I2R14Raw_sound (a : PairSlot) :
    (CA2_4_10I2R14Raw a).Encloses (CA2_4_10I2R14Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA2_4_10I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R14Certificates_valid :
    CA2_4_10I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R14Certificates (CA2_4_10I2R14CertificateIndex a)).input
lemma CA2_4_10I2R14P_check : ∀ a : PairSlot, contains (CA2_4_10I2R14Raw a) (CA2_4_10I2R14P a) = true := by
  decide +kernel
lemma CA2_4_10I2R14P_sound (a : PairSlot) :
    (CA2_4_10I2R14P a).Encloses (CA2_4_10I2R14Value a) :=
  contains_sound (CA2_4_10I2R14Raw_sound a) (CA2_4_10I2R14P_check a)
def CA2_4_10I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R14Certificates (CA2_4_10I2R14CertificateIndex a)).output
lemma CA2_4_10I2R14Terms_sound (a : PairSlot) :
    (CA2_4_10I2R14Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R14Certificates_valid
    (CA2_4_10I2R14CertificateIndex a) (CA2_4_10I2R14P_sound a)
def CA2_4_10I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R14Entropy_sound : CA2_4_10I2R14Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R14Value CA2_4_10I2R14Terms CA2_4_10I2R14Terms_sound) (by decide +kernel)
def CA2_4_10I2R14Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R14Mass_sound : CA2_4_10I2R14Mass.Encloses (∑ a, CA2_4_10I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R14P CA2_4_10I2R14Value CA2_4_10I2R14P_sound) (by decide +kernel)
def CA2_4_10I2R14MassTerm : Ball := .exact 0
lemma CA2_4_10I2R14MassTerm_sound : CA2_4_10I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R14Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R14Mass_sound)
def CA2_4_10I2R14H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R14H_sound : CA2_4_10I2R14H.Encloses (homogeneousEntropy CA2_4_10I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R14Value CA2_4_10I2R14MassTerm_sound CA2_4_10I2R14Entropy_sound) (by decide +kernel)
def CA2_4_10I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA2_4_10I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA2_4_10I2R15Raw_sound (a : PairSlot) :
    (CA2_4_10I2R15Raw a).Encloses (CA2_4_10I2R15Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA2_4_10I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R15Certificates_valid :
    CA2_4_10I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R15Certificates (CA2_4_10I2R15CertificateIndex a)).input
lemma CA2_4_10I2R15P_check : ∀ a : PairSlot, contains (CA2_4_10I2R15Raw a) (CA2_4_10I2R15P a) = true := by
  decide +kernel
lemma CA2_4_10I2R15P_sound (a : PairSlot) :
    (CA2_4_10I2R15P a).Encloses (CA2_4_10I2R15Value a) :=
  contains_sound (CA2_4_10I2R15Raw_sound a) (CA2_4_10I2R15P_check a)
def CA2_4_10I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R15Certificates (CA2_4_10I2R15CertificateIndex a)).output
lemma CA2_4_10I2R15Terms_sound (a : PairSlot) :
    (CA2_4_10I2R15Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R15Certificates_valid
    (CA2_4_10I2R15CertificateIndex a) (CA2_4_10I2R15P_sound a)
def CA2_4_10I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R15Entropy_sound : CA2_4_10I2R15Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R15Value CA2_4_10I2R15Terms CA2_4_10I2R15Terms_sound) (by decide +kernel)
def CA2_4_10I2R15Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R15Mass_sound : CA2_4_10I2R15Mass.Encloses (∑ a, CA2_4_10I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R15P CA2_4_10I2R15Value CA2_4_10I2R15P_sound) (by decide +kernel)
def CA2_4_10I2R15MassTerm : Ball := .exact 0
lemma CA2_4_10I2R15MassTerm_sound : CA2_4_10I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R15Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R15Mass_sound)
def CA2_4_10I2R15H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R15H_sound : CA2_4_10I2R15H.Encloses (homogeneousEntropy CA2_4_10I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R15Value CA2_4_10I2R15MassTerm_sound CA2_4_10I2R15Entropy_sound) (by decide +kernel)
def CA2_4_10I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA2_4_10I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 4 10)) A2_4_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA2_4_10I2R16Raw_sound (a : PairSlot) :
    (CA2_4_10I2R16Raw a).Encloses (CA2_4_10I2R16Value a) := by
  exact residualBall_sound_on (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 4 10) (show (shape 2 4 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA2_4_10I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_4_10I2R16Certificates_valid :
    CA2_4_10I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_4_10I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R16Certificates (CA2_4_10I2R16CertificateIndex a)).input
lemma CA2_4_10I2R16P_check : ∀ a : PairSlot, contains (CA2_4_10I2R16Raw a) (CA2_4_10I2R16P a) = true := by
  decide +kernel
lemma CA2_4_10I2R16P_sound (a : PairSlot) :
    (CA2_4_10I2R16P a).Encloses (CA2_4_10I2R16Value a) :=
  contains_sound (CA2_4_10I2R16Raw_sound a) (CA2_4_10I2R16P_check a)
def CA2_4_10I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I2R16Certificates (CA2_4_10I2R16CertificateIndex a)).output
lemma CA2_4_10I2R16Terms_sound (a : PairSlot) :
    (CA2_4_10I2R16Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I2R16Certificates_valid
    (CA2_4_10I2R16CertificateIndex a) (CA2_4_10I2R16P_sound a)
def CA2_4_10I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R16Entropy_sound : CA2_4_10I2R16Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_4_10I2R16Value CA2_4_10I2R16Terms CA2_4_10I2R16Terms_sound) (by decide +kernel)
def CA2_4_10I2R16Mass : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R16Mass_sound : CA2_4_10I2R16Mass.Encloses (∑ a, CA2_4_10I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_4_10I2R16P CA2_4_10I2R16Value CA2_4_10I2R16P_sound) (by decide +kernel)
def CA2_4_10I2R16MassTerm : Ball := .exact 0
lemma CA2_4_10I2R16MassTerm_sound : CA2_4_10I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I2R16Value a))) :=
  entropyTerm_zero_ball (CA2_4_10I2R16Mass_sound)
def CA2_4_10I2R16H : Ball := ⟨0, 0⟩
lemma CA2_4_10I2R16H_sound : CA2_4_10I2R16H.Encloses (homogeneousEntropy CA2_4_10I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I2R16Value CA2_4_10I2R16MassTerm_sound CA2_4_10I2R16Entropy_sound) (by decide +kernel)
def CA2_4_10I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_4_10I2R0H
  | 1 => CA2_4_10I2R1H
  | 2 => CA2_4_10I2R2H
  | 3 => CA2_4_10I2R3H
  | 4 => CA2_4_10I2R4H
  | 5 => CA2_4_10I2R5H
  | 6 => CA2_4_10I2R6H
  | 7 => CA2_4_10I2R7H
  | 8 => CA2_4_10I2R8H
  | 9 => CA2_4_10I2R9H
  | 10 => CA2_4_10I2R10H
  | 11 => CA2_4_10I2R11H
  | 12 => CA2_4_10I2R12H
  | 13 => CA2_4_10I2R13H
  | 14 => CA2_4_10I2R14H
  | 15 => CA2_4_10I2R15H
  | 16 => CA2_4_10I2R16H
  | _ => (.exact 0)
lemma CA2_4_10I2ResidualEntropies_sound (k : Fin 17) :
    (CA2_4_10I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_4_10I2R0H_sound
  · exact CA2_4_10I2R1H_sound
  · exact CA2_4_10I2R2H_sound
  · exact CA2_4_10I2R3H_sound
  · exact CA2_4_10I2R4H_sound
  · exact CA2_4_10I2R5H_sound
  · exact CA2_4_10I2R6H_sound
  · exact CA2_4_10I2R7H_sound
  · exact CA2_4_10I2R8H_sound
  · exact CA2_4_10I2R9H_sound
  · exact CA2_4_10I2R10H_sound
  · exact CA2_4_10I2R11H_sound
  · exact CA2_4_10I2R12H_sound
  · exact CA2_4_10I2R13H_sound
  · exact CA2_4_10I2R14H_sound
  · exact CA2_4_10I2R15H_sound
  · exact CA2_4_10I2R16H_sound
def CA2_4_10I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | _, _, _ => (.exact 0)
lemma CA2_4_10I2Singles_sound (u : Shape) (hu : u ∈ below (shape 2 4 10))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA2_4_10I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A2_4_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def CA2_4_10I2Singleton : Ball := ⟨(16222574466090492566167298681711 / 50000000000000000000000000000000), (27623665329 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I2Singleton_sound : CA2_4_10I2Singleton.Encloses
    (singletonEntropy (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA2_4_10I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_4_10Law_sound u) CA2_4_10I2Singles_sound) (by decide +kernel)
def CA2_4_10I2Group : Ball := ⟨(10815853413606162866468887861101 / 12500000000000000000000000000000), (75679181287 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I2Group_sound : CA2_4_10I2Group.Encloses
    (groupedEntropy (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_4_10I2Singleton_sound
    (finSumBall_sound 17 CA2_4_10I2ResidualEntropies _ CA2_4_10I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA2_4_10I2H : Ball := ⟨(114361613035409002036379178824189 / 100000000000000000000000000000000), (472233660579 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I2_sound : CA2_4_10I2H.Encloses (stageACapacity (shape 2 4 10) 2) := by
  have hb := contains_sound (Ball.add_sound CA2_4_10I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA2_4_10I2Group_sound)))
    (show contains (.add CA2_4_10I2PairH (.neg (.mul (.exact 2) CA2_4_10I2Group))) CA2_4_10I2H = true by decide +kernel)
  unfold CA2_4_10I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
