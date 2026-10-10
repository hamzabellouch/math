import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB1_3_4
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal1_1_6

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_2_5U0_0_4Leaf : Ball := ⟨0, 0⟩
lemma B1_2_5U0_0_4Leaf_sound : B1_2_5U0_0_4Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 0 0 4)) := by
  have hh : shapeMax (shape 0 0 4) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  change (Ball.exact 0).Encloses 0
  simpa only [Rat.cast_zero] using Ball.exact_sound 0
def B1_2_5U0_0_4Mass : Ball := ⟨(10839580338829366322698124931 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_2_5U0_0_4Mass_sound : B1_2_5U0_0_4Mass.Encloses (littleMass (shape 1 2 5) (shape 0 0 4) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 0 0 4))) (by decide +kernel)
def B1_2_5U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_2_5U0_1_3Leaf_sound : B1_2_5U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
def B1_2_5U0_1_3Mass : Ball := ⟨(1186081054548533539957298951707 / 25000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
lemma B1_2_5U0_1_3Mass_sound : B1_2_5U0_1_3Mass.Encloses (littleMass (shape 1 2 5) (shape 0 1 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 0 1 3))) (by decide +kernel)
def B1_2_5U0_2_2D : Ball := .exact (19531 / 200000)
lemma B1_2_5U0_2_2D_sound : B1_2_5U0_2_2D.Encloses (binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_2_5U0_2_2OneD : Ball := .exact (180469 / 200000)
lemma B1_2_5U0_2_2OneD_sound : B1_2_5U0_2_2OneD.Encloses (1 - (binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 1 2 5) (shape 0 2 2) = (19531 / 200000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((180469 / 200000) : ℚ) using 1 <;> norm_num [B1_2_5U0_2_2OneD, Ball.exact]
def B1_2_5U0_2_2EDLogWitness : LogWitness := ⟨-4, 19531, 12500⟩
def B1_2_5U0_2_2EDLog : Ball := ⟨(-232631441969328242519371516318041 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B1_2_5U0_2_2EDLog_sound : B1_2_5U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_2_5U0_2_2D_sound) (w := B1_2_5U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_2_5U0_2_2ED : Ball := ⟨(11358811732757374761614612713019 / 50000000000000000000000000000000), (1033962531 / 10000000000000000000000000000000)⟩
lemma B1_2_5U0_2_2ED_sound : B1_2_5U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_2_5U0_2_2D_sound) B1_2_5U0_2_2EDLog_sound) (by decide +kernel)
def B1_2_5U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 180469, 100000⟩
def B1_2_5U0_2_2EOneDLog : Ball := ⟨(-2568958716933578869052947578733 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B1_2_5U0_2_2EOneDLog_sound : B1_2_5U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_2_5U0_2_2OneD_sound) (w := B1_2_5U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_2_5U0_2_2EOneD : Ball := ⟨(9272348213725720898382327931727 / 100000000000000000000000000000000), (38215797243 / 100000000000000000000000000000000)⟩
lemma B1_2_5U0_2_2EOneD_sound : B1_2_5U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_2_5U0_2_2OneD_sound) B1_2_5U0_2_2EOneDLog_sound) (by decide +kernel)
def B1_2_5U0_2_2BinaryEntropy : Ball := ⟨(7751780094199723268145106355019 / 20000000000000000000000000000000), (52691272677 / 100000000000000000000000000000000)⟩
lemma B1_2_5U0_2_2BinaryEntropy_sound : B1_2_5U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 2 5) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_2_5U0_2_2EOneD_sound B1_2_5U0_2_2ED_sound)
    (Ball.mul_sound B1_2_5U0_2_2D_sound logN2_sound)) (by decide +kernel)
def B1_2_5U0_2_2Leaf : Ball := ⟨(164606275545034138422274949480111 / 50000000000000000000000000000000), (33467732881 / 20000000000000000000000000000000)⟩
lemma B1_2_5U0_2_2Leaf_sound : B1_2_5U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B1_2_5U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B1_2_5U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
def B1_2_5U0_2_2Mass : Ball := ⟨(340073829440952693670776139029 / 12500000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
lemma B1_2_5U0_2_2Mass_sound : B1_2_5U0_2_2Mass.Encloses (littleMass (shape 1 2 5) (shape 0 2 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 0 2 2))) (by decide +kernel)
def B1_2_5U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_2_5U1_0_3Leaf_sound : B1_2_5U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
def B1_2_5U1_0_3Mass : Ball := ⟨(340073829440952693670776139029 / 12500000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
lemma B1_2_5U1_0_3Mass_sound : B1_2_5U1_0_3Mass.Encloses (littleMass (shape 1 2 5) (shape 1 0 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 1 0 3))) (by decide +kernel)
def B1_2_5U1_1_2D : Ball := .exact 0
lemma B1_2_5U1_1_2D_sound : B1_2_5U1_1_2D.Encloses (binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_2_5U1_1_2OneD : Ball := .exact 1
lemma B1_2_5U1_1_2OneD_sound : B1_2_5U1_1_2OneD.Encloses (1 - (binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 1 2 5) (shape 1 1 2) = 0 := by decide +kernel
  rw [he]
  convert Ball.exact_sound (1 : ℚ) using 1 <;> norm_num [B1_2_5U1_1_2OneD, Ball.exact]
def B1_2_5U1_1_2ED : Ball := .exact 0
lemma B1_2_5U1_1_2ED_sound : B1_2_5U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ))) :=
  entropyTerm_zero_ball (B1_2_5U1_1_2D_sound)
def B1_2_5U1_1_2EOneDLog : Ball := .exact 0
lemma B1_2_5U1_1_2EOneDLog_sound : B1_2_5U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ)))) := by
  exact log_exact_one_ball (B1_2_5U1_1_2OneD_sound)
def B1_2_5U1_1_2EOneD : Ball := ⟨0, 0⟩
lemma B1_2_5U1_1_2EOneD_sound : B1_2_5U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_2_5U1_1_2OneD_sound) B1_2_5U1_1_2EOneDLog_sound) (by decide +kernel)
def B1_2_5U1_1_2BinaryEntropy : Ball := ⟨0, 0⟩
lemma B1_2_5U1_1_2BinaryEntropy_sound : B1_2_5U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 2 5) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_2_5U1_1_2EOneD_sound B1_2_5U1_1_2ED_sound)
    (Ball.mul_sound B1_2_5U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B1_2_5U1_1_2Leaf : Ball := ⟨(40235947810852509365018973782911 / 12500000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B1_2_5U1_1_2Leaf_sound : B1_2_5U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact 2).Encloses (2 - (binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 1 2 5) (shape 1 1 2) = 0 := by decide +kernel
    rw [he]
    convert Ball.exact_sound (2 : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B1_2_5U1_1_2Mass : Ball := ⟨(1186081054548533539957298951707 / 25000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
lemma B1_2_5U1_1_2Mass_sound : B1_2_5U1_1_2Mass.Encloses (littleMass (shape 1 2 5) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 1 1 2))) (by decide +kernel)
def B1_2_5U1_2_1D : Ball := .exact (10533 / 250000)
lemma B1_2_5U1_2_1D_sound : B1_2_5U1_2_1D.Encloses (binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_2_5U1_2_1OneD : Ball := .exact (239467 / 250000)
lemma B1_2_5U1_2_1OneD_sound : B1_2_5U1_2_1OneD.Encloses (1 - (binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 1 2 5) (shape 1 2 1) = (10533 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((239467 / 250000) : ℚ) using 1 <;> norm_num [B1_2_5U1_2_1OneD, Ball.exact]
def B1_2_5U1_2_1EDLogWitness : LogWitness := ⟨-5, 21066, 15625⟩
def B1_2_5U1_2_1EDLog : Ball := ⟨(-316694773200784155107075107979101 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B1_2_5U1_2_1EDLog_sound : B1_2_5U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_2_5U1_2_1D_sound) (w := B1_2_5U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_2_5U1_2_1ED : Ball := ⟨(21348774695192700836754061519 / 160000000000000000000000000000), (5353078821 / 100000000000000000000000000000000)⟩
lemma B1_2_5U1_2_1ED_sound : B1_2_5U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_2_5U1_2_1D_sound) B1_2_5U1_2_1EDLog_sound) (by decide +kernel)
def B1_2_5U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 239467, 125000⟩
def B1_2_5U1_2_1EOneDLog : Ball := ⟨(-4304529756115245594727191194021 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B1_2_5U1_2_1EOneDLog_sound : B1_2_5U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_2_5U1_2_1OneD_sound) (w := B1_2_5U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_2_5U1_2_1EOneD : Ball := ⟨(824634261686119613466029034927 / 20000000000000000000000000000000), (507091097 / 1250000000000000000000000000000)⟩
lemma B1_2_5U1_2_1EOneD_sound : B1_2_5U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_2_5U1_2_1OneD_sound) B1_2_5U1_2_1EOneDLog_sound) (by decide +kernel)
def B1_2_5U1_2_1BinaryEntropy : Ball := ⟨(20386523194061197667938115193607 / 100000000000000000000000000000000), (47704726189 / 100000000000000000000000000000000)⟩
lemma B1_2_5U1_2_1BinaryEntropy_sound : B1_2_5U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 2 5) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_2_5U1_2_1EOneD_sound B1_2_5U1_2_1ED_sound)
    (Ball.mul_sound B1_2_5U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B1_2_5U1_2_1Leaf : Ball := ⟨(157553349337076361610941936324801 / 50000000000000000000000000000000), (124378402689 / 100000000000000000000000000000000)⟩
lemma B1_2_5U1_2_1Leaf_sound : B1_2_5U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (489467 / 250000)).Encloses (2 - (binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 1 2 5) (shape 1 2 1) = (10533 / 250000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((489467 / 250000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B1_2_5U1_2_1Mass : Ball := ⟨(10839580338829366322698124931 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_2_5U1_2_1Mass_sound : B1_2_5U1_2_1Mass.Encloses (littleMass (shape 1 2 5) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 1 2 1))) (by decide +kernel)
def B1_2_5Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_2_5U0_0_4Leaf
  | 0, 1, 3 => B1_2_5U0_1_3Leaf
  | 0, 2, 2 => B1_2_5U0_2_2Leaf
  | 1, 0, 3 => B1_2_5U1_0_3Leaf
  | 1, 1, 2 => B1_2_5U1_1_2Leaf
  | 1, 2, 1 => B1_2_5U1_2_1Leaf
  | _, _, _ => (.exact 0)
lemma B1_2_5Leaves_sound (u : Shape) (hu : u ∈ below (shape 1 2 5)) :
    (B1_2_5Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) u) := by
  rw [B1_2_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_2_5U0_0_4Leaf_sound
  · exact B1_2_5U0_1_3Leaf_sound
  · exact B1_2_5U0_2_2Leaf_sound
  · exact B1_2_5U1_0_3Leaf_sound
  · exact B1_2_5U1_1_2Leaf_sound
  · exact B1_2_5U1_2_1Leaf_sound
def B1_2_5Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_2_5U0_0_4Mass
  | 0, 1, 3 => B1_2_5U0_1_3Mass
  | 0, 2, 2 => B1_2_5U0_2_2Mass
  | 1, 0, 3 => B1_2_5U1_0_3Mass
  | 1, 1, 2 => B1_2_5U1_1_2Mass
  | 1, 2, 1 => B1_2_5U1_2_1Mass
  | _, _, _ => (.exact 0)
lemma B1_2_5Masses_sound (u : Shape) (hu : u ∈ below (shape 1 2 5)) :
    (B1_2_5Masses u).Encloses ((fun u => (littleMass (shape 1 2 5) u : ℝ)) u) := by
  rw [B1_2_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_2_5U0_0_4Mass_sound
  · exact B1_2_5U0_1_3Mass_sound
  · exact B1_2_5U0_2_2Mass_sound
  · exact B1_2_5U1_0_3Mass_sound
  · exact B1_2_5U1_1_2Mass_sound
  · exact B1_2_5U1_2_1Mass_sound
def B1_2_5Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_2_5U0_2_2BinaryEntropy
  | 1, 1, 2 => B1_2_5U1_1_2BinaryEntropy
  | 1, 2, 1 => B1_2_5U1_2_1BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B1_2_5Binaries_sound (u : Shape) (hu : u ∈ (below (shape 1 2 5)).filter positive) :
    (B1_2_5Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 1 2 5) u)) u) := by
  have hl : (below (shape 1 2 5)).filter positive = [(shape 1 1 2), (shape 1 2 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B1_2_5U1_1_2BinaryEntropy_sound
  · exact B1_2_5U1_2_1BinaryEntropy_sound
def B1_2_5S2 : Ball := ⟨(41450674273625169102162892218041 / 100000000000000000000000000000000), (16917009863 / 100000000000000000000000000000000)⟩
lemma B1_2_5S2_sound : B1_2_5S2.Encloses
    (((below (shape 1 2 5)).map fun u => (littleMass (shape 1 2 5) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 1 2 5) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 1 2 5))
    (fun u => .mul (B1_2_5Masses u) (B1_2_5Leaves u)) _
    (fun u hu => Ball.mul_sound (B1_2_5Masses_sound u hu) (B1_2_5Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
