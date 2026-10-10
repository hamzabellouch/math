import Mathlib
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
def B2_3_3U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_3_3U0_1_3Leaf_sound : B2_3_3U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_3_3U0_1_3Mass : Ball := ⟨(466550470537589006566890154189 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
lemma B2_3_3U0_1_3Mass_sound : B2_3_3U0_1_3Mass.Encloses (littleMass (shape 2 3 3) (shape 0 1 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_3_3))
    (B2_3_3Law_sound (shape 0 1 3))) (by decide +kernel)
def B2_3_3U0_2_2D : Ball := .exact (55041 / 500000)
lemma B2_3_3U0_2_2D_sound : B2_3_3U0_2_2D.Encloses (binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_3_3U0_2_2OneD : Ball := .exact (444959 / 500000)
lemma B2_3_3U0_2_2OneD_sound : B2_3_3U0_2_2OneD.Encloses (1 - (binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 2 3 3) (shape 0 2 2) = (55041 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((444959 / 500000) : ℚ) using 1 <;> norm_num [B2_3_3U0_2_2OneD, Ball.exact]
def B2_3_3U0_2_2EDLogWitness : LogWitness := ⟨-4, 55041, 31250⟩
def B2_3_3U0_2_2EDLog : Ball := ⟨(-55163243408937486421493177388873 / 25000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B2_3_3U0_2_2EDLog_sound : B2_3_3U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U0_2_2D_sound) (w := B2_3_3U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U0_2_2ED : Ball := ⟨(3036240080471328190125405976661 / 12500000000000000000000000000000), (5827692557 / 50000000000000000000000000000000)⟩
lemma B2_3_3U0_2_2ED_sound : B2_3_3U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U0_2_2D_sound) B2_3_3U0_2_2EDLog_sound) (by decide +kernel)
def B2_3_3U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 444959, 250000⟩
def B2_3_3U0_2_2EOneDLog : Ball := ⟨(-5831297766604325579437218806789 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_3_3U0_2_2EOneDLog_sound : B2_3_3U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U0_2_2OneD_sound) (w := B2_3_3U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U0_2_2EOneD : Ball := ⟨(51893768458609882110016108861 / 500000000000000000000000000000), (37689493321 / 100000000000000000000000000000000)⟩
lemma B2_3_3U0_2_2EOneD_sound : B2_3_3U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U0_2_2OneD_sound) B2_3_3U0_2_2EOneDLog_sound) (by decide +kernel)
def B2_3_3U0_2_2BinaryEntropy : Ball := ⟨(21149488564266295949066621061427 / 50000000000000000000000000000000), (54007032481 / 100000000000000000000000000000000)⟩
lemma B2_3_3U0_2_2BinaryEntropy_sound : B2_3_3U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 3 3) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_3_3U0_2_2EOneD_sound B2_3_3U0_2_2ED_sound)
    (Ball.mul_sound B2_3_3U0_2_2D_sound logN2_sound)) (by decide +kernel)
def B2_3_3U0_2_2Leaf : Ball := ⟨(328752530760038539330924883010379 / 100000000000000000000000000000000), (41768878111 / 25000000000000000000000000000000)⟩
lemma B2_3_3U0_2_2Leaf_sound : B2_3_3U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B2_3_3U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_3_3U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
def B2_3_3U0_2_2Mass : Ball := ⟨(3278427034394245768597523877587 / 25000000000000000000000000000000), (67 / 50000000000000000000000000000000)⟩
lemma B2_3_3U0_2_2Mass_sound : B2_3_3U0_2_2Mass.Encloses (littleMass (shape 2 3 3) (shape 0 2 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_3_3))
    (B2_3_3Law_sound (shape 0 2 2))) (by decide +kernel)
def B2_3_3U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_3_3U0_3_1Leaf_sound : B2_3_3U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_3_3U0_3_1Mass : Ball := ⟨(14715925893121844557257952283 / 1562500000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
lemma B2_3_3U0_3_1Mass_sound : B2_3_3U0_3_1Mass.Encloses (littleMass (shape 2 3 3) (shape 0 3 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_3_3))
    (B2_3_3Law_sound (shape 0 3 1))) (by decide +kernel)
def B2_3_3U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_3_3U1_0_3Leaf_sound : B2_3_3U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_3_3U1_0_3Mass : Ball := ⟨(64933664603666840044717438439 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma B2_3_3U1_0_3Mass_sound : B2_3_3U1_0_3Mass.Encloses (littleMass (shape 2 3 3) (shape 1 0 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_3_3))
    (B2_3_3Law_sound (shape 1 0 3))) (by decide +kernel)
def B2_3_3U1_1_2D : Ball := .exact (573 / 125000)
lemma B2_3_3U1_1_2D_sound : B2_3_3U1_1_2D.Encloses (binaryParameter (shape 2 3 3) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_3_3U1_1_2OneD : Ball := .exact (124427 / 125000)
lemma B2_3_3U1_1_2OneD_sound : B2_3_3U1_1_2OneD.Encloses (1 - (binaryParameter (shape 2 3 3) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 2 3 3) (shape 1 1 2) = (573 / 125000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((124427 / 125000) : ℚ) using 1 <;> norm_num [B2_3_3U1_1_2OneD, Ball.exact]
def B2_3_3U1_1_2EDLogWitness : LogWitness := ⟨-8, 18336, 15625⟩
def B2_3_3U1_1_2EDLog : Ball := ⟨(-21540733198278794446444222587871 / 4000000000000000000000000000000), (95291206573 / 50000000000000000000000000000000)⟩
lemma B2_3_3U1_1_2EDLog_sound : B2_3_3U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 3 3) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U1_1_2D_sound) (w := B2_3_3U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U1_1_2ED : Ball := ⟨(246856802452274984356250790857 / 10000000000000000000000000000000), (436814891 / 50000000000000000000000000000000)⟩
lemma B2_3_3U1_1_2ED_sound : B2_3_3U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 3 3) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U1_1_2D_sound) B2_3_3U1_1_2EDLog_sound) (by decide +kernel)
def B2_3_3U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 124427, 62500⟩
def B2_3_3U1_1_2EOneDLog : Ball := ⟨(-22972693733715313906167338253 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_3_3U1_1_2EOneDLog_sound : B2_3_3U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 3 3) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U1_1_2OneD_sound) (w := B2_3_3U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U1_1_2EOneD : Ball := ⟨(457347738112799258144429343489 / 100000000000000000000000000000000), (8431501483 / 20000000000000000000000000000000)⟩
lemma B2_3_3U1_1_2EOneD_sound : B2_3_3U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 3 3) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U1_1_2OneD_sound) B2_3_3U1_1_2EOneDLog_sound) (by decide +kernel)
def B2_3_3U1_1_2BinaryEntropy : Ball := ⟨(1621827215102114015771898184501 / 50000000000000000000000000000000), (43225277149 / 100000000000000000000000000000000)⟩
lemma B2_3_3U1_1_2BinaryEntropy_sound : B2_3_3U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 3 3) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_3_3U1_1_2EOneD_sound B2_3_3U1_1_2ED_sound)
    (Ball.mul_sound B2_3_3U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B2_3_3U1_1_2Leaf : Ball := ⟨(64229963229552056661686960472001 / 20000000000000000000000000000000), (31690933043 / 25000000000000000000000000000000)⟩
lemma B2_3_3U1_1_2Leaf_sound : B2_3_3U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (249427 / 125000)).Encloses (2 - (binaryParameter (shape 2 3 3) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 2 3 3) (shape 1 1 2) = (573 / 125000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((249427 / 125000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_3_3U1_1_2Mass : Ball := ⟨(25412930157212049388918541585447 / 100000000000000000000000000000000), (239 / 100000000000000000000000000000000)⟩
lemma B2_3_3U1_1_2Mass_sound : B2_3_3U1_1_2Mass.Encloses (littleMass (shape 2 3 3) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_3_3))
    (B2_3_3Law_sound (shape 1 1 2))) (by decide +kernel)
def B2_3_3U1_2_1D : Ball := .exact (1687 / 40000)
lemma B2_3_3U1_2_1D_sound : B2_3_3U1_2_1D.Encloses (binaryParameter (shape 2 3 3) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_3_3U1_2_1OneD : Ball := .exact (38313 / 40000)
lemma B2_3_3U1_2_1OneD_sound : B2_3_3U1_2_1OneD.Encloses (1 - (binaryParameter (shape 2 3 3) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 2 3 3) (shape 1 2 1) = (1687 / 40000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((38313 / 40000) : ℚ) using 1 <;> norm_num [B2_3_3U1_2_1OneD, Ball.exact]
def B2_3_3U1_2_1EDLogWitness : LogWitness := ⟨-5, 1687, 1250⟩
def B2_3_3U1_2_1EDLog : Ball := ⟨(-316592765055010505433466504472543 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B2_3_3U1_2_1EDLog_sound : B2_3_3U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 2 3 3) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U1_2_1D_sound) (w := B2_3_3U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U1_2_1ED : Ball := ⟨(1335229986619506806665644982613 / 10000000000000000000000000000000), (669817773 / 12500000000000000000000000000000)⟩
lemma B2_3_3U1_2_1ED_sound : B2_3_3U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 3 3) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U1_2_1D_sound) B2_3_3U1_2_1EDLog_sound) (by decide +kernel)
def B2_3_3U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 38313, 20000⟩
def B2_3_3U1_2_1EOneDLog : Ball := ⟨(-2154509496585081089533142092769 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_3_3U1_2_1EOneDLog_sound : B2_3_3U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 3 3) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U1_2_1OneD_sound) (w := B2_3_3U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U1_2_1EOneD : Ball := ⟨(4127286117133210589164163650013 / 100000000000000000000000000000000), (40565466639 / 100000000000000000000000000000000)⟩
lemma B2_3_3U1_2_1EOneD_sound : B2_3_3U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 3 3) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U1_2_1OneD_sound) B2_3_3U1_2_1EOneDLog_sound) (by decide +kernel)
def B2_3_3U1_2_1BinaryEntropy : Ball := ⟨(20402934217339847998287789143041 / 100000000000000000000000000000000), (47710189551 / 100000000000000000000000000000000)⟩
lemma B2_3_3U1_2_1BinaryEntropy_sound : B2_3_3U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 3 3) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_3_3U1_2_1EOneD_sound B2_3_3U1_2_1ED_sound)
    (Ball.mul_sound B2_3_3U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B2_3_3U1_2_1Leaf : Ball := ⟨(315099778091129256590273089386111 / 100000000000000000000000000000000), (124375671007 / 100000000000000000000000000000000)⟩
lemma B2_3_3U1_2_1Leaf_sound : B2_3_3U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (78313 / 40000)).Encloses (2 - (binaryParameter (shape 2 3 3) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 2 3 3) (shape 1 2 1) = (1687 / 40000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((78313 / 40000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_3_3U1_2_1Mass : Ball := ⟨(25412930157212049388918541585447 / 100000000000000000000000000000000), (239 / 100000000000000000000000000000000)⟩
lemma B2_3_3U1_2_1Mass_sound : B2_3_3U1_2_1Mass.Encloses (littleMass (shape 2 3 3) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_3_3))
    (B2_3_3Law_sound (shape 1 2 1))) (by decide +kernel)
def B2_3_3U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_3_3U1_3_0Leaf_sound : B2_3_3U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_3_3U1_3_0Mass : Ball := ⟨(64933664603666840044717438439 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma B2_3_3U1_3_0Mass_sound : B2_3_3U1_3_0Mass.Encloses (littleMass (shape 2 3 3) (shape 1 3 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_3_3))
    (B2_3_3Law_sound (shape 1 3 0))) (by decide +kernel)
def B2_3_3U2_0_2D : Ball := .exact (104091 / 1000000)
lemma B2_3_3U2_0_2D_sound : B2_3_3U2_0_2D.Encloses (binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_3_3U2_0_2OneD : Ball := .exact (895909 / 1000000)
lemma B2_3_3U2_0_2OneD_sound : B2_3_3U2_0_2OneD.Encloses (1 - (binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 2 3 3) (shape 2 0 2) = (104091 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((895909 / 1000000) : ℚ) using 1 <;> norm_num [B2_3_3U2_0_2OneD, Ball.exact]
def B2_3_3U2_0_2EDLogWitness : LogWitness := ⟨-4, 104091, 62500⟩
def B2_3_3U2_0_2EDLog : Ball := ⟨(-56562244060752588474630885788059 / 25000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma B2_3_3U2_0_2EDLog_sound : B2_3_3U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U2_0_2D_sound) (w := B2_3_3U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U2_0_2ED : Ball := ⟨(23550482186111190747651214130259 / 100000000000000000000000000000000), (2755265829 / 25000000000000000000000000000000)⟩
lemma B2_3_3U2_0_2ED_sound : B2_3_3U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U2_0_2D_sound) B2_3_3U2_0_2EDLog_sound) (by decide +kernel)
def B2_3_3U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 895909, 500000⟩
def B2_3_3U2_0_2EOneDLog : Ball := ⟨(-10991643366502651450018611428491 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_3_3U2_0_2EOneDLog_sound : B2_3_3U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U2_0_2OneD_sound) (w := B2_3_3U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U2_0_2EOneD : Ball := ⟨(615469513552501497370920259143 / 6250000000000000000000000000000), (37943222041 / 100000000000000000000000000000000)⟩
lemma B2_3_3U2_0_2EOneD_sound : B2_3_3U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U2_0_2OneD_sound) B2_3_3U2_0_2EOneDLog_sound) (by decide +kernel)
def B2_3_3U2_0_2BinaryEntropy : Ball := ⟨(40613032720117741425840847164349 / 100000000000000000000000000000000), (53372710683 / 100000000000000000000000000000000)⟩
lemma B2_3_3U2_0_2BinaryEntropy_sound : B2_3_3U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 3 3) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_3_3U2_0_2EOneD_sound B2_3_3U2_0_2ED_sound)
    (Ball.mul_sound B2_3_3U2_0_2D_sound logN2_sound)) (by decide +kernel)
def B2_3_3U2_0_2Leaf : Ball := ⟨(328995014858302227927479117427341 / 100000000000000000000000000000000), (41800594201 / 25000000000000000000000000000000)⟩
lemma B2_3_3U2_0_2Leaf_sound : B2_3_3U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B2_3_3U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_3_3U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
def B2_3_3U2_0_2Mass : Ball := ⟨(14715925893121844557257952283 / 1562500000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
lemma B2_3_3U2_0_2Mass_sound : B2_3_3U2_0_2Mass.Encloses (littleMass (shape 2 3 3) (shape 2 0 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_3_3))
    (B2_3_3Law_sound (shape 2 0 2))) (by decide +kernel)
def B2_3_3U2_1_1D : Ball := .exact (19419 / 500000)
lemma B2_3_3U2_1_1D_sound : B2_3_3U2_1_1D.Encloses (binaryParameter (shape 2 3 3) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_3_3U2_1_1OneD : Ball := .exact (480581 / 500000)
lemma B2_3_3U2_1_1OneD_sound : B2_3_3U2_1_1OneD.Encloses (1 - (binaryParameter (shape 2 3 3) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 2 3 3) (shape 2 1 1) = (19419 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((480581 / 500000) : ℚ) using 1 <;> norm_num [B2_3_3U2_1_1OneD, Ball.exact]
def B2_3_3U2_1_1EDLogWitness : LogWitness := ⟨-5, 19419, 15625⟩
def B2_3_3U2_1_1EDLog : Ball := ⟨(-40604451627383861448565069676439 / 12500000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B2_3_3U2_1_1EDLog_sound : B2_3_3U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 2 3 3) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U2_1_1D_sound) (w := B2_3_3U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U2_1_1ED : Ball := ⟨(3153991384608668821878740352187 / 25000000000000000000000000000000), (2467279921 / 50000000000000000000000000000000)⟩
lemma B2_3_3U2_1_1ED_sound : B2_3_3U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 3 3) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U2_1_1D_sound) B2_3_3U2_1_1EDLog_sound) (by decide +kernel)
def B2_3_3U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 480581, 250000⟩
def B2_3_3U2_1_1EOneDLog : Ball := ⟨(-990307745431186665804901172341 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_3_3U2_1_1EOneDLog_sound : B2_3_3U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 3 3) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U2_1_1OneD_sound) (w := B2_3_3U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U2_1_1EOneD : Ball := ⟨(1903692346428260476156740841219 / 50000000000000000000000000000000), (40706794087 / 100000000000000000000000000000000)⟩
lemma B2_3_3U2_1_1EOneD_sound : B2_3_3U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 3 3) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U2_1_1OneD_sound) B2_3_3U2_1_1EOneDLog_sound) (by decide +kernel)
def B2_3_3U2_1_1BinaryEntropy : Ball := ⟨(152923162009199294660344707703 / 800000000000000000000000000000), (4728620721 / 10000000000000000000000000000000)⟩
lemma B2_3_3U2_1_1BinaryEntropy_sound : B2_3_3U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 3 3) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_3_3U2_1_1EOneD_sound B2_3_3U2_1_1ED_sound)
    (Ball.mul_sound B2_3_3U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B2_3_3U2_1_1Leaf : Ball := ⟨(63127369504501703177055472529633 / 20000000000000000000000000000000), (62293831089 / 50000000000000000000000000000000)⟩
lemma B2_3_3U2_1_1Leaf_sound : B2_3_3U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (980581 / 500000)).Encloses (2 - (binaryParameter (shape 2 3 3) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 2 3 3) (shape 2 1 1) = (19419 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((980581 / 500000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_3_3U2_1_1Mass : Ball := ⟨(3278427034394245768597523877587 / 25000000000000000000000000000000), (67 / 50000000000000000000000000000000)⟩
lemma B2_3_3U2_1_1Mass_sound : B2_3_3U2_1_1Mass.Encloses (littleMass (shape 2 3 3) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_3_3))
    (B2_3_3Law_sound (shape 2 1 1))) (by decide +kernel)
def B2_3_3U2_2_0D : Ball := .exact (102383 / 1000000)
lemma B2_3_3U2_2_0D_sound : B2_3_3U2_2_0D.Encloses (binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_3_3U2_2_0OneD : Ball := .exact (897617 / 1000000)
lemma B2_3_3U2_2_0OneD_sound : B2_3_3U2_2_0OneD.Encloses (1 - (binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 2 3 3) (shape 2 2 0) = (102383 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((897617 / 1000000) : ℚ) using 1 <;> norm_num [B2_3_3U2_2_0OneD, Ball.exact]
def B2_3_3U2_2_0EDLogWitness : LogWitness := ⟨-4, 102383, 62500⟩
def B2_3_3U2_2_0EDLog : Ball := ⟨(-56975864894596222495907774317173 / 25000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma B2_3_3U2_2_0EDLog_sound : B2_3_3U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U2_2_0D_sound) (w := B2_3_3U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U2_2_0ED : Ball := ⟨(1166671995100689009559705131583 / 5000000000000000000000000000000), (5420110891 / 50000000000000000000000000000000)⟩
lemma B2_3_3U2_2_0ED_sound : B2_3_3U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U2_2_0D_sound) B2_3_3U2_2_0EDLog_sound) (by decide +kernel)
def B2_3_3U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 897617, 500000⟩
def B2_3_3U2_2_0EOneDLog : Ball := ⟨(-2160236099982276913212034276979 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_3_3U2_2_0EOneDLog_sound : B2_3_3U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U2_2_0OneD_sound) (w := B2_3_3U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_3_3U2_2_0EOneD : Ball := ⟨(1939064647357791456006646571599 / 20000000000000000000000000000000), (7603111731 / 20000000000000000000000000000000)⟩
lemma B2_3_3U2_2_0EOneD_sound : B2_3_3U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U2_2_0OneD_sound) B2_3_3U2_2_0EOneDLog_sound) (by decide +kernel)
def B2_3_3U2_2_0BinaryEntropy : Ball := ⟨(40125411917529625532633781163727 / 100000000000000000000000000000000), (1063837383 / 2000000000000000000000000000000)⟩
lemma B2_3_3U2_2_0BinaryEntropy_sound : B2_3_3U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 3 3) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_3_3U2_2_0EOneD_sound B2_3_3U2_2_0ED_sound)
    (Ball.mul_sound B2_3_3U2_2_0D_sound logN2_sound)) (by decide +kernel)
def B2_3_3U2_2_0Leaf : Ball := ⟨(329057178046601600722235670684489 / 100000000000000000000000000000000), (20904818139 / 12500000000000000000000000000000)⟩
lemma B2_3_3U2_2_0Leaf_sound : B2_3_3U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B2_3_3U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_3_3U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
def B2_3_3U2_2_0Mass : Ball := ⟨(466550470537589006566890154189 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
lemma B2_3_3U2_2_0Mass_sound : B2_3_3U2_2_0Mass.Encloses (littleMass (shape 2 3 3) (shape 2 2 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_3_3))
    (B2_3_3Law_sound (shape 2 2 0))) (by decide +kernel)
def B2_3_3Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B2_3_3U0_1_3Leaf
  | 0, 2, 2 => B2_3_3U0_2_2Leaf
  | 0, 3, 1 => B2_3_3U0_3_1Leaf
  | 1, 0, 3 => B2_3_3U1_0_3Leaf
  | 1, 1, 2 => B2_3_3U1_1_2Leaf
  | 1, 2, 1 => B2_3_3U1_2_1Leaf
  | 1, 3, 0 => B2_3_3U1_3_0Leaf
  | 2, 0, 2 => B2_3_3U2_0_2Leaf
  | 2, 1, 1 => B2_3_3U2_1_1Leaf
  | 2, 2, 0 => B2_3_3U2_2_0Leaf
  | _, _, _ => (.exact 0)
lemma B2_3_3Leaves_sound (u : Shape) (hu : u ∈ below (shape 2 3 3)) :
    (B2_3_3Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) u) := by
  rw [B2_3_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_3_3U0_1_3Leaf_sound
  · exact B2_3_3U0_2_2Leaf_sound
  · exact B2_3_3U0_3_1Leaf_sound
  · exact B2_3_3U1_0_3Leaf_sound
  · exact B2_3_3U1_1_2Leaf_sound
  · exact B2_3_3U1_2_1Leaf_sound
  · exact B2_3_3U1_3_0Leaf_sound
  · exact B2_3_3U2_0_2Leaf_sound
  · exact B2_3_3U2_1_1Leaf_sound
  · exact B2_3_3U2_2_0Leaf_sound
def B2_3_3Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B2_3_3U0_1_3Mass
  | 0, 2, 2 => B2_3_3U0_2_2Mass
  | 0, 3, 1 => B2_3_3U0_3_1Mass
  | 1, 0, 3 => B2_3_3U1_0_3Mass
  | 1, 1, 2 => B2_3_3U1_1_2Mass
  | 1, 2, 1 => B2_3_3U1_2_1Mass
  | 1, 3, 0 => B2_3_3U1_3_0Mass
  | 2, 0, 2 => B2_3_3U2_0_2Mass
  | 2, 1, 1 => B2_3_3U2_1_1Mass
  | 2, 2, 0 => B2_3_3U2_2_0Mass
  | _, _, _ => (.exact 0)
lemma B2_3_3Masses_sound (u : Shape) (hu : u ∈ below (shape 2 3 3)) :
    (B2_3_3Masses u).Encloses ((fun u => (littleMass (shape 2 3 3) u : ℝ)) u) := by
  rw [B2_3_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_3_3U0_1_3Mass_sound
  · exact B2_3_3U0_2_2Mass_sound
  · exact B2_3_3U0_3_1Mass_sound
  · exact B2_3_3U1_0_3Mass_sound
  · exact B2_3_3U1_1_2Mass_sound
  · exact B2_3_3U1_2_1Mass_sound
  · exact B2_3_3U1_3_0Mass_sound
  · exact B2_3_3U2_0_2Mass_sound
  · exact B2_3_3U2_1_1Mass_sound
  · exact B2_3_3U2_2_0Mass_sound
def B2_3_3Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B2_3_3U0_2_2BinaryEntropy
  | 1, 1, 2 => B2_3_3U1_1_2BinaryEntropy
  | 1, 2, 1 => B2_3_3U1_2_1BinaryEntropy
  | 2, 0, 2 => B2_3_3U2_0_2BinaryEntropy
  | 2, 1, 1 => B2_3_3U2_1_1BinaryEntropy
  | 2, 2, 0 => B2_3_3U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B2_3_3Binaries_sound (u : Shape) (hu : u ∈ (below (shape 2 3 3)).filter positive) :
    (B2_3_3Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 2 3 3) u)) u) := by
  have hl : (below (shape 2 3 3)).filter positive = [(shape 1 1 2), (shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact B2_3_3U1_1_2BinaryEntropy_sound
  · exact B2_3_3U1_2_1BinaryEntropy_sound
  · exact B2_3_3U2_1_1BinaryEntropy_sound
def B2_3_3S2 : Ball := ⟨(257277205828662462897692981670147 / 100000000000000000000000000000000), (53506556373 / 50000000000000000000000000000000)⟩
lemma B2_3_3S2_sound : B2_3_3S2.Encloses
    (((below (shape 2 3 3)).map fun u => (littleMass (shape 2 3 3) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 2 3 3) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 2 3 3))
    (fun u => .mul (B2_3_3Masses u) (B2_3_3Leaves u)) _
    (fun u hu => Ball.mul_sound (B2_3_3Masses_sound u hu) (B2_3_3Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
