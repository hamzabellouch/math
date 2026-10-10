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
def B5_1_2U1_1_2D : Ball := .exact (42047 / 1000000)
lemma B5_1_2U1_1_2D_sound : B5_1_2U1_1_2D.Encloses (binaryParameter (shape 5 1 2) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B5_1_2U1_1_2OneD : Ball := .exact (957953 / 1000000)
lemma B5_1_2U1_1_2OneD_sound : B5_1_2U1_1_2OneD.Encloses (1 - (binaryParameter (shape 5 1 2) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 5 1 2) (shape 1 1 2) = (42047 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((957953 / 1000000) : ℚ) using 1 <;> norm_num [B5_1_2U1_1_2OneD, Ball.exact]
def B5_1_2U1_1_2EDLogWitness : LogWitness := ⟨-5, 42047, 31250⟩
def B5_1_2U1_1_2EDLog : Ball := ⟨(-316896723874678398578307138430309 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B5_1_2U1_1_2EDLog_sound : B5_1_2U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 5 1 2) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B5_1_2U1_1_2D_sound) (w := B5_1_2U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_1_2U1_1_2ED : Ball := ⟨(13324556548758602625022080249579 / 100000000000000000000000000000000), (5342279151 / 100000000000000000000000000000000)⟩
lemma B5_1_2U1_1_2ED_sound : B5_1_2U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 5 1 2) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B5_1_2U1_1_2D_sound) B5_1_2U1_1_2EDLog_sound) (by decide +kernel)
def B5_1_2U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 957953, 500000⟩
def B5_1_2U1_1_2EOneDLog : Ball := ⟨(-4295656275758179541792934076201 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B5_1_2U1_1_2EOneDLog_sound : B5_1_2U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 5 1 2) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B5_1_2U1_1_2OneD_sound) (w := B5_1_2U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_1_2U1_1_2EOneD : Ball := ⟨(4115036816331375366599166577099 / 100000000000000000000000000000000), (811417753 / 2000000000000000000000000000000)⟩
lemma B5_1_2U1_1_2EOneD_sound : B5_1_2U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 5 1 2) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B5_1_2U1_1_2OneD_sound) B5_1_2U1_1_2EOneDLog_sound) (by decide +kernel)
def B5_1_2U1_1_2BinaryEntropy : Ball := ⟨(4070813863038076006825576384973 / 20000000000000000000000000000000), (23846963259 / 50000000000000000000000000000000)⟩
lemma B5_1_2U1_1_2BinaryEntropy_sound : B5_1_2U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 5 1 2) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B5_1_2U1_1_2EOneD_sound B5_1_2U1_1_2ED_sound)
    (Ball.mul_sound B5_1_2U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B5_1_2U1_1_2Leaf : Ball := ⟨(19695023681025525817191748693793 / 6250000000000000000000000000000), (31095950631 / 25000000000000000000000000000000)⟩
lemma B5_1_2U1_1_2Leaf_sound : B5_1_2U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1957953 / 1000000)).Encloses (2 - (binaryParameter (shape 5 1 2) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 5 1 2) (shape 1 1 2) = (42047 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1957953 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B5_1_2U1_1_2Mass : Ball := ⟨(263347289989209950085958267 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B5_1_2U1_1_2Mass_sound : B5_1_2U1_1_2Mass.Encloses (littleMass (shape 5 1 2) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 1 1 2))) (by decide +kernel)
def B5_1_2U2_0_2D : Ball := .exact (6867 / 62500)
lemma B5_1_2U2_0_2D_sound : B5_1_2U2_0_2D.Encloses (binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B5_1_2U2_0_2OneD : Ball := .exact (55633 / 62500)
lemma B5_1_2U2_0_2OneD_sound : B5_1_2U2_0_2OneD.Encloses (1 - (binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 5 1 2) (shape 2 0 2) = (6867 / 62500) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((55633 / 62500) : ℚ) using 1 <;> norm_num [B5_1_2U2_0_2OneD, Ball.exact]
def B5_1_2U2_0_2EDLogWitness : LogWitness := ⟨-4, 27468, 15625⟩
def B5_1_2U2_0_2EDLog : Ball := ⟨(-22084392271038164781658598089709 / 10000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B5_1_2U2_0_2EDLog_sound : B5_1_2U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B5_1_2U2_0_2D_sound) (w := B5_1_2U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_1_2U2_0_2ED : Ball := ⟨(38823301561656083854246295829 / 160000000000000000000000000000), (11633150499 / 100000000000000000000000000000000)⟩
lemma B5_1_2U2_0_2ED_sound : B5_1_2U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B5_1_2U2_0_2D_sound) B5_1_2U2_0_2EDLog_sound) (by decide +kernel)
def B5_1_2U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 55633, 31250⟩
def B5_1_2U2_0_2EOneDLog : Ball := ⟨(-2327800127447388996729312677817 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B5_1_2U2_0_2EOneDLog_sound : B5_1_2U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B5_1_2U2_0_2OneD_sound) (w := B5_1_2U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_1_2U2_0_2EOneD : Ball := ⟨(10360200359222447364403348176399 / 100000000000000000000000000000000), (1178074599 / 3125000000000000000000000000000)⟩
lemma B5_1_2U2_0_2EOneD_sound : B5_1_2U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B5_1_2U2_0_2OneD_sound) B5_1_2U2_0_2EOneDLog_sound) (by decide +kernel)
def B5_1_2U2_0_2BinaryEntropy : Ball := ⟨(844810210750114617538725874727 / 2000000000000000000000000000000), (53984797867 / 100000000000000000000000000000000)⟩
lemma B5_1_2U2_0_2BinaryEntropy_sound : B5_1_2U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 5 1 2) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B5_1_2U2_0_2EOneD_sound B5_1_2U2_0_2ED_sound)
    (Ball.mul_sound B5_1_2U2_0_2D_sound logN2_sound)) (by decide +kernel)
def B5_1_2U2_0_2Leaf : Ball := ⟨(32876166056133391052546116649983 / 10000000000000000000000000000000), (167079959367 / 100000000000000000000000000000000)⟩
lemma B5_1_2U2_0_2Leaf_sound : B5_1_2U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B5_1_2U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B5_1_2U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
def B5_1_2U2_0_2Mass : Ball := ⟨(26175208896406964988043914431 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B5_1_2U2_0_2Mass_sound : B5_1_2U2_0_2Mass.Encloses (littleMass (shape 5 1 2) (shape 2 0 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 2 0 2))) (by decide +kernel)
def B5_1_2U2_1_1D : Ball := .exact (1993 / 500000)
lemma B5_1_2U2_1_1D_sound : B5_1_2U2_1_1D.Encloses (binaryParameter (shape 5 1 2) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B5_1_2U2_1_1OneD : Ball := .exact (498007 / 500000)
lemma B5_1_2U2_1_1OneD_sound : B5_1_2U2_1_1OneD.Encloses (1 - (binaryParameter (shape 5 1 2) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 5 1 2) (shape 2 1 1) = (1993 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((498007 / 500000) : ℚ) using 1 <;> norm_num [B5_1_2U2_1_1OneD, Ball.exact]
def B5_1_2U2_1_1EDLogWitness : LogWitness := ⟨-8, 15944, 15625⟩
def B5_1_2U2_1_1EDLog : Ball := ⟨(-276248352859576703796786793426803 / 50000000000000000000000000000000), (95291206573 / 50000000000000000000000000000000)⟩
lemma B5_1_2U2_1_1EDLog_sound : B5_1_2U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 5 1 2) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B5_1_2U2_1_1D_sound) (w := B5_1_2U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_1_2U2_1_1ED : Ball := ⟨(1101125934498272741333992158599 / 50000000000000000000000000000000), (1519323 / 200000000000000000000000000000)⟩
lemma B5_1_2U2_1_1ED_sound : B5_1_2U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 5 1 2) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B5_1_2U2_1_1D_sound) B5_1_2U2_1_1EDLog_sound) (by decide +kernel)
def B5_1_2U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 498007, 250000⟩
def B5_1_2U2_1_1EOneDLog : Ball := ⟨(-399396527142702344795877217257 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B5_1_2U2_1_1EOneDLog_sound : B5_1_2U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 5 1 2) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B5_1_2U2_1_1OneD_sound) (w := B5_1_2U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_1_2U2_1_1EOneD : Ball := ⟨(397804532585511533249520850669 / 100000000000000000000000000000000), (421828337 / 1000000000000000000000000000000)⟩
lemma B5_1_2U2_1_1EOneD_sound : B5_1_2U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 5 1 2) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B5_1_2U2_1_1OneD_sound) B5_1_2U2_1_1EOneDLog_sound) (by decide +kernel)
def B5_1_2U2_1_1BinaryEntropy : Ball := ⟨(1438172433876625608125606907683 / 50000000000000000000000000000000), (43111308867 / 100000000000000000000000000000000)⟩
lemma B5_1_2U2_1_1BinaryEntropy_sound : B5_1_2U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 5 1 2) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B5_1_2U2_1_1EOneD_sound B5_1_2U2_1_1ED_sound)
    (Ball.mul_sound B5_1_2U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B5_1_2U2_1_1Leaf : Ball := ⟨(321246060534923842510835927745293 / 100000000000000000000000000000000), (126801721599 / 100000000000000000000000000000000)⟩
lemma B5_1_2U2_1_1Leaf_sound : B5_1_2U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (998007 / 500000)).Encloses (2 - (binaryParameter (shape 5 1 2) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 5 1 2) (shape 2 1 1) = (1993 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((998007 / 500000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B5_1_2U2_1_1Mass : Ball := ⟨(46409897166330493680741531629 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B5_1_2U2_1_1Mass_sound : B5_1_2U2_1_1Mass.Encloses (littleMass (shape 5 1 2) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 2 1 1))) (by decide +kernel)
def B5_1_2U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B5_1_2U3_0_1Leaf_sound : B5_1_2U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B5_1_2U3_0_1Mass : Ball := ⟨(46409897166330493680741531629 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B5_1_2U3_0_1Mass_sound : B5_1_2U3_0_1Mass.Encloses (littleMass (shape 5 1 2) (shape 3 0 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 3 0 1))) (by decide +kernel)
def B5_1_2U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B5_1_2U3_1_0Leaf_sound : B5_1_2U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B5_1_2U3_1_0Mass : Ball := ⟨(26175208896406964988043914431 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B5_1_2U3_1_0Mass_sound : B5_1_2U3_1_0Mass.Encloses (littleMass (shape 5 1 2) (shape 3 1 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 3 1 0))) (by decide +kernel)
def B5_1_2U4_0_0Leaf : Ball := ⟨0, 0⟩
lemma B5_1_2U4_0_0Leaf_sound : B5_1_2U4_0_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 4 0 0)) := by
  have hh : shapeMax (shape 4 0 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [Rat.cast_zero, B5_1_2U4_0_0Leaf, Ball.exact] using Ball.exact_sound 0
def B5_1_2U4_0_0Mass : Ball := ⟨(263347289989209950085958267 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B5_1_2U4_0_0Mass_sound : B5_1_2U4_0_0Mass.Encloses (littleMass (shape 5 1 2) (shape 4 0 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 4 0 0))) (by decide +kernel)
def B5_1_2Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B5_1_2U1_1_2Leaf
  | 2, 0, 2 => B5_1_2U2_0_2Leaf
  | 2, 1, 1 => B5_1_2U2_1_1Leaf
  | 3, 0, 1 => B5_1_2U3_0_1Leaf
  | 3, 1, 0 => B5_1_2U3_1_0Leaf
  | 4, 0, 0 => B5_1_2U4_0_0Leaf
  | _, _, _ => (.exact 0)
lemma B5_1_2Leaves_sound (u : Shape) (hu : u ∈ below (shape 5 1 2)) :
    (B5_1_2Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) u) := by
  rw [B5_1_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_1_2U1_1_2Leaf_sound
  · exact B5_1_2U2_0_2Leaf_sound
  · exact B5_1_2U2_1_1Leaf_sound
  · exact B5_1_2U3_0_1Leaf_sound
  · exact B5_1_2U3_1_0Leaf_sound
  · exact B5_1_2U4_0_0Leaf_sound
def B5_1_2Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B5_1_2U1_1_2Mass
  | 2, 0, 2 => B5_1_2U2_0_2Mass
  | 2, 1, 1 => B5_1_2U2_1_1Mass
  | 3, 0, 1 => B5_1_2U3_0_1Mass
  | 3, 1, 0 => B5_1_2U3_1_0Mass
  | 4, 0, 0 => B5_1_2U4_0_0Mass
  | _, _, _ => (.exact 0)
lemma B5_1_2Masses_sound (u : Shape) (hu : u ∈ below (shape 5 1 2)) :
    (B5_1_2Masses u).Encloses ((fun u => (littleMass (shape 5 1 2) u : ℝ)) u) := by
  rw [B5_1_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_1_2U1_1_2Mass_sound
  · exact B5_1_2U2_0_2Mass_sound
  · exact B5_1_2U2_1_1Mass_sound
  · exact B5_1_2U3_0_1Mass_sound
  · exact B5_1_2U3_1_0Mass_sound
  · exact B5_1_2U4_0_0Mass_sound
def B5_1_2Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B5_1_2U1_1_2BinaryEntropy
  | 2, 0, 2 => B5_1_2U2_0_2BinaryEntropy
  | 2, 1, 1 => B5_1_2U2_1_1BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B5_1_2Binaries_sound (u : Shape) (hu : u ∈ (below (shape 5 1 2)).filter positive) :
    (B5_1_2Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 5 1 2) u)) u) := by
  have hl : (below (shape 5 1 2)).filter positive = [(shape 1 1 2), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B5_1_2U1_1_2BinaryEntropy_sound
  · exact B5_1_2U2_1_1BinaryEntropy_sound
def B5_1_2S2 : Ball := ⟨(202798422436966096303225510443 / 50000000000000000000000000000000), (165374319 / 100000000000000000000000000000000)⟩
lemma B5_1_2S2_sound : B5_1_2S2.Encloses
    (((below (shape 5 1 2)).map fun u => (littleMass (shape 5 1 2) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 5 1 2) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 5 1 2))
    (fun u => .mul (B5_1_2Masses u) (B5_1_2Leaves u)) _
    (fun u hu => Ball.mul_sound (B5_1_2Masses_sound u hu) (B5_1_2Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
