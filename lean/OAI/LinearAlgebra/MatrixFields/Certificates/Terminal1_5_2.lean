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
def B1_5_2U0_2_2D : Ball := .exact (109933 / 1000000)
lemma B1_5_2U0_2_2D_sound : B1_5_2U0_2_2D.Encloses (binaryParameter (shape 1 5 2) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_5_2U0_2_2OneD : Ball := .exact (890067 / 1000000)
lemma B1_5_2U0_2_2OneD_sound : B1_5_2U0_2_2OneD.Encloses (1 - (binaryParameter (shape 1 5 2) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 1 5 2) (shape 0 2 2) = (109933 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((890067 / 1000000) : ℚ) using 1 <;> norm_num [B1_5_2U0_2_2OneD, Ball.exact]
def B1_5_2U0_2_2EDLogWitness : LogWitness := ⟨-4, 109933, 62500⟩
def B1_5_2U0_2_2EDLog : Ball := ⟨(-220788418967003649163974598210309 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B1_5_2U0_2_2EDLog_sound : B1_5_2U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 1 5 2) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_5_2U0_2_2D_sound) (w := B1_5_2U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_5_2U0_2_2ED : Ball := ⟨(12135966631149806081771609752527 / 50000000000000000000000000000000), (93116873 / 800000000000000000000000000000)⟩
lemma B1_5_2U0_2_2ED_sound : B1_5_2U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 5 2) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_5_2U0_2_2D_sound) B1_5_2U0_2_2EDLog_sound) (by decide +kernel)
def B1_5_2U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 890067, 500000⟩
def B1_5_2U0_2_2EOneDLog : Ball := ⟨(-11645853819053979009096802094341 / 100000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma B1_5_2U0_2_2EOneDLog_sound : B1_5_2U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 5 2) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_5_2U0_2_2OneD_sound) (w := B1_5_2U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_5_2U0_2_2EOneD : Ball := ⟨(1295698771395489741836220418713 / 12500000000000000000000000000000), (9423950929 / 25000000000000000000000000000000)⟩
lemma B1_5_2U0_2_2EOneD_sound : B1_5_2U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 5 2) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_5_2U0_2_2OneD_sound) B1_5_2U0_2_2EOneDLog_sound) (by decide +kernel)
def B1_5_2U0_2_2BinaryEntropy : Ball := ⟨(1056437458337829421706235965909 / 2500000000000000000000000000000), (53991256491 / 100000000000000000000000000000000)⟩
lemma B1_5_2U0_2_2BinaryEntropy_sound : B1_5_2U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 5 2) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_5_2U0_2_2EOneD_sound B1_5_2U0_2_2ED_sound)
    (Ball.mul_sound B1_5_2U0_2_2D_sound logN2_sound)) (by decide +kernel)
def B1_5_2U0_2_2Leaf : Ball := ⟨(164379506607404830246102091070317 / 50000000000000000000000000000000), (4176966691 / 2500000000000000000000000000000)⟩
lemma B1_5_2U0_2_2Leaf_sound : B1_5_2U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 5 2) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B1_5_2U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B1_5_2U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
def B1_5_2U0_2_2Mass : Ball := ⟨(27838926089202276630516723591 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma B1_5_2U0_2_2Mass_sound : B1_5_2U0_2_2Mass.Encloses (littleMass (shape 1 5 2) (shape 0 2 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_5_2))
    (B1_5_2Law_sound (shape 0 2 2))) (by decide +kernel)
def B1_5_2U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_5_2U0_3_1Leaf_sound : B1_5_2U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 5 2) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B1_5_2U0_3_1Mass : Ball := ⟨(394443851550199476968409845113 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
lemma B1_5_2U0_3_1Mass_sound : B1_5_2U0_3_1Mass.Encloses (littleMass (shape 1 5 2) (shape 0 3 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_5_2))
    (B1_5_2Law_sound (shape 0 3 1))) (by decide +kernel)
def B1_5_2U0_4_0Leaf : Ball := ⟨0, 0⟩
lemma B1_5_2U0_4_0Leaf_sound : B1_5_2U0_4_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 5 2) (shape 0 4 0)) := by
  have hh : shapeMax (shape 0 4 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B1_5_2U0_4_0Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B1_5_2U0_4_0Mass : Ball := ⟨(4456348111125662593963668059 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_5_2U0_4_0Mass_sound : B1_5_2U0_4_0Mass.Encloses (littleMass (shape 1 5 2) (shape 0 4 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_5_2))
    (B1_5_2Law_sound (shape 0 4 0))) (by decide +kernel)
def B1_5_2U1_1_2D : Ball := .exact (10523 / 250000)
lemma B1_5_2U1_1_2D_sound : B1_5_2U1_1_2D.Encloses (binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_5_2U1_1_2OneD : Ball := .exact (239477 / 250000)
lemma B1_5_2U1_1_2OneD_sound : B1_5_2U1_1_2OneD.Encloses (1 - (binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 1 5 2) (shape 1 1 2) = (10523 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((239477 / 250000) : ℚ) using 1 <;> norm_num [B1_5_2U1_1_2OneD, Ball.exact]
def B1_5_2U1_1_2EDLogWitness : LogWitness := ⟨-5, 21046, 15625⟩
def B1_5_2U1_1_2EDLog : Ball := ⟨(-15839487900517856513979567611963 / 5000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B1_5_2U1_1_2EDLog_sound : B1_5_2U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_5_2U1_1_2D_sound) (w := B1_5_2U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_5_2U1_1_2ED : Ball := ⟨(2666862898834390465545711839691 / 20000000000000000000000000000000), (5347996623 / 100000000000000000000000000000000)⟩
lemma B1_5_2U1_1_2ED_sound : B1_5_2U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_5_2U1_1_2D_sound) B1_5_2U1_1_2EDLog_sound) (by decide +kernel)
def B1_5_2U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 239477, 125000⟩
def B1_5_2U1_1_2EOneDLog : Ball := ⟨(-537544237821271786708674943729 / 12500000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B1_5_2U1_1_2EOneDLog_sound : B1_5_2U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_5_2U1_1_2OneD_sound) (w := B1_5_2U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_5_2U1_1_2EOneD : Ball := ⟨(205967170305159525865013359199 / 5000000000000000000000000000000), (20284490913 / 50000000000000000000000000000000)⟩
lemma B1_5_2U1_1_2EOneD_sound : B1_5_2U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_5_2U1_1_2OneD_sound) B1_5_2U1_1_2EOneDLog_sound) (by decide +kernel)
def B1_5_2U1_1_2BinaryEntropy : Ball := ⟨(20371253012688064641427839024309 / 100000000000000000000000000000000), (47699643991 / 100000000000000000000000000000000)⟩
lemma B1_5_2U1_1_2BinaryEntropy_sound : B1_5_2U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 5 2) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_5_2U1_1_2EOneD_sound B1_5_2U1_1_2ED_sound)
    (Ball.mul_sound B1_5_2U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B1_5_2U1_1_2Leaf : Ball := ⟨(315113136425802459623382275685407 / 100000000000000000000000000000000), (124380943787 / 100000000000000000000000000000000)⟩
lemma B1_5_2U1_1_2Leaf_sound : B1_5_2U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 5 2) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (489477 / 250000)).Encloses (2 - (binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 1 5 2) (shape 1 1 2) = (10523 / 250000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((489477 / 250000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B1_5_2U1_1_2Mass : Ball := ⟨(4456348111125662593963668059 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_5_2U1_1_2Mass_sound : B1_5_2U1_1_2Mass.Encloses (littleMass (shape 1 5 2) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_5_2))
    (B1_5_2Law_sound (shape 1 1 2))) (by decide +kernel)
def B1_5_2U1_2_1D : Ball := .exact (3747 / 1000000)
lemma B1_5_2U1_2_1D_sound : B1_5_2U1_2_1D.Encloses (binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_5_2U1_2_1OneD : Ball := .exact (996253 / 1000000)
lemma B1_5_2U1_2_1OneD_sound : B1_5_2U1_2_1OneD.Encloses (1 - (binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 1 5 2) (shape 1 2 1) = (3747 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((996253 / 1000000) : ℚ) using 1 <;> norm_num [B1_5_2U1_2_1OneD, Ball.exact]
def B1_5_2U1_2_1EDLogWitness : LogWitness := ⟨-9, 29976, 15625⟩
def B1_5_2U1_2_1EDLog : Ball := ⟨(-1745874924740808355355881138477 / 312500000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
lemma B1_5_2U1_2_1EDLog_sound : B1_5_2U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_5_2U1_2_1D_sound) (w := B1_5_2U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_5_2U1_2_1ED : Ball := ⟨(2093373869761218850405915720279 / 100000000000000000000000000000000), (396729057 / 50000000000000000000000000000000)⟩
lemma B1_5_2U1_2_1ED_sound : B1_5_2U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_5_2U1_2_1D_sound) B1_5_2U1_2_1EDLog_sound) (by decide +kernel)
def B1_5_2U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 996253, 500000⟩
def B1_5_2U1_2_1EOneDLog : Ball := ⟨(-750807517979978009641163873 / 200000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B1_5_2U1_2_1EOneDLog_sound : B1_5_2U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_5_2U1_2_1OneD_sound) (w := B1_5_2U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_5_2U1_2_1EOneD : Ball := ⟨(23374820069065844751219950999 / 6250000000000000000000000000000), (1318529867 / 3125000000000000000000000000000)⟩
lemma B1_5_2U1_2_1EOneD_sound : B1_5_2U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_5_2U1_2_1OneD_sound) B1_5_2U1_2_1EOneDLog_sound) (by decide +kernel)
def B1_5_2U1_2_1BinaryEntropy : Ball := ⟨(2727093239422083873864071740623 / 100000000000000000000000000000000), (21572552741 / 50000000000000000000000000000000)⟩
lemma B1_5_2U1_2_1BinaryEntropy_sound : B1_5_2U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 5 2) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_5_2U1_2_1EOneD_sound B1_5_2U1_2_1ED_sound)
    (Ball.mul_sound B1_5_2U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B1_5_2U1_2_1Leaf : Ball := ⟨(32128452610103101750978888588423 / 10000000000000000000000000000000), (25363380933 / 20000000000000000000000000000000)⟩
lemma B1_5_2U1_2_1Leaf_sound : B1_5_2U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 5 2) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1996253 / 1000000)).Encloses (2 - (binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 1 5 2) (shape 1 2 1) = (3747 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1996253 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B1_5_2U1_2_1Mass : Ball := ⟨(394443851550199476968409845113 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
lemma B1_5_2U1_2_1Mass_sound : B1_5_2U1_2_1Mass.Encloses (littleMass (shape 1 5 2) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_5_2))
    (B1_5_2Law_sound (shape 1 2 1))) (by decide +kernel)
def B1_5_2U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_5_2U1_3_0Leaf_sound : B1_5_2U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 5 2) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B1_5_2U1_3_0Mass : Ball := ⟨(27838926089202276630516723591 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma B1_5_2U1_3_0Mass_sound : B1_5_2U1_3_0Mass.Encloses (littleMass (shape 1 5 2) (shape 1 3 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_5_2))
    (B1_5_2Law_sound (shape 1 3 0))) (by decide +kernel)
def B1_5_2Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_5_2U0_2_2Leaf
  | 0, 3, 1 => B1_5_2U0_3_1Leaf
  | 0, 4, 0 => B1_5_2U0_4_0Leaf
  | 1, 1, 2 => B1_5_2U1_1_2Leaf
  | 1, 2, 1 => B1_5_2U1_2_1Leaf
  | 1, 3, 0 => B1_5_2U1_3_0Leaf
  | _, _, _ => (.exact 0)
lemma B1_5_2Leaves_sound (u : Shape) (hu : u ∈ below (shape 1 5 2)) :
    (B1_5_2Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 5 2) u) := by
  rw [B1_5_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_5_2U0_2_2Leaf_sound
  · exact B1_5_2U0_3_1Leaf_sound
  · exact B1_5_2U0_4_0Leaf_sound
  · exact B1_5_2U1_1_2Leaf_sound
  · exact B1_5_2U1_2_1Leaf_sound
  · exact B1_5_2U1_3_0Leaf_sound
def B1_5_2Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_5_2U0_2_2Mass
  | 0, 3, 1 => B1_5_2U0_3_1Mass
  | 0, 4, 0 => B1_5_2U0_4_0Mass
  | 1, 1, 2 => B1_5_2U1_1_2Mass
  | 1, 2, 1 => B1_5_2U1_2_1Mass
  | 1, 3, 0 => B1_5_2U1_3_0Mass
  | _, _, _ => (.exact 0)
lemma B1_5_2Masses_sound (u : Shape) (hu : u ∈ below (shape 1 5 2)) :
    (B1_5_2Masses u).Encloses ((fun u => (littleMass (shape 1 5 2) u : ℝ)) u) := by
  rw [B1_5_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_5_2U0_2_2Mass_sound
  · exact B1_5_2U0_3_1Mass_sound
  · exact B1_5_2U0_4_0Mass_sound
  · exact B1_5_2U1_1_2Mass_sound
  · exact B1_5_2U1_2_1Mass_sound
  · exact B1_5_2U1_3_0Mass_sound
def B1_5_2Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_5_2U0_2_2BinaryEntropy
  | 1, 1, 2 => B1_5_2U1_1_2BinaryEntropy
  | 1, 2, 1 => B1_5_2U1_2_1BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B1_5_2Binaries_sound (u : Shape) (hu : u ∈ (below (shape 1 5 2)).filter positive) :
    (B1_5_2Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 1 5 2) u)) u) := by
  have hl : (below (shape 1 5 2)).filter positive = [(shape 1 1 2), (shape 1 2 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B1_5_2U1_1_2BinaryEntropy_sound
  · exact B1_5_2U1_2_1BinaryEntropy_sound
def B1_5_2S2 : Ball := ⟨(3448608467743772816283012723469 / 100000000000000000000000000000000), (351540337 / 25000000000000000000000000000000)⟩
lemma B1_5_2S2_sound : B1_5_2S2.Encloses
    (((below (shape 1 5 2)).map fun u => (littleMass (shape 1 5 2) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 1 5 2) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 1 5 2))
    (fun u => .mul (B1_5_2Masses u) (B1_5_2Leaves u)) _
    (fun u hu => Ball.mul_sound (B1_5_2Masses_sound u hu) (B1_5_2Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
