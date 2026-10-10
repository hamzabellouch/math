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
def B1_4_3U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_4_3U0_1_3Leaf_sound : B1_4_3U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B1_4_3U0_1_3Mass : Ball := ⟨(181419853805933728200300858261 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma B1_4_3U0_1_3Mass_sound : B1_4_3U0_1_3Mass.Encloses (littleMass (shape 1 4 3) (shape 0 1 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_4_3))
    (B1_4_3Law_sound (shape 0 1 3))) (by decide +kernel)
def B1_4_3U0_2_2D : Ball := .exact (23901 / 250000)
lemma B1_4_3U0_2_2D_sound : B1_4_3U0_2_2D.Encloses (binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_4_3U0_2_2OneD : Ball := .exact (226099 / 250000)
lemma B1_4_3U0_2_2OneD_sound : B1_4_3U0_2_2OneD.Encloses (1 - (binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 1 4 3) (shape 0 2 2) = (23901 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((226099 / 250000) : ℚ) using 1 <;> norm_num [B1_4_3U0_2_2OneD, Ball.exact]
def B1_4_3U0_2_2EDLogWitness : LogWitness := ⟨-4, 23901, 15625⟩
def B1_4_3U0_2_2EDLog : Ball := ⟨(-234754061879590774959727984514419 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma B1_4_3U0_2_2EDLog_sound : B1_4_3U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_4_3U0_2_2D_sound) (w := B1_4_3U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_4_3U0_2_2ED : Ball := ⟨(22443427331936396449249834231517 / 100000000000000000000000000000000), (5061233619 / 50000000000000000000000000000000)⟩
lemma B1_4_3U0_2_2ED_sound : B1_4_3U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_4_3U0_2_2D_sound) B1_4_3U0_2_2EDLog_sound) (by decide +kernel)
def B1_4_3U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 226099, 125000⟩
def B1_4_3U0_2_2EOneDLog : Ball := ⟨(-2512199035246581498367078978841 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B1_4_3U0_2_2EOneDLog_sound : B1_4_3U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_4_3U0_2_2OneD_sound) (w := B1_4_3U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_4_3U0_2_2EOneD : Ball := ⟨(568005689670216830199298190037 / 6250000000000000000000000000000), (4787832559 / 12500000000000000000000000000000)⟩
lemma B1_4_3U0_2_2EOneD_sound : B1_4_3U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_4_3U0_2_2OneD_sound) B1_4_3U0_2_2EOneDLog_sound) (by decide +kernel)
def B1_4_3U0_2_2BinaryEntropy : Ball := ⟨(38158282671685166868591109420493 / 100000000000000000000000000000000), (10494822921 / 20000000000000000000000000000000)⟩
lemma B1_4_3U0_2_2BinaryEntropy_sound : B1_4_3U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 4 3) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_4_3U0_2_2EOneD_sound B1_4_3U0_2_2ED_sound)
    (Ball.mul_sound B1_4_3U0_2_2D_sound logN2_sound)) (by decide +kernel)
def B1_4_3U0_2_2Leaf : Ball := ⟨(6585442494448705906921534158549 / 2000000000000000000000000000000), (8369104801 / 5000000000000000000000000000000)⟩
lemma B1_4_3U0_2_2Leaf_sound : B1_4_3U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B1_4_3U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B1_4_3U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
def B1_4_3U0_2_2Mass : Ball := ⟨(12008393707958752871067573302183 / 100000000000000000000000000000000), (27 / 20000000000000000000000000000000)⟩
lemma B1_4_3U0_2_2Mass_sound : B1_4_3U0_2_2Mass.Encloses (littleMass (shape 1 4 3) (shape 0 2 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_4_3))
    (B1_4_3Law_sound (shape 0 2 2))) (by decide +kernel)
def B1_4_3U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_4_3U0_3_1Leaf_sound : B1_4_3U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B1_4_3U0_3_1Mass : Ball := ⟨(1880816292854954103757064512223 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
lemma B1_4_3U0_3_1Mass_sound : B1_4_3U0_3_1Mass.Encloses (littleMass (shape 1 4 3) (shape 0 3 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_4_3))
    (B1_4_3Law_sound (shape 0 3 1))) (by decide +kernel)
def B1_4_3U0_4_0Leaf : Ball := ⟨0, 0⟩
lemma B1_4_3U0_4_0Leaf_sound : B1_4_3U0_4_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 0 4 0)) := by
  have hh : shapeMax (shape 0 4 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B1_4_3U0_4_0Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B1_4_3U0_4_0Mass : Ball := ⟨(477318587058984464774530633 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_4_3U0_4_0Mass_sound : B1_4_3U0_4_0Mass.Encloses (littleMass (shape 1 4 3) (shape 0 4 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_4_3))
    (B1_4_3Law_sound (shape 0 4 0))) (by decide +kernel)
def B1_4_3U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_4_3U1_0_3Leaf_sound : B1_4_3U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B1_4_3U1_0_3Mass : Ball := ⟨(477318587058984464774530633 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_4_3U1_0_3Mass_sound : B1_4_3U1_0_3Mass.Encloses (littleMass (shape 1 4 3) (shape 1 0 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_4_3))
    (B1_4_3Law_sound (shape 1 0 3))) (by decide +kernel)
def B1_4_3U1_1_2D : Ball := .exact (41743 / 1000000)
lemma B1_4_3U1_1_2D_sound : B1_4_3U1_1_2D.Encloses (binaryParameter (shape 1 4 3) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_4_3U1_1_2OneD : Ball := .exact (958257 / 1000000)
lemma B1_4_3U1_1_2OneD_sound : B1_4_3U1_1_2OneD.Encloses (1 - (binaryParameter (shape 1 4 3) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 1 4 3) (shape 1 1 2) = (41743 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((958257 / 1000000) : ℚ) using 1 <;> norm_num [B1_4_3U1_1_2OneD, Ball.exact]
def B1_4_3U1_1_2EDLogWitness : LogWitness := ⟨-5, 41743, 31250⟩
def B1_4_3U1_1_2EDLog : Ball := ⟨(-317622350641322343593845801674799 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B1_4_3U1_1_2EDLog_sound : B1_4_3U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 1 4 3) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_4_3U1_1_2D_sound) (w := B1_4_3U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_4_3U1_1_2ED : Ball := ⟨(13258509782820718588637905299311 / 100000000000000000000000000000000), (5303654449 / 100000000000000000000000000000000)⟩
lemma B1_4_3U1_1_2ED_sound : B1_4_3U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 4 3) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_4_3U1_1_2D_sound) B1_4_3U1_1_2EDLog_sound) (by decide +kernel)
def B1_4_3U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 958257, 500000⟩
def B1_4_3U1_1_2EOneDLog : Ball := ⟨(-4263926976511183716334593201789 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B1_4_3U1_1_2EOneDLog_sound : B1_4_3U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 4 3) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_4_3U1_1_2OneD_sound) (w := B1_4_3U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_4_3U1_1_2EOneD : Ball := ⟨(4085937872730677374463638277767 / 100000000000000000000000000000000), (40583762551 / 100000000000000000000000000000000)⟩
lemma B1_4_3U1_1_2EOneD_sound : B1_4_3U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 4 3) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_4_3U1_1_2OneD_sound) B1_4_3U1_1_2EOneDLog_sound) (by decide +kernel)
def B1_4_3U1_1_2BinaryEntropy : Ball := ⟨(10118925965681387834100947412289 / 50000000000000000000000000000000), (47655301817 / 100000000000000000000000000000000)⟩
lemma B1_4_3U1_1_2BinaryEntropy_sound : B1_4_3U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 4 3) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_4_3U1_1_2EOneD_sound B1_4_3U1_1_2ED_sound)
    (Ball.mul_sound B1_4_3U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B1_4_3U1_1_2Leaf : Ball := ⟨(39396163226118301215806980271601 / 12500000000000000000000000000000), (995224919 / 800000000000000000000000000000)⟩
lemma B1_4_3U1_1_2Leaf_sound : B1_4_3U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1958257 / 1000000)).Encloses (2 - (binaryParameter (shape 1 4 3) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 1 4 3) (shape 1 1 2) = (41743 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1958257 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B1_4_3U1_1_2Mass : Ball := ⟨(1880816292854954103757064512223 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
lemma B1_4_3U1_1_2Mass_sound : B1_4_3U1_1_2Mass.Encloses (littleMass (shape 1 4 3) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_4_3))
    (B1_4_3Law_sound (shape 1 1 2))) (by decide +kernel)
def B1_4_3U1_2_1D : Ball := .exact (3057 / 1000000)
lemma B1_4_3U1_2_1D_sound : B1_4_3U1_2_1D.Encloses (binaryParameter (shape 1 4 3) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_4_3U1_2_1OneD : Ball := .exact (996943 / 1000000)
lemma B1_4_3U1_2_1OneD_sound : B1_4_3U1_2_1OneD.Encloses (1 - (binaryParameter (shape 1 4 3) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 1 4 3) (shape 1 2 1) = (3057 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((996943 / 1000000) : ℚ) using 1 <;> norm_num [B1_4_3U1_2_1OneD, Ball.exact]
def B1_4_3U1_2_1EDLogWitness : LogWitness := ⟨-9, 24456, 15625⟩
def B1_4_3U1_2_1EDLog : Ball := ⟨(-579032123607343959922323580543109 / 100000000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
lemma B1_4_3U1_2_1EDLog_sound : B1_4_3U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 1 4 3) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_4_3U1_2_1D_sound) (w := B1_4_3U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_4_3U1_2_1ED : Ball := ⟨(44252530046691262137063579643 / 2500000000000000000000000000000), (647344931 / 100000000000000000000000000000000)⟩
lemma B1_4_3U1_2_1ED_sound : B1_4_3U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 4 3) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_4_3U1_2_1D_sound) B1_4_3U1_2_1EDLog_sound) (by decide +kernel)
def B1_4_3U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 996943, 500000⟩
def B1_4_3U1_2_1EOneDLog : Ball := ⟨(-76542054229892072811856966359 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B1_4_3U1_2_1EOneDLog_sound : B1_4_3U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 4 3) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_4_3U1_2_1OneD_sound) (w := B1_4_3U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_4_3U1_2_1EOneD : Ball := ⟨(305232260680445170981084478451 / 100000000000000000000000000000000), (42222178381 / 100000000000000000000000000000000)⟩
lemma B1_4_3U1_2_1EOneD_sound : B1_4_3U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 4 3) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_4_3U1_2_1OneD_sound) B1_4_3U1_2_1EOneDLog_sound) (by decide +kernel)
def B1_4_3U1_2_1BinaryEntropy : Ball := ⟨(1143614277822635468776237732663 / 50000000000000000000000000000000), (42998992299 / 100000000000000000000000000000000)⟩
lemma B1_4_3U1_2_1BinaryEntropy_sound : B1_4_3U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 4 3) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_4_3U1_2_1EOneD_sound B1_4_3U1_2_1ED_sound)
    (Ball.mul_sound B1_4_3U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B1_4_3U1_2_1Leaf : Ball := ⟨(321395577316988970435636338251871 / 100000000000000000000000000000000), (6343036931 / 5000000000000000000000000000000)⟩
lemma B1_4_3U1_2_1Leaf_sound : B1_4_3U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1996943 / 1000000)).Encloses (2 - (binaryParameter (shape 1 4 3) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 1 4 3) (shape 1 2 1) = (3057 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1996943 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B1_4_3U1_2_1Mass : Ball := ⟨(12008393707958752871067573302183 / 100000000000000000000000000000000), (27 / 20000000000000000000000000000000)⟩
lemma B1_4_3U1_2_1Mass_sound : B1_4_3U1_2_1Mass.Encloses (littleMass (shape 1 4 3) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_4_3))
    (B1_4_3Law_sound (shape 1 2 1))) (by decide +kernel)
def B1_4_3U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_4_3U1_3_0Leaf_sound : B1_4_3U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B1_4_3U1_3_0Mass : Ball := ⟨(181419853805933728200300858261 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma B1_4_3U1_3_0Mass_sound : B1_4_3U1_3_0Mass.Encloses (littleMass (shape 1 4 3) (shape 1 3 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_4_3))
    (B1_4_3Law_sound (shape 1 3 0))) (by decide +kernel)
def B1_4_3Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B1_4_3U0_1_3Leaf
  | 0, 2, 2 => B1_4_3U0_2_2Leaf
  | 0, 3, 1 => B1_4_3U0_3_1Leaf
  | 0, 4, 0 => B1_4_3U0_4_0Leaf
  | 1, 0, 3 => B1_4_3U1_0_3Leaf
  | 1, 1, 2 => B1_4_3U1_1_2Leaf
  | 1, 2, 1 => B1_4_3U1_2_1Leaf
  | 1, 3, 0 => B1_4_3U1_3_0Leaf
  | _, _, _ => (.exact 0)
lemma B1_4_3Leaves_sound (u : Shape) (hu : u ∈ below (shape 1 4 3)) :
    (B1_4_3Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) u) := by
  rw [B1_4_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_4_3U0_1_3Leaf_sound
  · exact B1_4_3U0_2_2Leaf_sound
  · exact B1_4_3U0_3_1Leaf_sound
  · exact B1_4_3U0_4_0Leaf_sound
  · exact B1_4_3U1_0_3Leaf_sound
  · exact B1_4_3U1_1_2Leaf_sound
  · exact B1_4_3U1_2_1Leaf_sound
  · exact B1_4_3U1_3_0Leaf_sound
def B1_4_3Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B1_4_3U0_1_3Mass
  | 0, 2, 2 => B1_4_3U0_2_2Mass
  | 0, 3, 1 => B1_4_3U0_3_1Mass
  | 0, 4, 0 => B1_4_3U0_4_0Mass
  | 1, 0, 3 => B1_4_3U1_0_3Mass
  | 1, 1, 2 => B1_4_3U1_1_2Mass
  | 1, 2, 1 => B1_4_3U1_2_1Mass
  | 1, 3, 0 => B1_4_3U1_3_0Mass
  | _, _, _ => (.exact 0)
lemma B1_4_3Masses_sound (u : Shape) (hu : u ∈ below (shape 1 4 3)) :
    (B1_4_3Masses u).Encloses ((fun u => (littleMass (shape 1 4 3) u : ℝ)) u) := by
  rw [B1_4_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_4_3U0_1_3Mass_sound
  · exact B1_4_3U0_2_2Mass_sound
  · exact B1_4_3U0_3_1Mass_sound
  · exact B1_4_3U0_4_0Mass_sound
  · exact B1_4_3U1_0_3Mass_sound
  · exact B1_4_3U1_1_2Mass_sound
  · exact B1_4_3U1_2_1Mass_sound
  · exact B1_4_3U1_3_0Mass_sound
def B1_4_3Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_4_3U0_2_2BinaryEntropy
  | 1, 1, 2 => B1_4_3U1_1_2BinaryEntropy
  | 1, 2, 1 => B1_4_3U1_2_1BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B1_4_3Binaries_sound (u : Shape) (hu : u ∈ (below (shape 1 4 3)).filter positive) :
    (B1_4_3Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 1 4 3) u)) u) := by
  have hl : (below (shape 1 4 3)).filter positive = [(shape 1 1 2), (shape 1 2 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B1_4_3U1_1_2BinaryEntropy_sound
  · exact B1_4_3U1_2_1BinaryEntropy_sound
def B1_4_3S2 : Ball := ⟨(45043077270396458956602823687649 / 50000000000000000000000000000000), (4986188371 / 12500000000000000000000000000000)⟩
lemma B1_4_3S2_sound : B1_4_3S2.Encloses
    (((below (shape 1 4 3)).map fun u => (littleMass (shape 1 4 3) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 1 4 3) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 1 4 3))
    (fun u => .mul (B1_4_3Masses u) (B1_4_3Leaves u)) _
    (fun u hu => Ball.mul_sound (B1_4_3Masses_sound u hu) (B1_4_3Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
