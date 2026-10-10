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
def B1_3_4U0_0_4Leaf : Ball := ⟨0, 0⟩
lemma B1_3_4U0_0_4Leaf_sound : B1_3_4U0_0_4Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 3 4) (shape 0 0 4)) := by
  have hh : shapeMax (shape 0 0 4) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B1_3_4U0_0_4Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B1_3_4U0_0_4Mass : Ball := ⟨(11296930969545920829977701957 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B1_3_4U0_0_4Mass_sound : B1_3_4U0_0_4Mass.Encloses (littleMass (shape 1 3 4) (shape 0 0 4) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_3_4))
    (B1_3_4Law_sound (shape 0 0 4))) (by decide +kernel)
def B1_3_4U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_3_4U0_1_3Leaf_sound : B1_3_4U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 3 4) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simpa only [B1_3_4U0_1_3Leaf, logN10, AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true] using logN10_sound
def B1_3_4U0_1_3Mass : Ball := ⟨(1835521493311920037404366035991 / 50000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
lemma B1_3_4U0_1_3Mass_sound : B1_3_4U0_1_3Mass.Encloses (littleMass (shape 1 3 4) (shape 0 1 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_3_4))
    (B1_3_4Law_sound (shape 0 1 3))) (by decide +kernel)
def B1_3_4U0_2_2D : Ball := .exact (46483 / 500000)
lemma B1_3_4U0_2_2D_sound : B1_3_4U0_2_2D.Encloses (binaryParameter (shape 1 3 4) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_3_4U0_2_2OneD : Ball := .exact (453517 / 500000)
lemma B1_3_4U0_2_2OneD_sound : B1_3_4U0_2_2OneD.Encloses (1 - (binaryParameter (shape 1 3 4) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 1 3 4) (shape 0 2 2) = (46483 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((453517 / 500000) : ℚ) using 1 <;> norm_num [B1_3_4U0_2_2OneD, Ball.exact]
def B1_3_4U0_2_2EDLogWitness : LogWitness := ⟨-4, 46483, 31250⟩
def B1_3_4U0_2_2EDLog : Ball := ⟨(-59388036101788952339754245697507 / 25000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B1_3_4U0_2_2EDLog_sound : B1_3_4U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 1 3 4) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_3_4U0_2_2D_sound) (w := B1_3_4U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_3_4U0_2_2ED : Ball := ⟨(11042136328477823486435186411029 / 50000000000000000000000000000000), (9843158123 / 100000000000000000000000000000000)⟩
lemma B1_3_4U0_2_2ED_sound : B1_3_4U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 3 4) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_3_4U0_2_2D_sound) B1_3_4U0_2_2EDLog_sound) (by decide +kernel)
def B1_3_4U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 453517, 250000⟩
def B1_3_4U0_2_2EOneDLog : Ball := ⟨(-609845895945556733363202867553 / 6250000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B1_3_4U0_2_2EOneDLog_sound : B1_3_4U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 3 4) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_3_4U0_2_2OneD_sound) (w := B1_3_4U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_3_4U0_2_2EOneD : Ball := ⟨(8850415398129313697429749596289 / 100000000000000000000000000000000), (19207192059 / 50000000000000000000000000000000)⟩
lemma B1_3_4U0_2_2EOneD_sound : B1_3_4U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 3 4) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_3_4U0_2_2OneD_sound) B1_3_4U0_2_2EOneDLog_sound) (by decide +kernel)
def B1_3_4U0_2_2BinaryEntropy : Ball := ⟨(4672325016734818529228545097933 / 12500000000000000000000000000000), (5219480549 / 10000000000000000000000000000000)⟩
lemma B1_3_4U0_2_2BinaryEntropy_sound : B1_3_4U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 3 4) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_3_4U0_2_2EOneD_sound B1_3_4U0_2_2ED_sound)
    (Ball.mul_sound B1_3_4U0_2_2D_sound logN2_sound)) (by decide +kernel)
def B1_3_4U0_2_2Leaf : Ball := ⟨(65868316325445781613790663942627 / 20000000000000000000000000000000), (83718978921 / 50000000000000000000000000000000)⟩
lemma B1_3_4U0_2_2Leaf_sound : B1_3_4U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 3 4) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B1_3_4U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B1_3_4U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
def B1_3_4U0_2_2Mass : Ball := ⟨(13125128956309370446223832483411 / 50000000000000000000000000000000), (13 / 5000000000000000000000000000000)⟩
lemma B1_3_4U0_2_2Mass_sound : B1_3_4U0_2_2Mass.Encloses (littleMass (shape 1 3 4) (shape 0 2 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_3_4))
    (B1_3_4Law_sound (shape 0 2 2))) (by decide +kernel)
def B1_3_4U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_3_4U0_3_1Leaf_sound : B1_3_4U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 3 4) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simpa only [B1_3_4U0_3_1Leaf, logN10, AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true] using logN10_sound
def B1_3_4U0_3_1Mass : Ball := ⟨(160933812951551762605775804971 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
lemma B1_3_4U0_3_1Mass_sound : B1_3_4U0_3_1Mass.Encloses (littleMass (shape 1 3 4) (shape 0 3 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_3_4))
    (B1_3_4Law_sound (shape 0 3 1))) (by decide +kernel)
def B1_3_4U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_3_4U1_0_3Leaf_sound : B1_3_4U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 3 4) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simpa only [B1_3_4U1_0_3Leaf, logN10, AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true] using logN10_sound
def B1_3_4U1_0_3Mass : Ball := ⟨(160933812951551762605775804971 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
lemma B1_3_4U1_0_3Mass_sound : B1_3_4U1_0_3Mass.Encloses (littleMass (shape 1 3 4) (shape 1 0 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_3_4))
    (B1_3_4Law_sound (shape 1 0 3))) (by decide +kernel)
def B1_3_4U1_1_2D : Ball := .exact (301 / 250000)
lemma B1_3_4U1_1_2D_sound : B1_3_4U1_1_2D.Encloses (binaryParameter (shape 1 3 4) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_3_4U1_1_2OneD : Ball := .exact (249699 / 250000)
lemma B1_3_4U1_1_2OneD_sound : B1_3_4U1_1_2OneD.Encloses (1 - (binaryParameter (shape 1 3 4) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 1 3 4) (shape 1 1 2) = (301 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((249699 / 250000) : ℚ) using 1 <;> norm_num [B1_3_4U1_1_2OneD, Ball.exact]
def B1_3_4U1_1_2EDLogWitness : LogWitness := ⟨-10, 19264, 15625⟩
def B1_3_4U1_1_2EDLog : Ball := ⟨(-168052648302387693917382182971301 / 25000000000000000000000000000000), (7279189391 / 3125000000000000000000000000000)⟩
lemma B1_3_4U1_1_2EDLog_sound : B1_3_4U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 1 3 4) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_3_4U1_1_2D_sound) (w := B1_3_4U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_3_4U1_1_2ED : Ball := ⟨(80934155422429913390611259319 / 10000000000000000000000000000000), (28045261 / 10000000000000000000000000000000)⟩
lemma B1_3_4U1_1_2ED_sound : B1_3_4U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 3 4) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_3_4U1_1_2D_sound) B1_3_4U1_1_2EDLog_sound) (by decide +kernel)
def B1_3_4U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 249699, 125000⟩
def B1_3_4U1_1_2EOneDLog : Ball := ⟨(-1882383422351678894223498981 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B1_3_4U1_1_2EOneDLog_sound : B1_3_4U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 3 4) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_3_4U1_1_2OneD_sound) (w := B1_3_4U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_3_4U1_1_2EOneD : Ball := ⟨(120327490093514718261430648847 / 100000000000000000000000000000000), (2643790999 / 6250000000000000000000000000000)⟩
lemma B1_3_4U1_1_2EOneD_sound : B1_3_4U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 3 4) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_3_4U1_1_2OneD_sound) B1_3_4U1_1_2EOneDLog_sound) (by decide +kernel)
def B1_3_4U1_1_2BinaryEntropy : Ball := ⟨(101312396485723126742137796647 / 10000000000000000000000000000000), (21316049989 / 50000000000000000000000000000000)⟩
lemma B1_3_4U1_1_2BinaryEntropy_sound : B1_3_4U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 3 4) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_3_4U1_1_2EOneD_sound B1_3_4U1_1_2ED_sound)
    (Ball.mul_sound B1_3_4U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B1_3_4U1_1_2Leaf : Ball := ⟨(6433876123243260184700997177711 / 2000000000000000000000000000000), (7936153439 / 6250000000000000000000000000000)⟩
lemma B1_3_4U1_1_2Leaf_sound : B1_3_4U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 3 4) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (499699 / 250000)).Encloses (2 - (binaryParameter (shape 1 3 4) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 1 3 4) (shape 1 1 2) = (301 / 250000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((499699 / 250000) : ℚ) using 1; norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B1_3_4U1_1_2Mass : Ball := ⟨(13125128956309370446223832483411 / 50000000000000000000000000000000), (13 / 5000000000000000000000000000000)⟩
lemma B1_3_4U1_1_2Mass_sound : B1_3_4U1_1_2Mass.Encloses (littleMass (shape 1 3 4) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_3_4))
    (B1_3_4Law_sound (shape 1 1 2))) (by decide +kernel)
def B1_3_4U1_2_1D : Ball := .exact (10537 / 250000)
lemma B1_3_4U1_2_1D_sound : B1_3_4U1_2_1D.Encloses (binaryParameter (shape 1 3 4) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_3_4U1_2_1OneD : Ball := .exact (239463 / 250000)
lemma B1_3_4U1_2_1OneD_sound : B1_3_4U1_2_1OneD.Encloses (1 - (binaryParameter (shape 1 3 4) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 1 3 4) (shape 1 2 1) = (10537 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((239463 / 250000) : ℚ) using 1 <;> norm_num [B1_3_4U1_2_1OneD, Ball.exact]
def B1_3_4U1_2_1EDLogWitness : LogWitness := ⟨-5, 21074, 15625⟩
def B1_3_4U1_2_1EDLog : Ball := ⟨(-316656804524485588305492584261679 / 100000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B1_3_4U1_2_1EDLog_sound : B1_3_4U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 1 3 4) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_3_4U1_2_1D_sound) (w := B1_3_4U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_3_4U1_2_1ED : Ball := ⟨(13346450997098018575899901441461 / 100000000000000000000000000000000), (53551117 / 1000000000000000000000000000000)⟩
lemma B1_3_4U1_2_1ED_sound : B1_3_4U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 3 4) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_3_4U1_2_1D_sound) B1_3_4U1_2_1EDLog_sound) (by decide +kernel)
def B1_3_4U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 239463, 125000⟩
def B1_3_4U1_2_1EOneDLog : Ball := ⟨(-4306200146360205403795606812577 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B1_3_4U1_2_1EOneDLog_sound : B1_3_4U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 3 4) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_3_4U1_2_1OneD_sound) (w := B1_3_4U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_3_4U1_2_1EOneD : Ball := ⟨(4124702422591415466436429576641 / 100000000000000000000000000000000), (20283305067 / 50000000000000000000000000000000)⟩
lemma B1_3_4U1_2_1EOneD_sound : B1_3_4U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 3 4) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_3_4U1_2_1OneD_sound) B1_3_4U1_2_1EOneDLog_sound) (by decide +kernel)
def B1_3_4U1_2_1BinaryEntropy : Ball := ⟨(20392630156313491532468080158787 / 100000000000000000000000000000000), (11926689767 / 25000000000000000000000000000000)⟩
lemma B1_3_4U1_2_1BinaryEntropy_sound : B1_3_4U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 3 4) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_3_4U1_2_1EOneD_sound B1_3_4U1_2_1ED_sound)
    (Ball.mul_sound B1_3_4U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B1_3_4U1_2_1Leaf : Ball := ⟨(315104123573492828661284511435279 / 100000000000000000000000000000000), (124377386249 / 100000000000000000000000000000000)⟩
lemma B1_3_4U1_2_1Leaf_sound : B1_3_4U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 3 4) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (489463 / 250000)).Encloses (2 - (binaryParameter (shape 1 3 4) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 1 3 4) (shape 1 2 1) = (10537 / 250000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((489463 / 250000) : ℚ) using 1; norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B1_3_4U1_2_1Mass : Ball := ⟨(1835521493311920037404366035991 / 50000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
lemma B1_3_4U1_2_1Mass_sound : B1_3_4U1_2_1Mass.Encloses (littleMass (shape 1 3 4) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_3_4))
    (B1_3_4Law_sound (shape 1 2 1))) (by decide +kernel)
def B1_3_4U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_3_4U1_3_0Leaf_sound : B1_3_4U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 3 4) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simpa only [B1_3_4U1_3_0Leaf, logN10, AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true] using logN10_sound
def B1_3_4U1_3_0Mass : Ball := ⟨(11296930969545920829977701957 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B1_3_4U1_3_0Mass_sound : B1_3_4U1_3_0Mass.Encloses (littleMass (shape 1 3 4) (shape 1 3 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_3_4))
    (B1_3_4Law_sound (shape 1 3 0))) (by decide +kernel)
def B1_3_4Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_3_4U0_0_4Leaf
  | 0, 1, 3 => B1_3_4U0_1_3Leaf
  | 0, 2, 2 => B1_3_4U0_2_2Leaf
  | 0, 3, 1 => B1_3_4U0_3_1Leaf
  | 1, 0, 3 => B1_3_4U1_0_3Leaf
  | 1, 1, 2 => B1_3_4U1_1_2Leaf
  | 1, 2, 1 => B1_3_4U1_2_1Leaf
  | 1, 3, 0 => B1_3_4U1_3_0Leaf
  | _, _, _ => (.exact 0)
lemma B1_3_4Leaves_sound (u : Shape) (hu : u ∈ below (shape 1 3 4)) :
    (B1_3_4Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 3 4) u) := by
  rw [B1_3_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_3_4U0_0_4Leaf_sound
  · exact B1_3_4U0_1_3Leaf_sound
  · exact B1_3_4U0_2_2Leaf_sound
  · exact B1_3_4U0_3_1Leaf_sound
  · exact B1_3_4U1_0_3Leaf_sound
  · exact B1_3_4U1_1_2Leaf_sound
  · exact B1_3_4U1_2_1Leaf_sound
  · exact B1_3_4U1_3_0Leaf_sound
def B1_3_4Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_3_4U0_0_4Mass
  | 0, 1, 3 => B1_3_4U0_1_3Mass
  | 0, 2, 2 => B1_3_4U0_2_2Mass
  | 0, 3, 1 => B1_3_4U0_3_1Mass
  | 1, 0, 3 => B1_3_4U1_0_3Mass
  | 1, 1, 2 => B1_3_4U1_1_2Mass
  | 1, 2, 1 => B1_3_4U1_2_1Mass
  | 1, 3, 0 => B1_3_4U1_3_0Mass
  | _, _, _ => (.exact 0)
lemma B1_3_4Masses_sound (u : Shape) (hu : u ∈ below (shape 1 3 4)) :
    (B1_3_4Masses u).Encloses ((fun u => (littleMass (shape 1 3 4) u : ℝ)) u) := by
  rw [B1_3_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_3_4U0_0_4Mass_sound
  · exact B1_3_4U0_1_3Mass_sound
  · exact B1_3_4U0_2_2Mass_sound
  · exact B1_3_4U0_3_1Mass_sound
  · exact B1_3_4U1_0_3Mass_sound
  · exact B1_3_4U1_1_2Mass_sound
  · exact B1_3_4U1_2_1Mass_sound
  · exact B1_3_4U1_3_0Mass_sound
def B1_3_4Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_3_4U0_2_2BinaryEntropy
  | 1, 1, 2 => B1_3_4U1_1_2BinaryEntropy
  | 1, 2, 1 => B1_3_4U1_2_1BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B1_3_4Binaries_sound (u : Shape) (hu : u ∈ (below (shape 1 3 4)).filter positive) :
    (B1_3_4Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 1 3 4) u)) u) := by
  have hl : (below (shape 1 3 4)).filter positive = [(shape 1 1 2), (shape 1 2 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B1_3_4U1_1_2BinaryEntropy_sound
  · exact B1_3_4U1_2_1BinaryEntropy_sound
def B1_3_4S2 : Ball := ⟨(97325307607168493791537301136049 / 50000000000000000000000000000000), (4316662133 / 5000000000000000000000000000000)⟩
lemma B1_3_4S2_sound : B1_3_4S2.Encloses
    (((below (shape 1 3 4)).map fun u => (littleMass (shape 1 3 4) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 1 3 4) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 1 3 4))
    (fun u => .mul (B1_3_4Masses u) (B1_3_4Leaves u)) _
    (fun u hu => Ball.mul_sound (B1_3_4Masses_sound u hu) (B1_3_4Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
