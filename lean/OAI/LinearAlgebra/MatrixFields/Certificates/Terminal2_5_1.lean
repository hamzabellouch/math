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
def B2_5_1U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_5_1U0_3_1Leaf_sound : B2_5_1U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 5 1) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_5_1U0_3_1Mass : Ball := ⟨(8730128534988305962655873559 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B2_5_1U0_3_1Mass_sound : B2_5_1U0_3_1Mass.Encloses (littleMass (shape 2 5 1) (shape 0 3 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_5_1))
    (B2_5_1Law_sound (shape 0 3 1))) (by decide +kernel)
def B2_5_1U0_4_0Leaf : Ball := ⟨0, 0⟩
lemma B2_5_1U0_4_0Leaf_sound : B2_5_1U0_4_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 5 1) (shape 0 4 0)) := by
  have hh : shapeMax (shape 0 4 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B2_5_1U0_4_0Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B2_5_1U0_4_0Mass : Ball := ⟨(348255140010022353957739057 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B2_5_1U0_4_0Mass_sound : B2_5_1U0_4_0Mass.Encloses (littleMass (shape 2 5 1) (shape 0 4 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_5_1))
    (B2_5_1Law_sound (shape 0 4 0))) (by decide +kernel)
def B2_5_1U1_2_1D : Ball := .exact (3587 / 1000000)
lemma B2_5_1U1_2_1D_sound : B2_5_1U1_2_1D.Encloses (binaryParameter (shape 2 5 1) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_5_1U1_2_1OneD : Ball := .exact (996413 / 1000000)
lemma B2_5_1U1_2_1OneD_sound : B2_5_1U1_2_1OneD.Encloses (1 - (binaryParameter (shape 2 5 1) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 2 5 1) (shape 1 2 1) = (3587 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((996413 / 1000000) : ℚ) using 1 <;> norm_num [B2_5_1U1_2_1OneD, Ball.exact]
def B2_5_1U1_2_1EDLogWitness : LogWitness := ⟨-9, 28696, 15625⟩
def B2_5_1U1_2_1EDLog : Ball := ⟨(-563043908043199152811645612664621 / 100000000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
lemma B2_5_1U1_2_1EDLog_sound : B2_5_1U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 2 5 1) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_5_1U1_2_1D_sound) (w := B2_5_1U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_5_1U1_2_1ED : Ball := ⟨(504909624537738840283843203157 / 25000000000000000000000000000000), (189894199 / 25000000000000000000000000000000)⟩
lemma B2_5_1U1_2_1ED_sound : B2_5_1U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 5 1) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_5_1U1_2_1D_sound) B2_5_1U1_2_1EDLog_sound) (by decide +kernel)
def B2_5_1U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 996413, 500000⟩
def B2_5_1U1_2_1EOneDLog : Ball := ⟨(-17967243550669688953494441141 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_5_1U1_2_1EOneDLog_sound : B2_5_1U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 5 1) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_5_1U1_2_1OneD_sound) (w := B2_5_1U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_5_1U1_2_1EOneD : Ball := ⟨(358055900961068735584365131613 / 100000000000000000000000000000000), (5274966501 / 12500000000000000000000000000000)⟩
lemma B2_5_1U1_2_1EOneD_sound : B2_5_1U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 5 1) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_5_1U1_2_1OneD_sound) B2_5_1U1_2_1EOneDLog_sound) (by decide +kernel)
def B2_5_1U1_2_1BinaryEntropy : Ball := ⟨(2626326292778876479207699037713 / 100000000000000000000000000000000), (10777806041 / 25000000000000000000000000000000)⟩
lemma B2_5_1U1_2_1BinaryEntropy_sound : B2_5_1U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 5 1) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_5_1U1_2_1EOneD_sound B2_5_1U1_2_1ED_sound)
    (Ball.mul_sound B2_5_1U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B2_5_1U1_2_1Leaf : Ball := ⟨(321310277107629963115782498027451 / 100000000000000000000000000000000), (6341353453 / 5000000000000000000000000000000)⟩
lemma B2_5_1U1_2_1Leaf_sound : B2_5_1U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 5 1) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1996413 / 1000000)).Encloses (2 - (binaryParameter (shape 2 5 1) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 2 5 1) (shape 1 2 1) = (3587 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1996413 / 1000000) : ℚ) using 1; norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_5_1U1_2_1Mass : Ball := ⟨(30948584829331435076273891283 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma B2_5_1U1_2_1Mass_sound : B2_5_1U1_2_1Mass.Encloses (littleMass (shape 2 5 1) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_5_1))
    (B2_5_1Law_sound (shape 1 2 1))) (by decide +kernel)
def B2_5_1U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_5_1U1_3_0Leaf_sound : B2_5_1U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 5 1) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_5_1U1_3_0Mass : Ball := ⟨(30948584829331435076273891283 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma B2_5_1U1_3_0Mass_sound : B2_5_1U1_3_0Mass.Encloses (littleMass (shape 2 5 1) (shape 1 3 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_5_1))
    (B2_5_1Law_sound (shape 1 3 0))) (by decide +kernel)
def B2_5_1U2_1_1D : Ball := .exact (21083 / 500000)
lemma B2_5_1U2_1_1D_sound : B2_5_1U2_1_1D.Encloses (binaryParameter (shape 2 5 1) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_5_1U2_1_1OneD : Ball := .exact (478917 / 500000)
lemma B2_5_1U2_1_1OneD_sound : B2_5_1U2_1_1OneD.Encloses (1 - (binaryParameter (shape 2 5 1) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 2 5 1) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((478917 / 500000) : ℚ) using 1 <;> norm_num [B2_5_1U2_1_1OneD, Ball.exact]
def B2_5_1U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B2_5_1U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B2_5_1U2_1_1EDLog_sound : B2_5_1U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 2 5 1) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_5_1U2_1_1D_sound) (w := B2_5_1U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_5_1U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
lemma B2_5_1U2_1_1ED_sound : B2_5_1U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 5 1) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_5_1U2_1_1D_sound) B2_5_1U2_1_1EDLog_sound) (by decide +kernel)
def B2_5_1U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B2_5_1U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_5_1U2_1_1EOneDLog_sound : B2_5_1U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 5 1) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_5_1U2_1_1OneD_sound) (w := B2_5_1U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_5_1U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
lemma B2_5_1U2_1_1EOneD_sound : B2_5_1U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 5 1) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_5_1U2_1_1OneD_sound) B2_5_1U2_1_1EOneDLog_sound) (by decide +kernel)
def B2_5_1U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
lemma B2_5_1U2_1_1BinaryEntropy_sound : B2_5_1U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 5 1) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_5_1U2_1_1EOneD_sound B2_5_1U2_1_1ED_sound)
    (Ball.mul_sound B2_5_1U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B2_5_1U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
lemma B2_5_1U2_1_1Leaf_sound : B2_5_1U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 5 1) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (978917 / 500000)).Encloses (2 - (binaryParameter (shape 2 5 1) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 2 5 1) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((978917 / 500000) : ℚ) using 1; norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_5_1U2_1_1Mass : Ball := ⟨(348255140010022353957739057 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B2_5_1U2_1_1Mass_sound : B2_5_1U2_1_1Mass.Encloses (littleMass (shape 2 5 1) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_5_1))
    (B2_5_1Law_sound (shape 2 1 1))) (by decide +kernel)
def B2_5_1U2_2_0D : Ball := .exact (55043 / 500000)
lemma B2_5_1U2_2_0D_sound : B2_5_1U2_2_0D.Encloses (binaryParameter (shape 2 5 1) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_5_1U2_2_0OneD : Ball := .exact (444957 / 500000)
lemma B2_5_1U2_2_0OneD_sound : B2_5_1U2_2_0OneD.Encloses (1 - (binaryParameter (shape 2 5 1) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 2 5 1) (shape 2 2 0) = (55043 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((444957 / 500000) : ℚ) using 1 <;> norm_num [B2_5_1U2_2_0OneD, Ball.exact]
def B2_5_1U2_2_0EDLogWitness : LogWitness := ⟨-4, 55043, 31250⟩
def B2_5_1U2_2_0EDLog : Ball := ⟨(-22064934004685379356673449299827 / 10000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B2_5_1U2_2_0EDLog_sound : B2_5_1U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 2 5 1) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_5_1U2_2_0D_sound) (w := B2_5_1U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_5_1U2_2_0ED : Ball := ⟨(1518150203024871669911720837263 / 6250000000000000000000000000000), (11655808631 / 100000000000000000000000000000000)⟩
lemma B2_5_1U2_2_0ED_sound : B2_5_1U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 5 1) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_5_1U2_2_0D_sound) B2_5_1U2_2_0EDLog_sound) (by decide +kernel)
def B2_5_1U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 444957, 250000⟩
def B2_5_1U2_2_0EOneDLog : Ball := ⟨(-583152250691689478453229215219 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_5_1U2_2_0EOneDLog_sound : B2_5_1U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 5 1) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_5_1U2_2_0OneD_sound) (w := B2_5_1U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_5_1U2_2_0EOneD : Ball := ⟨(1297388380055110376320567559581 / 12500000000000000000000000000000), (7537864783 / 20000000000000000000000000000000)⟩
lemma B2_5_1U2_2_0EOneD_sound : B2_5_1U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 5 1) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_5_1U2_2_0OneD_sound) B2_5_1U2_2_0EOneDLog_sound) (by decide +kernel)
def B2_5_1U2_2_0BinaryEntropy : Ball := ⟨(8460018068150208732480522660599 / 20000000000000000000000000000000), (54007455999 / 100000000000000000000000000000000)⟩
lemma B2_5_1U2_2_0BinaryEntropy_sound : B2_5_1U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 5 1) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_5_1U2_2_0EOneD_sound B2_5_1U2_2_0ED_sound)
    (Ball.mul_sound B2_5_1U2_2_0D_sound logN2_sound)) (by decide +kernel)
def B2_5_1U2_2_0Leaf : Ball := ⟨(328752356421927043814894573583359 / 100000000000000000000000000000000), (83537713871 / 50000000000000000000000000000000)⟩
lemma B2_5_1U2_2_0Leaf_sound : B2_5_1U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 5 1) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B2_5_1U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_5_1U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
def B2_5_1U2_2_0Mass : Ball := ⟨(8730128534988305962655873559 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B2_5_1U2_2_0Mass_sound : B2_5_1U2_2_0Mass.Encloses (littleMass (shape 2 5 1) (shape 2 2 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_5_1))
    (B2_5_1Law_sound (shape 2 2 0))) (by decide +kernel)
def B2_5_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B2_5_1U0_3_1Leaf
  | 0, 4, 0 => B2_5_1U0_4_0Leaf
  | 1, 2, 1 => B2_5_1U1_2_1Leaf
  | 1, 3, 0 => B2_5_1U1_3_0Leaf
  | 2, 1, 1 => B2_5_1U2_1_1Leaf
  | 2, 2, 0 => B2_5_1U2_2_0Leaf
  | _, _, _ => (.exact 0)
lemma B2_5_1Leaves_sound (u : Shape) (hu : u ∈ below (shape 2 5 1)) :
    (B2_5_1Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 5 1) u) := by
  rw [B2_5_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_5_1U0_3_1Leaf_sound
  · exact B2_5_1U0_4_0Leaf_sound
  · exact B2_5_1U1_2_1Leaf_sound
  · exact B2_5_1U1_3_0Leaf_sound
  · exact B2_5_1U2_1_1Leaf_sound
  · exact B2_5_1U2_2_0Leaf_sound
def B2_5_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B2_5_1U0_3_1Mass
  | 0, 4, 0 => B2_5_1U0_4_0Mass
  | 1, 2, 1 => B2_5_1U1_2_1Mass
  | 1, 3, 0 => B2_5_1U1_3_0Mass
  | 2, 1, 1 => B2_5_1U2_1_1Mass
  | 2, 2, 0 => B2_5_1U2_2_0Mass
  | _, _, _ => (.exact 0)
lemma B2_5_1Masses_sound (u : Shape) (hu : u ∈ below (shape 2 5 1)) :
    (B2_5_1Masses u).Encloses ((fun u => (littleMass (shape 2 5 1) u : ℝ)) u) := by
  rw [B2_5_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_5_1U0_3_1Mass_sound
  · exact B2_5_1U0_4_0Mass_sound
  · exact B2_5_1U1_2_1Mass_sound
  · exact B2_5_1U1_3_0Mass_sound
  · exact B2_5_1U2_1_1Mass_sound
  · exact B2_5_1U2_2_0Mass_sound
def B2_5_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B2_5_1U1_2_1BinaryEntropy
  | 2, 1, 1 => B2_5_1U2_1_1BinaryEntropy
  | 2, 2, 0 => B2_5_1U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B2_5_1Binaries_sound (u : Shape) (hu : u ∈ (below (shape 2 5 1)).filter positive) :
    (B2_5_1Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 2 5 1) u)) u) := by
  have hl : (below (shape 2 5 1)).filter positive = [(shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B2_5_1U1_2_1BinaryEntropy_sound
  · exact B2_5_1U2_1_1BinaryEntropy_sound
def B2_5_1S2 : Ball := ⟨(16906386274561049158059689213 / 3125000000000000000000000000000), (220586351 / 100000000000000000000000000000000)⟩
lemma B2_5_1S2_sound : B2_5_1S2.Encloses
    (((below (shape 2 5 1)).map fun u => (littleMass (shape 2 5 1) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 2 5 1) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 2 5 1))
    (fun u => .mul (B2_5_1Masses u) (B2_5_1Leaves u)) _
    (fun u hu => Ball.mul_sound (B2_5_1Masses_sound u hu) (B2_5_1Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
