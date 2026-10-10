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
def B3_2_3U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_2_3U0_1_3Leaf_sound : B3_2_3U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 2 3) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_2_3U0_1_3Mass : Ball := ⟨(3000961201670361542477883491 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B3_2_3U0_1_3Mass_sound : B3_2_3U0_1_3Mass.Encloses (littleMass (shape 3 2 3) (shape 0 1 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_2_3))
    (B3_2_3Law_sound (shape 0 1 3))) (by decide +kernel)
def B3_2_3U0_2_2D : Ball := .exact (20837 / 200000)
lemma B3_2_3U0_2_2D_sound : B3_2_3U0_2_2D.Encloses (binaryParameter (shape 3 2 3) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_2_3U0_2_2OneD : Ball := .exact (179163 / 200000)
lemma B3_2_3U0_2_2OneD_sound : B3_2_3U0_2_2OneD.Encloses (1 - (binaryParameter (shape 3 2 3) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 3 2 3) (shape 0 2 2) = (20837 / 200000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((179163 / 200000) : ℚ) using 1 <;> norm_num [B3_2_3U0_2_2OneD, Ball.exact]
def B3_2_3U0_2_2EDLogWitness : LogWitness := ⟨-4, 20837, 12500⟩
def B3_2_3U0_2_2EDLog : Ball := ⟨(-226158711395997353564112106926423 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B3_2_3U0_2_2EDLog_sound : B3_2_3U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 3 2 3) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U0_2_2D_sound) (w := B3_2_3U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U0_2_2ED : Ball := ⟨(23562345346791984281077019860129 / 100000000000000000000000000000000), (11031015953 / 100000000000000000000000000000000)⟩
lemma B3_2_3U0_2_2ED_sound : B3_2_3U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 2 3) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U0_2_2D_sound) B3_2_3U0_2_2EDLog_sound) (by decide +kernel)
def B3_2_3U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 179163, 100000⟩
def B3_2_3U0_2_2EOneDLog : Ball := ⟨(-11002136054002092463393093233409 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_2_3U0_2_2EOneDLog_sound : B3_2_3U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 2 3) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U0_2_2OneD_sound) (w := B3_2_3U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U0_2_2EOneD : Ball := ⟨(4927939254607942230047241907443 / 50000000000000000000000000000000), (18969620493 / 50000000000000000000000000000000)⟩
lemma B3_2_3U0_2_2EOneD_sound : B3_2_3U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 2 3) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U0_2_2OneD_sound) B3_2_3U0_2_2EOneDLog_sound) (by decide +kernel)
def B3_2_3U0_2_2BinaryEntropy : Ball := ⟨(10159944439167914736833733635741 / 25000000000000000000000000000000), (53382663321 / 100000000000000000000000000000000)⟩
lemma B3_2_3U0_2_2BinaryEntropy_sound : B3_2_3U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 2 3) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_2_3U0_2_2EOneD_sound B3_2_3U0_2_2ED_sound)
    (Ball.mul_sound B3_2_3U0_2_2D_sound logN2_sound)) (by decide +kernel)
def B3_2_3U0_2_2Leaf : Ball := ⟨(328991502462102384361930710537671 / 100000000000000000000000000000000), (167200386277 / 100000000000000000000000000000000)⟩
lemma B3_2_3U0_2_2Leaf_sound : B3_2_3U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 2 3) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B3_2_3U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_2_3U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
def B3_2_3U0_2_2Mass : Ball := ⟨(541968814941377438344242143929 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
lemma B3_2_3U0_2_2Mass_sound : B3_2_3U0_2_2Mass.Encloses (littleMass (shape 3 2 3) (shape 0 2 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_2_3))
    (B3_2_3Law_sound (shape 0 2 2))) (by decide +kernel)
def B3_2_3U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_2_3U1_0_3Leaf_sound : B3_2_3U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 2 3) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_2_3U1_0_3Mass : Ball := ⟨(539050071041767176960078266569 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
lemma B3_2_3U1_0_3Mass_sound : B3_2_3U1_0_3Mass.Encloses (littleMass (shape 3 2 3) (shape 1 0 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_2_3))
    (B3_2_3Law_sound (shape 1 0 3))) (by decide +kernel)
def B3_2_3U1_1_2D : Ball := .exact (947 / 200000)
lemma B3_2_3U1_1_2D_sound : B3_2_3U1_1_2D.Encloses (binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_2_3U1_1_2OneD : Ball := .exact (199053 / 200000)
lemma B3_2_3U1_1_2OneD_sound : B3_2_3U1_1_2OneD.Encloses (1 - (binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 3 2 3) (shape 1 1 2) = (947 / 200000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((199053 / 200000) : ℚ) using 1 <;> norm_num [B3_2_3U1_1_2OneD, Ball.exact]
def B3_2_3U1_1_2EDLogWitness : LogWitness := ⟨-8, 3788, 3125⟩
def B3_2_3U1_1_2EDLog : Ball := ⟨(-267638677617204774276902959196961 / 50000000000000000000000000000000), (95291206573 / 50000000000000000000000000000000)⟩
lemma B3_2_3U1_1_2EDLog_sound : B3_2_3U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U1_1_2D_sound) (w := B3_2_3U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U1_1_2ED : Ball := ⟨(506907655406985842480454204719 / 20000000000000000000000000000000), (902407727 / 100000000000000000000000000000000)⟩
lemma B3_2_3U1_1_2ED_sound : B3_2_3U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U1_1_2D_sound) B3_2_3U1_1_2EDLog_sound) (by decide +kernel)
def B3_2_3U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 199053, 100000⟩
def B3_2_3U1_1_2EOneDLog : Ball := ⟨(-474624562523299173208176196821 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_2_3U1_1_2EOneDLog_sound : B3_2_3U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U1_1_2OneD_sound) (w := B3_2_3U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U1_1_2EOneD : Ball := ⟨(472377215219751351623035482529 / 100000000000000000000000000000000), (10537778079 / 25000000000000000000000000000000)⟩
lemma B3_2_3U1_1_2EOneD_sound : B3_2_3U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U1_1_2OneD_sound) B3_2_3U1_1_2EOneDLog_sound) (by decide +kernel)
def B3_2_3U1_1_2BinaryEntropy : Ball := ⟨(3335120682249814668034365825217 / 100000000000000000000000000000000), (21627027547 / 50000000000000000000000000000000)⟩
lemma B3_2_3U1_1_2BinaryEntropy_sound : B3_2_3U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 2 3) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_2_3U1_1_2EOneD_sound B3_2_3U1_1_2ED_sound)
    (Ball.mul_sound B3_2_3U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B3_2_3U1_1_2Leaf : Ball := ⟨(501758615055128950613716142031 / 156250000000000000000000000000), (126754139523 / 100000000000000000000000000000000)⟩
lemma B3_2_3U1_1_2Leaf_sound : B3_2_3U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 2 3) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (399053 / 200000)).Encloses (2 - (binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 3 2 3) (shape 1 1 2) = (947 / 200000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((399053 / 200000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B3_2_3U1_1_2Mass : Ball := ⟨(14632618547294745801274531434457 / 100000000000000000000000000000000), (153 / 100000000000000000000000000000000)⟩
lemma B3_2_3U1_1_2Mass_sound : B3_2_3U1_1_2Mass.Encloses (littleMass (shape 3 2 3) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_2_3))
    (B3_2_3Law_sound (shape 1 1 2))) (by decide +kernel)
def B3_2_3U1_2_1D : Ball := .exact (38889 / 1000000)
lemma B3_2_3U1_2_1D_sound : B3_2_3U1_2_1D.Encloses (binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_2_3U1_2_1OneD : Ball := .exact (961111 / 1000000)
lemma B3_2_3U1_2_1OneD_sound : B3_2_3U1_2_1OneD.Encloses (1 - (binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 3 2 3) (shape 1 2 1) = (38889 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((961111 / 1000000) : ℚ) using 1 <;> norm_num [B3_2_3U1_2_1OneD, Ball.exact]
def B3_2_3U1_2_1EDLogWitness : LogWitness := ⟨-5, 38889, 31250⟩
def B3_2_3U1_2_1EDLog : Ball := ⟨(-40588048058701519414271962400259 / 12500000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B3_2_3U1_2_1EDLog_sound : B3_2_3U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U1_2_1D_sound) (w := B3_2_3U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U1_2_1ED : Ball := ⟨(12627428807638747108012978766269 / 100000000000000000000000000000000), (1235259911 / 25000000000000000000000000000000)⟩
lemma B3_2_3U1_2_1ED_sound : B3_2_3U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U1_2_1D_sound) B3_2_3U1_2_1EDLog_sound) (by decide +kernel)
def B3_2_3U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 961111, 500000⟩
def B3_2_3U1_2_1EOneDLog : Ball := ⟨(-1983268599968726397978668862597 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_2_3U1_2_1EOneDLog_sound : B3_2_3U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U1_2_1OneD_sound) (w := B3_2_3U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U1_2_1EOneD : Ball := ⟨(3812282534769085194175352818399 / 100000000000000000000000000000000), (5088079269 / 12500000000000000000000000000000)⟩
lemma B3_2_3U1_2_1EOneD_sound : B3_2_3U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U1_2_1OneD_sound) B3_2_3U1_2_1EOneDLog_sound) (by decide +kernel)
def B3_2_3U1_2_1BinaryEntropy : Ball := ⟨(9567645706443701807990502419601 / 50000000000000000000000000000000), (47292687011 / 100000000000000000000000000000000)⟩
lemma B3_2_3U1_2_1BinaryEntropy_sound : B3_2_3U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 2 3) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_2_3U1_2_1EOneD_sound B3_2_3U1_2_1ED_sound)
    (Ball.mul_sound B3_2_3U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B3_2_3U1_2_1Leaf : Ball := ⟨(315628639389155101973366898777513 / 100000000000000000000000000000000), (124584422277 / 100000000000000000000000000000000)⟩
lemma B3_2_3U1_2_1Leaf_sound : B3_2_3U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 2 3) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1961111 / 1000000)).Encloses (2 - (binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 3 2 3) (shape 1 2 1) = (38889 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1961111 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B3_2_3U1_2_1Mass : Ball := ⟨(3774266288822559599228366594839 / 50000000000000000000000000000000), (89 / 100000000000000000000000000000000)⟩
lemma B3_2_3U1_2_1Mass_sound : B3_2_3U1_2_1Mass.Encloses (littleMass (shape 3 2 3) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_2_3))
    (B3_2_3Law_sound (shape 1 2 1))) (by decide +kernel)
def B3_2_3U2_0_2D : Ball := .exact (22013 / 200000)
lemma B3_2_3U2_0_2D_sound : B3_2_3U2_0_2D.Encloses (binaryParameter (shape 3 2 3) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_2_3U2_0_2OneD : Ball := .exact (177987 / 200000)
lemma B3_2_3U2_0_2OneD_sound : B3_2_3U2_0_2OneD.Encloses (1 - (binaryParameter (shape 3 2 3) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 3 2 3) (shape 2 0 2) = (22013 / 200000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((177987 / 200000) : ℚ) using 1 <;> norm_num [B3_2_3U2_0_2OneD, Ball.exact]
def B3_2_3U2_0_2EDLogWitness : LogWitness := ⟨-4, 22013, 12500⟩
def B3_2_3U2_0_2EDLog : Ball := ⟨(-27583552232710530620549709460953 / 12500000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B3_2_3U2_0_2EDLog_sound : B3_2_3U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 3 2 3) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U2_0_2D_sound) (w := B3_2_3U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U2_0_2ED : Ball := ⟨(12143934705973138211003215087279 / 50000000000000000000000000000000), (11653585169 / 100000000000000000000000000000000)⟩
lemma B3_2_3U2_0_2ED_sound : B3_2_3U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 2 3) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U2_0_2D_sound) B3_2_3U2_0_2EDLog_sound) (by decide +kernel)
def B3_2_3U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 177987, 100000⟩
def B3_2_3U2_0_2EOneDLog : Ball := ⟨(-11660685263090779968348502269377 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_2_3U2_0_2EOneDLog_sound : B3_2_3U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 2 3) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U2_0_2OneD_sound) (w := B3_2_3U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U2_0_2EOneD : Ball := ⟨(5188625969804346635566112183549 / 50000000000000000000000000000000), (37690213299 / 100000000000000000000000000000000)⟩
lemma B3_2_3U2_0_2EOneD_sound : B3_2_3U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 2 3) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U2_0_2OneD_sound) B3_2_3U2_0_2EOneDLog_sound) (by decide +kernel)
def B3_2_3U2_0_2BinaryEntropy : Ball := ⟨(42294245794388007741239417784741 / 100000000000000000000000000000000), (6750654067 / 12500000000000000000000000000000)⟩
lemma B3_2_3U2_0_2BinaryEntropy_sound : B3_2_3U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 2 3) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_2_3U2_0_2EOneD_sound B3_2_3U2_0_2ED_sound)
    (Ball.mul_sound B3_2_3U2_0_2D_sound logN2_sound)) (by decide +kernel)
def B3_2_3U2_0_2Leaf : Ball := ⟨(3287532715147962311153047012527 / 1000000000000000000000000000000), (167075872433 / 100000000000000000000000000000000)⟩
lemma B3_2_3U2_0_2Leaf_sound : B3_2_3U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 2 3) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B3_2_3U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_2_3U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
def B3_2_3U2_0_2Mass : Ball := ⟨(3774266288822559599228366594839 / 50000000000000000000000000000000), (89 / 100000000000000000000000000000000)⟩
lemma B3_2_3U2_0_2Mass_sound : B3_2_3U2_0_2Mass.Encloses (littleMass (shape 3 2 3) (shape 2 0 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_2_3))
    (B3_2_3Law_sound (shape 2 0 2))) (by decide +kernel)
def B3_2_3U2_1_1D : Ball := .exact (21083 / 500000)
lemma B3_2_3U2_1_1D_sound : B3_2_3U2_1_1D.Encloses (binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_2_3U2_1_1OneD : Ball := .exact (478917 / 500000)
lemma B3_2_3U2_1_1OneD_sound : B3_2_3U2_1_1OneD.Encloses (1 - (binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 3 2 3) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((478917 / 500000) : ℚ) using 1 <;> norm_num [B3_2_3U2_1_1OneD, Ball.exact]
def B3_2_3U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B3_2_3U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B3_2_3U2_1_1EDLog_sound : B3_2_3U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U2_1_1D_sound) (w := B3_2_3U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
lemma B3_2_3U2_1_1ED_sound : B3_2_3U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U2_1_1D_sound) B3_2_3U2_1_1EDLog_sound) (by decide +kernel)
def B3_2_3U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B3_2_3U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_2_3U2_1_1EOneDLog_sound : B3_2_3U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U2_1_1OneD_sound) (w := B3_2_3U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
lemma B3_2_3U2_1_1EOneD_sound : B3_2_3U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U2_1_1OneD_sound) B3_2_3U2_1_1EOneDLog_sound) (by decide +kernel)
def B3_2_3U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
lemma B3_2_3U2_1_1BinaryEntropy_sound : B3_2_3U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 2 3) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_2_3U2_1_1EOneD_sound B3_2_3U2_1_1ED_sound)
    (Ball.mul_sound B3_2_3U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B3_2_3U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
lemma B3_2_3U2_1_1Leaf_sound : B3_2_3U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 2 3) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (978917 / 500000)).Encloses (2 - (binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 3 2 3) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((978917 / 500000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B3_2_3U2_1_1Mass : Ball := ⟨(14632618547294745801274531434457 / 100000000000000000000000000000000), (153 / 100000000000000000000000000000000)⟩
lemma B3_2_3U2_1_1Mass_sound : B3_2_3U2_1_1Mass.Encloses (littleMass (shape 3 2 3) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_2_3))
    (B3_2_3Law_sound (shape 2 1 1))) (by decide +kernel)
def B3_2_3U2_2_0D : Ball := .exact (25593 / 250000)
lemma B3_2_3U2_2_0D_sound : B3_2_3U2_2_0D.Encloses (binaryParameter (shape 3 2 3) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_2_3U2_2_0OneD : Ball := .exact (224407 / 250000)
lemma B3_2_3U2_2_0OneD_sound : B3_2_3U2_2_0OneD.Encloses (1 - (binaryParameter (shape 3 2 3) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 3 2 3) (shape 2 2 0) = (25593 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((224407 / 250000) : ℚ) using 1 <;> norm_num [B3_2_3U2_2_0OneD, Ball.exact]
def B3_2_3U2_2_0EDLogWitness : LogWitness := ⟨-4, 25593, 15625⟩
def B3_2_3U2_2_0EDLog : Ball := ⟨(-113957102063378952030784463086693 / 50000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B3_2_3U2_2_0EDLog_sound : B3_2_3U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 3 2 3) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U2_2_0D_sound) (w := B3_2_3U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U2_2_0ED : Ball := ⟨(11666016452432230077295467055111 / 50000000000000000000000000000000), (10839057111 / 100000000000000000000000000000000)⟩
lemma B3_2_3U2_2_0ED_sound : B3_2_3U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 2 3) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U2_2_0D_sound) B3_2_3U2_2_0EDLog_sound) (by decide +kernel)
def B3_2_3U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 224407, 125000⟩
def B3_2_3U2_2_0EOneDLog : Ball := ⟨(-5399977520216846740471713413351 / 50000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma B3_2_3U2_2_0EOneDLog_sound : B3_2_3U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 2 3) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U2_2_0OneD_sound) (w := B3_2_3U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_2_3U2_2_0EOneD : Ball := ⟨(9694342043034415411912286335599 / 100000000000000000000000000000000), (19008012261 / 50000000000000000000000000000000)⟩
lemma B3_2_3U2_2_0EOneD_sound : B3_2_3U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 2 3) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U2_2_0OneD_sound) B3_2_3U2_2_0EOneDLog_sound) (by decide +kernel)
def B3_2_3U2_2_0BinaryEntropy : Ball := ⟨(40122261264727147688069307164769 / 100000000000000000000000000000000), (26595352239 / 50000000000000000000000000000000)⟩
lemma B3_2_3U2_2_0BinaryEntropy_sound : B3_2_3U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 2 3) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_2_3U2_2_0EOneD_sound B3_2_3U2_2_0ED_sound)
    (Ball.mul_sound B3_2_3U2_2_0D_sound logN2_sound)) (by decide +kernel)
def B3_2_3U2_2_0Leaf : Ball := ⟨(41132196019650809737311914794403 / 12500000000000000000000000000000), (41809694511 / 25000000000000000000000000000000)⟩
lemma B3_2_3U2_2_0Leaf_sound : B3_2_3U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 2 3) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B3_2_3U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_2_3U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
def B3_2_3U2_2_0Mass : Ball := ⟨(539050071041767176960078266569 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
lemma B3_2_3U2_2_0Mass_sound : B3_2_3U2_2_0Mass.Encloses (littleMass (shape 3 2 3) (shape 2 2 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_2_3))
    (B3_2_3Law_sound (shape 2 2 0))) (by decide +kernel)
def B3_2_3U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_2_3U3_0_1Leaf_sound : B3_2_3U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 2 3) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_2_3U3_0_1Mass : Ball := ⟨(541968814941377438344242143929 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
lemma B3_2_3U3_0_1Mass_sound : B3_2_3U3_0_1Mass.Encloses (littleMass (shape 3 2 3) (shape 3 0 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_2_3))
    (B3_2_3Law_sound (shape 3 0 1))) (by decide +kernel)
def B3_2_3U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_2_3U3_1_0Leaf_sound : B3_2_3U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 2 3) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_2_3U3_1_0Mass : Ball := ⟨(3000961201670361542477883491 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B3_2_3U3_1_0Mass_sound : B3_2_3U3_1_0Mass.Encloses (littleMass (shape 3 2 3) (shape 3 1 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_2_3))
    (B3_2_3Law_sound (shape 3 1 0))) (by decide +kernel)
def B3_2_3Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B3_2_3U0_1_3Leaf
  | 0, 2, 2 => B3_2_3U0_2_2Leaf
  | 1, 0, 3 => B3_2_3U1_0_3Leaf
  | 1, 1, 2 => B3_2_3U1_1_2Leaf
  | 1, 2, 1 => B3_2_3U1_2_1Leaf
  | 2, 0, 2 => B3_2_3U2_0_2Leaf
  | 2, 1, 1 => B3_2_3U2_1_1Leaf
  | 2, 2, 0 => B3_2_3U2_2_0Leaf
  | 3, 0, 1 => B3_2_3U3_0_1Leaf
  | 3, 1, 0 => B3_2_3U3_1_0Leaf
  | _, _, _ => (.exact 0)
lemma B3_2_3Leaves_sound (u : Shape) (hu : u ∈ below (shape 3 2 3)) :
    (B3_2_3Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 2 3) u) := by
  rw [B3_2_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_2_3U0_1_3Leaf_sound
  · exact B3_2_3U0_2_2Leaf_sound
  · exact B3_2_3U1_0_3Leaf_sound
  · exact B3_2_3U1_1_2Leaf_sound
  · exact B3_2_3U1_2_1Leaf_sound
  · exact B3_2_3U2_0_2Leaf_sound
  · exact B3_2_3U2_1_1Leaf_sound
  · exact B3_2_3U2_2_0Leaf_sound
  · exact B3_2_3U3_0_1Leaf_sound
  · exact B3_2_3U3_1_0Leaf_sound
def B3_2_3Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B3_2_3U0_1_3Mass
  | 0, 2, 2 => B3_2_3U0_2_2Mass
  | 1, 0, 3 => B3_2_3U1_0_3Mass
  | 1, 1, 2 => B3_2_3U1_1_2Mass
  | 1, 2, 1 => B3_2_3U1_2_1Mass
  | 2, 0, 2 => B3_2_3U2_0_2Mass
  | 2, 1, 1 => B3_2_3U2_1_1Mass
  | 2, 2, 0 => B3_2_3U2_2_0Mass
  | 3, 0, 1 => B3_2_3U3_0_1Mass
  | 3, 1, 0 => B3_2_3U3_1_0Mass
  | _, _, _ => (.exact 0)
lemma B3_2_3Masses_sound (u : Shape) (hu : u ∈ below (shape 3 2 3)) :
    (B3_2_3Masses u).Encloses ((fun u => (littleMass (shape 3 2 3) u : ℝ)) u) := by
  rw [B3_2_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_2_3U0_1_3Mass_sound
  · exact B3_2_3U0_2_2Mass_sound
  · exact B3_2_3U1_0_3Mass_sound
  · exact B3_2_3U1_1_2Mass_sound
  · exact B3_2_3U1_2_1Mass_sound
  · exact B3_2_3U2_0_2Mass_sound
  · exact B3_2_3U2_1_1Mass_sound
  · exact B3_2_3U2_2_0Mass_sound
  · exact B3_2_3U3_0_1Mass_sound
  · exact B3_2_3U3_1_0Mass_sound
def B3_2_3Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B3_2_3U0_2_2BinaryEntropy
  | 1, 1, 2 => B3_2_3U1_1_2BinaryEntropy
  | 1, 2, 1 => B3_2_3U1_2_1BinaryEntropy
  | 2, 0, 2 => B3_2_3U2_0_2BinaryEntropy
  | 2, 1, 1 => B3_2_3U2_1_1BinaryEntropy
  | 2, 2, 0 => B3_2_3U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B3_2_3Binaries_sound (u : Shape) (hu : u ∈ (below (shape 3 2 3)).filter positive) :
    (B3_2_3Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 3 2 3) u)) u) := by
  have hl : (below (shape 3 2 3)).filter positive = [(shape 1 1 2), (shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact B3_2_3U1_1_2BinaryEntropy_sound
  · exact B3_2_3U1_2_1BinaryEntropy_sound
  · exact B3_2_3U2_1_1BinaryEntropy_sound
def B3_2_3S2 : Ball := ⟨(148129463261957605657082804649427 / 100000000000000000000000000000000), (61613453871 / 100000000000000000000000000000000)⟩
lemma B3_2_3S2_sound : B3_2_3S2.Encloses
    (((below (shape 3 2 3)).map fun u => (littleMass (shape 3 2 3) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 3 2 3) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 3 2 3))
    (fun u => .mul (B3_2_3Masses u) (B3_2_3Leaves u)) _
    (fun u hu => Ball.mul_sound (B3_2_3Masses_sound u hu) (B3_2_3Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
