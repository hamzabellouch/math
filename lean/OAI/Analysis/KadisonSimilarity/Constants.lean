import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace OAI

/-! The numerical constants fixed by the manuscript. -/

noncomputable section

namespace KadisonSimilarity

def rowConstant : ℝ := 4 * Real.sqrt 2
def cyclicConstant : ℝ := (1 + 4 * rowConstant) ^ 2
def cornerConstant : ℝ := 6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant)
def factorConstant : ℝ := max (max (3 * cornerConstant + 2) (1 + 2 * rowConstant)) 2
def universalConstant : ℝ := 3 * factorConstant + 2

theorem rowConstant_pos : 0 < rowConstant := by unfold rowConstant; positivity

theorem cyclicConstant_pos : 0 < cyclicConstant := by
  unfold cyclicConstant
  have := rowConstant_pos
  positivity

theorem one_le_cyclicConstant : 1 ≤ cyclicConstant := by
  unfold cyclicConstant
  nlinarith [rowConstant_pos]

theorem cornerConstant_pos : 0 < cornerConstant := by
  unfold cornerConstant
  have := cyclicConstant_pos
  positivity

theorem finiteFactorConstant_le : 3 * cornerConstant + 2 ≤ factorConstant :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem infiniteFactorConstant_le : 1 + 2 * rowConstant ≤ factorConstant :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem two_le_factorConstant : 2 ≤ factorConstant := le_max_right _ _

theorem factorConstant_pos : 0 < factorConstant := lt_of_lt_of_le (by norm_num) two_le_factorConstant

theorem universalConstant_pos : 0 < universalConstant := by
  unfold universalConstant
  linarith [factorConstant_pos]

end KadisonSimilarity

end

end OAI
