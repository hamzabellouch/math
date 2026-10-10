import OAI.Probability.RadialTransition.InitialSlopes

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma phaseWindow_coords {x : Parameter} {r : ℝ} (hx : x ∈ phaseWindow r) :
    |x 0-1| ≤ r ∧ |x 1+3/4| ≤ r := by
  have hn : ‖x-phaseCenter‖ ≤ r := Metric.mem_closedBall.mp hx
  constructor
  · exact (parameter_coord_abs_le (x-phaseCenter) 0).trans hn
  · have hh := (parameter_coord_abs_le (x-phaseCenter) 1).trans hn
    change |x 1-(-3/4)| ≤ r at hh
    simpa only [neg_div, sub_neg_eq_add] using hh

lemma phaseWindow_positive {x : Parameter} {r : ℝ} (hr : r < 1) (hx : x ∈ phaseWindow r) :
    x ∈ positiveParameters := by
  have hh := (abs_le.mp (phaseWindow_coords hx).1).1
  change 0 < x 0
  linarith

lemma phaseWindow_mono {r s : ℝ} (h : r ≤ s) : phaseWindow r ⊆ phaseWindow s :=
  Metric.closedBall_subset_closedBall h

lemma phaseWindow_near {x y : Parameter} {r s : ℝ} (hx : x ∈ phaseWindow r)
    (hy : y ∈ Metric.closedBall x s) : y ∈ phaseWindow (r+s) := by
  change dist y phaseCenter ≤ r+s
  calc
    dist y phaseCenter ≤ dist y x+dist x phaseCenter := dist_triangle _ _ _
    _ ≤ r+s := by have h1 := Metric.mem_closedBall.mp hx; have h2 := Metric.mem_closedBall.mp hy; linarith

lemma phaseWindow_quarter_bounds {x : Parameter} (hx : x ∈ phaseWindow (1/4)) :
    x 0 ∈ Icc (3/4:ℝ) (5/4) ∧ |x 1| ≤ 2 := by
  have h1 := abs_le.mp (phaseWindow_coords hx).1
  have h2 := abs_le.mp (phaseWindow_coords hx).2
  constructor
  · constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

lemma phaseWindow_half_bounds {x : Parameter} (hx : x ∈ phaseWindow (1/2)) :
    x 0 ∈ Icc (1/2:ℝ) (3/2) ∧ |x 1| ≤ 2 := by
  have h1 := abs_le.mp (phaseWindow_coords hx).1
  have h2 := abs_le.mp (phaseWindow_coords hx).2
  constructor
  · constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

lemma parameter_vertical_norm (h : ℝ) : ‖parameter 0 h‖ = |h| := by
  have hn := parameter_norm_le (parameter 0 h)
  have hl := parameter_coord_abs_le (parameter 0 h) 1
  simp only [parameter_zero, parameter_one, abs_zero, zero_add] at hn hl
  exact le_antisymm hn hl

lemma parameter_horizontal_norm (β : ℝ) : ‖parameter β 0‖ = |β| := by
  have hn := parameter_norm_le (parameter β 0)
  have hl := parameter_coord_abs_le (parameter β 0) 0
  simp only [parameter_zero, parameter_one, abs_zero, add_zero] at hn hl
  exact le_antisymm hn hl

lemma parameter_sub (β h β' h' : ℝ) : parameter β h-parameter β' h'=parameter (β-β') (h-h') := by
  ext i
  fin_cases i <;> rfl

end RadialTransition
end

end OAI
