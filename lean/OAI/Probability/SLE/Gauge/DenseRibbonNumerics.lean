import OAI.Probability.SLE.Gauge.RibbonExperimentAssembly

namespace OAI

/-! Absorb the fixed initial passage probability into the quadratic
experiment cost, and convert width-scaled unit-strip mass to m^(2-d). -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma ribbon_mass_after_width_scaling (κ c a : ℝ) (ha : 0 < a) (m : ℕ) (hm : 0 < m) :
    (a / (m : ℝ)) ^ dimension κ * ((m : ℝ) ^ 2 * c) =
      c * a ^ dimension κ * (m : ℝ) ^ codimension κ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_eq_mul_one_div, Real.mul_rpow ha.le (one_div_nonneg.mpr hmR.le)]
  calc
    _ = c * a ^ dimension κ * ((m : ℝ) ^ 2 * (1 / (m : ℝ)) ^ dimension κ) := by ring
    _ = _ := by rw [ribbon_mass_power_cancellation κ hmR]

/-- One initial positive-probability event and quadratically many uniform
steps have one stretched-exponential cost, uniformly in the mesh. -/
theorem ribbon_initial_and_steps_quadratic_cost
    {q p D : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hp : 0 < p) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m N : ℕ), 0 < m → (N : ℝ) ≤ D * (m : ℝ) ^ 2 →
      Real.exp (-C * (m : ℝ) ^ 2) ≤ q ^ N * p := by
  obtain ⟨C, hC, hcost⟩ := ribbon_probability_of_quadratic_completion
    (lt_min hq hp) ((min_le_left q p).trans hq1) (show 0 ≤ D + 1 by linarith)
  refine ⟨C, hC, fun m N hm hN => ?_⟩
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcount : ((N + 1 : ℕ) : ℝ) ≤ (D + 1) * (m : ℝ) ^ 2 := by
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith
  calc
    _ ≤ min q p ^ (N + 1) := hcost m (N + 1) hcount
    _ = min q p ^ N * min q p := pow_succ _ _
    _ ≤ q ^ N * p := mul_le_mul (pow_le_pow_left₀ (le_of_lt (lt_min hq hp))
      (min_le_left q p) N) (min_le_right q p) (le_of_lt (lt_min hq hp)) (pow_nonneg hq.le N)

end SLEExactGauge

end

end OAI
