import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePackingAsymptotics

namespace OAI

/-! # A common subexponential envelope for fixed polynomial losses -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem log_shift_div_tendsto_zero :
    Tendsto (fun r : ℝ => Real.log (2 + r) / r) atTop (𝓝 0) := by
  have hadd : Tendsto (fun r : ℝ => 2 + r) atTop atTop := by
    apply tendsto_atTop.mpr
    intro x
    filter_upwards [eventually_ge_atTop (x - 2)] with r hr
    linarith
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp hadd
  convert h using 1
  funext r
  simp only [Function.comp_apply, pow_one, one_mul]
  congr 1
  ring

/-- One nonnegative error function tending to zero absorbs a fixed
polynomial at every sufficiently large scale. This allows the same error
to be used simultaneously for all sampled chart positions. -/
theorem exists_polynomial_exp_envelope {A : ℝ} (hA : 0 ≤ A) (p : ℕ) :
    ∃ ε : ℝ → ℝ, (∀ r, 0 ≤ ε r) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ r : ℝ, 1 ≤ r → A * (1 + r) ^ p ≤ Real.exp (r * ε r) := by
  let ε : ℝ → ℝ := fun r =>
    (Real.log (A + 1) + (p : ℝ) * Real.log (2 + max r 0)) / max r 1
  have hε (r : ℝ) : 0 ≤ ε r := by
    apply div_nonneg
    · exact add_nonneg (Real.log_nonneg (by linarith))
        (mul_nonneg (Nat.cast_nonneg p) (Real.log_nonneg (by linarith [le_max_right r 0])))
    · linarith [le_max_right r 1]
  have hlim : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun r : ℝ => Real.log (A + 1) / r) atTop (𝓝 0)).add
      (log_shift_div_tendsto_zero.const_mul (p : ℝ))
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    dsimp [ε]
    rw [max_eq_left hr, max_eq_left (by linarith : 0 ≤ r)]
    ring
  refine ⟨ε, hε, hlim, ?_⟩
  intro r hr
  have hr0 : 0 < r := by linarith
  have heq : Real.exp (r * ε r) = (A + 1) * (2 + r) ^ p := by
    have hmul : r * ε r = Real.log (A + 1) + (p : ℝ) * Real.log (2 + r) := by
      dsimp [ε]
      rw [max_eq_left hr, max_eq_left hr0.le]
      field_simp
    rw [hmul, Real.exp_add, Real.exp_log (by linarith : 0 < A + 1),
      Real.exp_nat_mul, Real.exp_log (by linarith : 0 < 2 + r)]
  rw [heq]
  exact mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) (by linarith) p)
    (by positivity) (by linarith)

end PolycyclicRecognition

end OAI
