import Mathlib

namespace OAI
noncomputable section

open Filter

namespace Problem337

/-- Taking two logarithms converts a double exponential lower bound to a slope bound. -/
theorem slope_lower_of_double_exp {x c : ℝ} {k : ℕ}
    (hk : 0 < k) (h : Real.exp (Real.exp (c * (k : ℝ))) ≤ x) :
    c ≤ Real.log (Real.log x) / (k : ℝ) := by
  have hfirst : Real.exp (c * (k : ℝ)) ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) h
  have hsecond : c * (k : ℝ) ≤ Real.log (Real.log x) := by
    simpa using Real.log_le_log (Real.exp_pos _) hfirst
  exact (le_div_iff₀ (by exact_mod_cast hk)).2 hsecond

/-- Eventual double exponential bounds lead to eventual lower bounds for the slope. -/
theorem eventually_slope_lower_of_double_exp (f : ℕ → ℝ) (c : ℝ)
    (h : ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp (c * (k : ℝ))) ≤ f k) :
    ∀ᶠ k : ℕ in atTop, c ≤ Real.log (Real.log (f k)) / (k : ℝ) := by
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with k h hk
  exact slope_lower_of_double_exp hk h

/-- The lower limiting slope uses only eventual double exponential lower bounds
and boundedness above; no Egyptian fraction constructions enter this step. -/
theorem liminf_slope_lower_of_double_exp (f : ℕ → ℝ) (A : ℝ)
    (hupper : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => Real.log (Real.log (f k)) / (k : ℝ)))
    (hlower : ∀ c : ℝ, c < A →
      ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp (c * (k : ℝ))) ≤ f k) :
    A ≤ liminf (fun k : ℕ => Real.log (Real.log (f k)) / (k : ℝ)) atTop ∧
    liminf (fun k : ℕ => Real.log (Real.log (f k)) / (k : ℝ)) atTop ≤
      limsup (fun k : ℕ => Real.log (Real.log (f k)) / (k : ℝ)) atTop := by
  have hlow : IsBoundedUnder (· ≥ ·) atTop
      (fun k : ℕ => Real.log (Real.log (f k)) / (k : ℝ)) :=
    ⟨A - 1, eventually_slope_lower_of_double_exp f (A - 1)
      (hlower (A - 1) (by linarith))⟩
  constructor
  · apply (le_liminf_iff' hupper.isCoboundedUnder_ge hlow).2
    intro c hc
    exact eventually_slope_lower_of_double_exp f c (hlower c hc)
  · exact liminf_le_limsup hupper hlow

/-- A coarse elementary bound for log 2 is enough for the stated constant 600. -/
theorem one_div_six_hundred_lt_prescribed_rate :
    (1 : ℝ) / 600 < Real.log 2 / 257 := by
  have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hlog
  linarith

/-- Specialization of the family of rates to the explicit constant in the corollary. -/
theorem eventually_double_exp_six_hundred (f : ℕ → ℝ)
    (h : ∀ c : ℝ, c < Real.log 2 / 257 →
      ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp (c * (k : ℝ))) ≤ f k) :
    ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp ((k : ℝ) / 600)) ≤ f k := by
  simpa [div_eq_mul_inv, mul_comm] using
    h (1 / 600) one_div_six_hundred_lt_prescribed_rate

end Problem337

end

end OAI
