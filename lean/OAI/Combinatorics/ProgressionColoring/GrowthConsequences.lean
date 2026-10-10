import OAI.Combinatorics.ProgressionColoring.GrowthRates

namespace OAI

namespace QuantitativeVanDerWaerden

open Filter

/-- A single threshold for all color counts yields divergence of the actual
infimum over all integers `r ≥ 2`. -/
theorem uniform_length_rate_tendsto
    {F : ℕ → ℕ → ℝ} {c : ℝ} {K : ℕ} (hc : 0 < c)
    (hbound : ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) < F r k) :
    Tendsto (fun k : ℕ => ⨅ r : {r : ℕ // 2 ≤ r},
      Real.log (F r.val k) / ((k : ℝ) * Real.log (r.val : ℝ))) atTop atTop := by
  let : Nonempty {r : ℕ // 2 ≤ r} := ⟨⟨2, le_rfl⟩⟩
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcoef : 0 < c / (2 * Real.log 2) := by positivity
  apply tendsto_iInf_atTop_of_uniform_lower (hlog.const_mul_atTop hcoef)
  filter_upwards [eventually_ge_atTop (max K 2)] with k hk
  intro r
  exact log_ratio_lower_of_rpow_bound hc.le r.property
    ((le_max_right K 2).trans hk) (hbound k ((le_max_left K 2).trans hk) r.val r.property)

/-- The superpolynomial color estimate is uniform in every progression
length at least three, including the real infimum conclusion. -/
theorem uniform_color_rate_tendsto
    {F : ℕ → ℕ → ℝ} {R : ℕ}
    (hbound : ∀ r ≥ R, ∀ k ≥ 3,
      Real.exp ((Real.log (r : ℝ)) ^ 2 / (64 * Real.log 2)) < F r k) :
    Tendsto (fun r : ℕ => ⨅ k : {k : ℕ // 3 ≤ k},
      Real.log (F r k.val) / Real.log (r : ℝ)) atTop atTop := by
  let : Nonempty {k : ℕ // 3 ≤ k} := ⟨⟨3, le_rfl⟩⟩
  have hlog : Tendsto (fun r : ℕ => Real.log (r : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hden : 0 < (64 : ℝ) * Real.log 2 := by positivity
  apply tendsto_iInf_atTop_of_uniform_lower (hlog.atTop_div_const hden)
  filter_upwards [eventually_ge_atTop (max R 2)] with r hr
  intro k
  have hrone : (1 : ℝ) < r := by
    exact_mod_cast (by have := (le_max_right R 2).trans hr; omega : 1 < r)
  exact log_ratio_lower_of_exp_bound hrone
    (hbound r ((le_max_left R 2).trans hr) k.val k.property)

/-- Every fixed number of colors at least two has the full kth-root limit. -/
theorem fixed_color_kthRoot_tendsto
    {F : ℕ → ℕ → ℝ} {c : ℝ} {K : ℕ} (hc : 0 < c)
    (hbound : ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) < F r k)
    {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun k : ℕ => (F r k) ^ (1 / (k : ℝ))) atTop atTop := by
  have hm : (0 : ℝ) < (Nat.log 2 r : ℝ) := by
    exact_mod_cast (Nat.log_pos (by omega : 1 < 2) hr)
  apply tendsto_kthRoot_of_eventually_rpow_bound (mul_pos hc hm)
  filter_upwards [eventually_ge_atTop K] with k hk
  simpa only [mul_assoc, mul_left_comm, mul_comm] using (hbound k hk r hr).le

/-- A quadratic logarithmic lower bound dominates every fixed power.
This statement even allows an arbitrary real exponent. -/
theorem polynomial_ratio_tendsto_of_exp_sq_log
    {F : ℕ → ℝ} {C : ℝ} (hC : 0 < C) (A : ℝ)
    (hbound : ∀ᶠ r : ℕ in atTop,
      Real.exp ((Real.log (r : ℝ)) ^ 2 / C) < F r) :
    Tendsto (fun r : ℕ => F r / (r : ℝ) ^ A) atTop atTop := by
  have hlog : Tendsto (fun r : ℕ => Real.log (r : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ),
    hlog.eventually_ge_atTop (C * (A + 1))] with r hb hr hlarge
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlogr : 0 ≤ Real.log (r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have hquad : (A + 1) * Real.log (r : ℝ) ≤ (Real.log (r : ℝ)) ^ 2 / C := by
    apply (le_div_iff₀ hC).2
    nlinarith [mul_nonneg hlogr (sub_nonneg.mpr hlarge)]
  have hpow : (r : ℝ) ^ (A + 1) ≤ F r := by
    calc
      (r : ℝ) ^ (A + 1) = Real.exp (Real.log (r : ℝ) * (A + 1)) :=
        Real.rpow_def_of_pos hrpos _
      _ ≤ Real.exp ((Real.log (r : ℝ)) ^ 2 / C) :=
        Real.exp_le_exp.mpr (by simpa only [mul_comm] using hquad)
      _ ≤ F r := hb.le
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hrpos A)).2
  calc
    (r : ℝ) * (r : ℝ) ^ A = (r : ℝ) ^ (A + 1) := by
      rw [Real.rpow_add hrpos, Real.rpow_one]
      ring
    _ ≤ F r := hpow

end QuantitativeVanDerWaerden

end OAI
