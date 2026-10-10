import OAI.NumberTheory.TotientAsymptotic.NormalizedComparison

namespace OAI

/-!
The PPT construction has a first normalized cutoff approaching one.  Its
inverse-log-cube loss still implies the literal first-cutoff power bound
in Ford's comparison lemma.  No fixed bound such as `ν₁ ≤ 4/5` is needed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- A contracting adjacent row leaves enough room for the grid and
normality errors before checking the published first-cutoff bound. -/
lemma ppt_log_loss_of_contracted_coordinate {t ω e ν : ℝ}
    (ht : 0 < t) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hν : ν ≤ 1/(1+ω)+e) (herr : 4*e ≤ ω)
    (hbudget : 4*Real.log (10*t) ≤ t*ω) :
    Real.log (10*t) ≤ t*(1-ν) := by
  have hden : 0 < 1+ω := by linarith
  have hrec : 1/(1+ω) ≤ 1-ω/2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hν' : ν ≤ 1-ω/4 := by linarith
  have hh := mul_le_mul_of_nonneg_left hν' ht.le
  nlinarith

lemma ppt_comparison_cutoff_power_of_log_loss {z ν : ℝ} (hz : 1 < z)
    (hB : 0 < B z) (hloss : Real.log (10*B z) ≤ B z*(1-ν)) :
    Real.exp (Real.exp (B z*ν)) ≤ z^(1/(10*B z)) := by
  have hscale : 0 < 10*B z := by positivity
  have hinner : Real.exp (B z*ν) ≤ Real.log z/(10*B z) := by
    apply (le_div_iff₀ hscale).mpr
    calc
      _ = Real.exp (Real.log (10*B z)+B z*ν) := by
        rw [Real.exp_add, Real.exp_log hscale]
        ring
      _ ≤ Real.exp (B z) := Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.log z := Real.exp_log (Real.log_pos hz)
  conv_rhs => rw [Real.rpow_def_of_pos (zero_lt_one.trans hz)]
  exact Real.exp_le_exp.mpr (by simpa only [div_eq_mul_inv, one_mul] using hinner)

lemma ppt_inverse_log_cube_cutoff_loss {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ t : ℝ in atTop, Real.log (10*t) ≤ γ*t/(Real.log t)^3 := by
  have h₃ : Tendsto (fun t : ℝ => (Real.log t)^3/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have h₄ : Tendsto (fun t : ℝ => (Real.log t)^4/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hsum : Tendsto (fun t : ℝ =>
      Real.log 10*((Real.log t)^3/t)+(Real.log t)^4/t) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (h₃.const_mul (Real.log 10)).add h₄
  filter_upwards [hsum.eventually (eventually_lt_nhds hγ),
    eventually_gt_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have he : Real.log (10*t)*(Real.log t)^3/t =
      Real.log 10*((Real.log t)^3/t)+(Real.log t)^4/t := by
    rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) ht0.ne']
    ring
  rw [← he] at ht
  have hm := (div_lt_iff₀ ht0).mp ht
  exact (le_div_iff₀ (pow_pos hlog 3)).mpr hm.le

theorem ppt_comparison_cutoff_power_of_inverse_log_cube {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ z : ℝ in atTop, ∀ ν : ℝ,
      ν ≤ 1-γ/(Real.log (B z))^3 →
      Real.exp (Real.exp (B z*ν)) ≤ z^(1/(10*B z)) := by
  filter_upwards [B_tendsto.eventually (ppt_inverse_log_cube_cutoff_loss hγ),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with z hloss hB hz
  intro ν hν
  apply ppt_comparison_cutoff_power_of_log_loss hz (zero_lt_one.trans hB)
  apply hloss.trans
  have hh : γ/(Real.log (B z))^3 ≤ 1-ν := by linarith
  have hm := mul_le_mul_of_nonneg_left hh (zero_lt_one.trans hB).le
  convert hm using 1
  ring

/-- The first normalized cutoff is controlled by its actual logarithmic
loss.  All other assumptions are the literal Ford parameter restrictions
expressed through normalized coordinates. -/
theorem ppt_ford_parameters_of_normalized_grid {z : ℝ} (hz : 1 < z)
    (hB : 0 < B z) (b D r : ℕ) (S : ℝ) (ν μ : ℕ → ℝ)
    (hb : 1 ≤ b) (hν : ν 0=1) (hS : Real.exp (Real.exp 1) ≤ S)
    (hSb : S ≤ comparisonCutoffs z ν b)
    (horder : ∀ j ∈ Finset.range b, ν (j+1) < μ j ∧ μ j < ν j)
    (hfirst : Real.log (10*B z) ≤ B z*(1-ν 1))
    (hgap : ∀ j ∈ Finset.Icc 2 b,
      2*Real.sqrt (B S/B z) < ν (j-1)-ν j)
    (hD : 1 ≤ D) (hDz : (D : ℝ) ≤ z^(1/100 : ℝ))
    (hDs : (largestPrimeFactor D : ℝ) ≤ comparisonCutoffs z ν b)
    (hr : 1 ≤ r) (hrz : (r : ℝ) ≤ z^(1/10 : ℝ)) :
    FordComparisonParameters b z S D r
      (comparisonCutoffs z ν) (comparisonCutoffs z μ) := by
  refine ⟨hb, ?_, hS, hSb, ?_, ?_, ?_, hD, hDz, hDs, hr, hrz⟩
  · simp only [comparisonCutoffs, hν, mul_one, B,
      Real.exp_log (Real.log_pos hz), Real.exp_log (zero_lt_one.trans hz)]
  · intro j hj
    exact ⟨Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr
      (mul_lt_mul_of_pos_left (horder j hj).1 hB)),
      Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr
      (mul_lt_mul_of_pos_left (horder j hj).2 hB))⟩
  · exact ppt_comparison_cutoff_power_of_log_loss hz hB hfirst
  · intro j hj
    simpa only [comparisonCutoffs_doubleLog hB.ne'] using hgap j hj

end TotientAsymptotic

end

end OAI
