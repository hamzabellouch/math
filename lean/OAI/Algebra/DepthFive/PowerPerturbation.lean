import Mathlib

namespace OAI

/-! The small change in exponent from one to `rho` does not destroy the
inverse-square-root scale of the rounded operator parameters. -/

noncomputable section
open Filter Topology

namespace Problem335.PowerPerturbation

/-- An explicit error that tends to zero. -/
def error (n : ℝ) : ℝ := 2 * Real.log n / Real.sqrt n + 2 / n

lemma tendsto_error : Tendsto error atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  convert (hlog.const_mul 2).add (hinv.const_mul 2) using 1
  · funext x
    simp [error, div_eq_mul_inv, mul_assoc]
  · norm_num

lemma eventually_error_le_log_two :
    ∀ᶠ n : ℝ in atTop, error n ≤ Real.log 2 := by
  exact tendsto_error.eventually_le_const (Real.log_pos (by norm_num))

/-- Deterministic perturbation estimate, with all rounding and exponent
hypotheses explicit. The extra `exp (1/n)` allows a second ceiling error. -/
lemma rpow_mul_exp_le {n a e : ℝ} (hn : 1 ≤ n) (ha : 0 < a)
    (haUpper : a ≤ n ^ (-(1 / 2 : ℝ)) * Real.exp (1 / n))
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hgap : 1 - e ≤ 4 / Real.sqrt n) :
    a ^ e * Real.exp (1 / n) ≤
      n ^ (-(1 / 2 : ℝ)) * Real.exp (error n) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn
  have hi0 : 0 ≤ 1 / n := by positivity
  have hlog : Real.log a ≤ -(Real.log n / 2) + 1 / n := by
    have h := Real.log_le_log ha haUpper
    rw [Real.log_mul (Real.rpow_pos_of_pos hn0 _).ne' (Real.exp_ne_zero _),
      Real.log_rpow hn0, Real.log_exp] at h
    convert h using 1; ring
  have h1 := mul_le_mul_of_nonneg_right hlog he0
  have h2 := mul_le_mul_of_nonneg_right hgap hl0
  have h3 := mul_le_mul_of_nonneg_right he1 hi0
  have hexp : Real.log a * e + 1 / n ≤
      Real.log n * (-(1 / 2 : ℝ)) + error n := by
    unfold error
    simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
    nlinarith
  rw [Real.rpow_def_of_pos ha, ← Real.exp_add,
    Real.rpow_def_of_pos hn0, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexp

lemma rpow_mul_exp_le_two {n a e : ℝ} (hn : 1 ≤ n) (ha : 0 < a)
    (haUpper : a ≤ n ^ (-(1 / 2 : ℝ)) * Real.exp (1 / n))
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hgap : 1 - e ≤ 4 / Real.sqrt n)
    (herr : error n ≤ Real.log 2) :
    a ^ e * Real.exp (1 / n) ≤ 2 / Real.sqrt n := by
  calc
    a ^ e * Real.exp (1 / n) ≤ n ^ (-(1 / 2 : ℝ)) * Real.exp (error n) :=
      rpow_mul_exp_le hn ha haUpper he0 he1 hgap
    _ ≤ n ^ (-(1 / 2 : ℝ)) * 2 := by
      gcongr
      exact (Real.exp_le_exp.mpr herr).trans_eq (Real.exp_log (by norm_num))
    _ = 2 / Real.sqrt n := by
      rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow]
      ring

/-- Uniform in both the rounded parameter and the varying exponent. -/
theorem eventually_rpow_mul_exp_le_two :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ a e : ℝ,
      0 < a → a ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (1 / (n : ℝ)) →
      0 ≤ e → e ≤ 1 → 1 - e ≤ 4 / Real.sqrt (n : ℝ) →
      a ^ e * Real.exp (1 / (n : ℝ)) ≤ 2 / Real.sqrt (n : ℝ) := by
  have he := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually eventually_error_le_log_two
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 he
  refine ⟨max n₀ 1, fun n hn a e ha haUpper he0 he1 hgap => ?_⟩
  apply rpow_mul_exp_le_two (by exact_mod_cast (le_trans (le_max_right _ _) hn))
    ha haUpper he0 he1 hgap
  exact hn₀ n (le_trans (le_max_left _ _) hn)

/-- The exponent used for `q` is also covered by the uniform estimate. -/
theorem eventually_q_beta_bounds :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ a rho beta : ℝ,
      0 < a → a ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (1 / (n : ℝ)) →
      0 ≤ rho → rho ≤ 1 → 1 - rho ≤ 4 / Real.sqrt (n : ℝ) →
      beta ≤ a ^ rho * Real.exp (1 / (n : ℝ)) →
      a ^ ((1 + rho) / 2) ≤ 2 / Real.sqrt (n : ℝ) ∧
      beta ≤ 2 / Real.sqrt (n : ℝ) := by
  obtain ⟨n₀, h⟩ := eventually_rpow_mul_exp_le_two
  refine ⟨n₀, fun n hn a rho beta ha haUpper hr0 hr1 hgap hbeta => ?_⟩
  constructor
  · have he0 : 0 ≤ (1 + rho) / 2 := by linarith
    have he1 : (1 + rho) / 2 ≤ 1 := by linarith
    have hegap : 1 - (1 + rho) / 2 ≤ 4 / Real.sqrt (n : ℝ) := by linarith
    calc
      a ^ ((1 + rho) / 2) = a ^ ((1 + rho) / 2) * 1 := (mul_one _).symm
      _ ≤ a ^ ((1 + rho) / 2) * Real.exp (1 / (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ha.le _)
        exact Real.one_le_exp_iff.mpr (by positivity)
      _ ≤ 2 / Real.sqrt (n : ℝ) := h n hn a _ ha haUpper he0 he1 hegap
  · exact hbeta.trans (h n hn a rho ha haUpper hr0 hr1 hgap)

lemma inverse_sqrt_le_rpow {n a e : ℝ} (hn : 1 ≤ n)
    (ha : n ^ (-(1 / 2 : ℝ)) ≤ a) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    n ^ (-(1 / 2 : ℝ)) ≤ a ^ e := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hb0 : 0 < n ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hn0 _
  have hb1 : n ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  calc
    n ^ (-(1 / 2 : ℝ)) ≤ (n ^ (-(1 / 2 : ℝ))) ^ e := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hb0 hb1 he1
    _ ≤ a ^ e := Real.rpow_le_rpow hb0.le ha he0

/-- The inverse-square-root estimate implies both weaker bounds used in the
circuit rank analysis after increasing the absolute threshold. -/
theorem eventually_inverse_sqrt_bounds :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      2 / Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (-(2 / 5 : ℝ)) ∧
      2 / Real.sqrt (n : ℝ) ≤ 1 / 2 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop 2)
  refine ⟨max n₀ 16, fun n hn => ?_⟩
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right _ _) hn)
  have hn0 : 0 < (n : ℝ) := by linarith
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hs4 : 4 ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by norm_num) hn0.le).2
    norm_num
    exact_mod_cast hn16
  constructor
  · calc
      2 / Real.sqrt (n : ℝ) = 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow]
        rfl
      _ ≤ (n : ℝ) ^ (1 / 10 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right (hn₀ n (le_trans (le_max_left _ _) hn))
        positivity
      _ = (n : ℝ) ^ (-(2 / 5 : ℝ)) := by
        rw [← Real.rpow_add hn0]
        norm_num
  · apply (div_le_iff₀ hs0).2
    linarith

end Problem335.PowerPerturbation

end

end OAI
