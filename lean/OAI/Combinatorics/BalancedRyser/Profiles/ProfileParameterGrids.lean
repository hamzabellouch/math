import Mathlib

namespace OAI

open Filter Set MeasureTheory
open scoped Topology BigOperators

namespace Balanced.ProfileParameterGrids

lemma right_rule_error {f : ℝ → ℝ} {a b ε : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hmod : ∀ x ∈ Icc a b, ‖f b - f x‖ ≤ ε) :
    ‖(b - a) * f b - ∫ x in a..b, f x‖ ≤ ε * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun x => f b - f x) (C := ε) (by
      intro x hx
      rw [uIoc_of_le hab] at hx
      exact hmod x ⟨hx.1.le, hx.2⟩)
  rw [intervalIntegral.integral_sub intervalIntegrable_const hf,
    intervalIntegral.integral_const, smul_eq_mul,
    abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact h

theorem right_grid_error {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hmod : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |x - y| ≤ 1 / (n : ℝ) → ‖f x - f y‖ ≤ ε) :
    ‖(∑ i ∈ Finset.range n, f (((i + 1 : ℕ) : ℝ) / n)) / n -
      ∫ x in (0 : ℝ)..1, f x‖ ≤ ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  let a : ℕ → ℝ := fun i => (i : ℝ) / n
  have ha_mem : ∀ i ≤ n, a i ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hnR.le
    · apply (div_le_one hnR).mpr
      exact_mod_cast hi
  have ha_le : ∀ i, a i ≤ a (i + 1) := by
    intro i
    apply div_le_div_of_nonneg_right _ hnR.le
    exact_mod_cast Nat.le_succ i
  have ha_diff : ∀ i, a (i + 1) - a i = 1 / (n : ℝ) := by
    intro i
    dsimp [a]
    push_cast
    ring
  have hseg : ∀ i < n, Icc (a i) (a (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
    intro i hi x hx
    exact ⟨(ha_mem i hi.le).1.trans hx.1,
      hx.2.trans (ha_mem (i + 1) (Nat.succ_le_of_lt hi)).2⟩
  have hint : ∀ i < n, IntervalIntegrable f volume (a i) (a (i + 1)) := by
    intro i hi
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (ha_le i)]
    exact hf.mono (hseg i hi)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have hsum' : (∑ i ∈ Finset.range n, ∫ x in a i..a (i + 1), f x) =
      ∫ x in (0 : ℝ)..1, f x := by
    simpa [a, hn0] using hsum
  have herr : ∀ i ∈ Finset.range n,
      ‖(1 / (n : ℝ)) * f (a (i + 1)) -
        ∫ x in a i..a (i + 1), f x‖ ≤ ε / n := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hb := right_rule_error (ha_le i) (hint i hin) (ε := ε) (by
      intro x hx
      apply hmod (a (i + 1)) (ha_mem (i + 1) (Nat.succ_le_of_lt hin)) x (hseg i hin hx)
      rw [abs_of_nonneg (sub_nonneg.mpr hx.2)]
      have hx' := hx.1
      rw [← ha_diff i]
      linarith)
    rw [ha_diff] at hb
    simpa only [div_eq_mul_inv, one_mul] using hb
  calc
    ‖(∑ i ∈ Finset.range n, f (((i + 1 : ℕ) : ℝ) / n)) / n -
        ∫ x in (0 : ℝ)..1, f x‖ =
      ‖∑ i ∈ Finset.range n,
        ((1 / (n : ℝ)) * f (a (i + 1)) - ∫ x in a i..a (i + 1), f x)‖ := by
          congr 1
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum']
          dsimp [a]
          ring
    _ ≤ ∑ i ∈ Finset.range n, ε / n :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum herr)
    _ = ε := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

theorem tendsto_right_grid {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range n, f (((i + 1 : ℕ) : ℝ) / n)) / n)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff_le.mp hu (ε / 2) (by linarith)
  have hsmall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n < δ :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨max 1 N, fun n hn => ?_⟩
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 N).trans hn)
  have hnδ : (1 : ℝ) / n ≤ δ := (hN n ((le_max_right 1 N).trans hn)).le
  have he := right_grid_error hf hnpos (ε := ε / 2) (by
    intro x hx y hy hxy
    have hm := hmod x hx y hy (by simpa only [Real.dist_eq] using hxy.trans hnδ)
    simpa only [Real.dist_eq, Real.norm_eq_abs] using hm)
  rw [Real.dist_eq]
  simpa only [Real.norm_eq_abs] using he.trans_lt (half_lt_self hε)

lemma rpow_mapsTo_unit {p : ℝ} (hp : 0 ≤ p) :
    MapsTo (fun x : ℝ => x ^ p) (Icc 0 1) (Icc 0 1) := by
  intro x hx
  exact ⟨Real.rpow_nonneg hx.1 _, Real.rpow_le_one hx.1 hx.2 hp⟩

theorem tendsto_power_grid {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range n, f ((((i + 1 : ℕ) : ℝ) / n) ^ γ⁻¹)) / n)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, f (x ^ γ⁻¹))) := by
  apply tendsto_right_grid
  exact hf.comp (Real.continuous_rpow_const (inv_nonneg.mpr hγ.le)).continuousOn
    (rpow_mapsTo_unit (inv_nonneg.mpr hγ.le))

theorem integral_power_grid_density {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {γ : ℝ} (hγ : 1 ≤ γ) :
    (∫ x in (0 : ℝ)..1, f (x ^ γ⁻¹)) =
      ∫ z in (0 : ℝ)..1, f z * (γ * z ^ (γ - 1)) := by
  have hγpos : 0 < γ := lt_of_lt_of_le zero_lt_one hγ
  have hγ0 : γ ≠ 0 := ne_of_gt hγpos
  let g : ℝ → ℝ := fun x => f (x ^ γ⁻¹)
  have hg_unit : ContinuousOn g (Icc 0 1) :=
    hf.comp (Real.continuous_rpow_const (inv_nonneg.mpr hγpos.le)).continuousOn
      (rpow_mapsTo_unit (inv_nonneg.mpr hγpos.le))
  have hg_image : ContinuousOn g ((fun x : ℝ => x ^ γ) '' uIcc (0 : ℝ) 1) := by
    apply hg_unit.mono
    rw [uIcc_of_le zero_le_one]
    exact (rpow_mapsTo_unit hγpos.le).image_subset
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := 1) (f := fun x : ℝ => x ^ γ)
    (f' := fun x : ℝ => γ * x ^ (γ - 1)) (g := g)
    (fun x _ => Real.hasDerivAt_rpow_const (Or.inr hγ))
    ((continuous_const.mul (Real.continuous_rpow_const (sub_nonneg.mpr hγ))).continuousOn)
    hg_image
  rw [Real.zero_rpow hγ0, Real.one_rpow] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  dsimp [g]
  have hp : (x ^ γ) ^ γ⁻¹ = x := by
    rw [← Real.rpow_mul hx.1, mul_inv_cancel₀ hγ0, Real.rpow_one]
  rw [hp]

theorem tendsto_power_grid_density {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {γ : ℝ} (hγ : 1 ≤ γ) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range n, f ((((i + 1 : ℕ) : ℝ) / n) ^ γ⁻¹)) / n)
      atTop (𝓝 (∫ z in (0 : ℝ)..1, f z * (γ * z ^ (γ - 1)))) := by
  rw [← integral_power_grid_density hf hγ]
  exact tendsto_power_grid hf (lt_of_lt_of_le zero_lt_one hγ)

theorem tendsto_sqrt_two_grid_density {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range n,
        f ((((i + 1 : ℕ) : ℝ) / n) ^ (Real.sqrt 2)⁻¹)) / n)
      atTop (𝓝 (∫ z in (0 : ℝ)..1,
        f z * (Real.sqrt 2 * z ^ (Real.sqrt 2 - 1)))) := by
  apply tendsto_power_grid_density hf
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

theorem tendsto_power_grid_density_comp {α : Type*} {l : Filter α}
    {N : α → ℕ} (hN : Tendsto N l atTop) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {γ : ℝ} (hγ : 1 ≤ γ) :
    Tendsto (fun a =>
      (∑ i ∈ Finset.range (N a), f ((((i + 1 : ℕ) : ℝ) / (N a)) ^ γ⁻¹)) / (N a))
      l (𝓝 (∫ z in (0 : ℝ)..1, f z * (γ * z ^ (γ - 1)))) :=
  (tendsto_power_grid_density hf hγ).comp hN

end Balanced.ProfileParameterGrids

end OAI
