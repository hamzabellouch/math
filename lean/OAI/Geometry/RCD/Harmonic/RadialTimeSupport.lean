import OAI.Geometry.RCD.Transport.AsymmetricMidpoint

namespace OAI

/-! # One-sided CD support bounds at an arbitrary contraction time

Only the initial density bound is retained. This is the contribution which
survives when the other endpoint concentrates at the pole.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem cd_time_renyi_lower (μ ν₀ ν₁ : Measure X) [SigmaFinite μ]
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    {C₀ : ℝ≥0∞} (h0 : ν₀ ≤ C₀ • μ) (K N : ℝ) (hN : 1 < N)
    (t : Time) (β : ℝ≥0∞)
    (hβ : ∀ᵐ γ ∂π, β ≤ tau K N (1 - (t : ℝ)) (dist (γ 0) (γ 1)))
    (hR : (∫⁻ γ, tau K N (1 - (t : ℝ)) (dist (γ 0) (γ 1)) *
          (ν₀.rnDeriv μ (γ 0)) ^ (-(1 / N)) +
        tau K N (t : ℝ) (dist (γ 0) (γ 1)) *
          (ν₁.rnDeriv μ (γ 1)) ^ (-(1 / N)) ∂π) ≤
        renyiIntegral μ (π.map (fun γ => γ t)) N) :
    β * C₀ ^ (-(1 / N)) ≤ renyiIntegral μ (π.map (fun γ => γ t)) N := by
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have he0 : ν₀ ≪ μ := Measure.absolutelyContinuous_of_le_smul h0
  have hd0 : ∀ᵐ γ ∂π, ν₀.rnDeriv μ (γ 0) ≤ C₀ := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 0).aemeasurable
      (p := fun x => ν₀.rnDeriv μ x ≤ C₀)
    rw [hend.1]
    exact he0.ae_le (rnDeriv_le_const_of_le_smul μ ν₀ h0)
  calc
    _ = ∫⁻ _ : C(Time, X), β * C₀ ^ (-(1 / N)) ∂π := by simp
    _ ≤ _ := (lintegral_mono_ae (by
      filter_upwards [hd0, hβ] with γ hγ0 hb
      have hi : C₀ ^ (-(1 / N)) ≤ (ν₀.rnDeriv μ (γ 0)) ^ (-(1 / N)) := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hγ0 (by positivity))
      exact (mul_le_mul' hb hi).trans (le_add_right le_rfl))).trans hR

noncomputable def timeSupportFactor (n : ℕ) (β C₀ : ℝ≥0∞) : ℝ≥0∞ :=
  (β * C₀ ^ (-(1 / (n : ℝ)))) ^ n

theorem timeSupportFactor_scale {n : ℕ} (hn : 0 < n) (β : ℝ≥0∞)
    {C₀ m : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hm : m ≠ 0) :
    timeSupportFactor n β (C₀ * m⁻¹) = timeSupportFactor n β C₀ * m := by
  have hi : m⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hm
  have hp : (m⁻¹) ^ (-(1 / (n : ℝ))) = m ^ (1 / (n : ℝ)) := by
    rw [ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
  unfold timeSupportFactor
  rw [ENNReal.mul_rpow_of_ne_top hC₀ hi, hp, ← mul_assoc, mul_pow]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (m ^ (1 / (n : ℝ))) ^ n = m := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div_mul_cancel hn0,
      ENNReal.rpow_one]
  rw [he]

theorem FullCD.exists_time_ac_support_bound (μ : Measure X) [SigmaFinite μ]
    {K : ℝ} {n : ℕ} (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C₁ : ℝ≥0∞} (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₁ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (s₀ s₁ : Set X) (hs0 : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs1 : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (hn : 2 ≤ n) (t : Time) (β : ℝ≥0∞)
    (hβ : ∀ x ∈ s₀, ∀ y ∈ s₁, β ≤ tau K n (1 - (t : ℝ)) (dist x y)) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      timeSupportFactor n β C₀ ≤ μ {x | (π.map (fun γ => γ t)).rnDeriv μ x ≠ 0} := by
  obtain ⟨π, hπ, hg, hp, hR⟩ := hcd ν₀ ν₁ inferInstance inferInstance
    (Measure.absolutelyContinuous_of_le_smul h0) (Measure.absolutelyContinuous_of_le_smul h1)
    hm0 hm1
  let := hπ
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have ha0 : ∀ᵐ γ ∂π, γ 0 ∈ s₀ := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 0).aemeasurable (p := fun x => x ∈ s₀)
    rwa [hend.1]
  have ha1 : ∀ᵐ γ ∂π, γ 1 ∈ s₁ := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 1).aemeasurable (p := fun x => x ∈ s₁)
    rwa [hend.2]
  have hb : ∀ᵐ γ ∂π, β ≤ tau K n (1 - (t : ℝ)) (dist (γ 0) (γ 1)) := by
    filter_upwards [ha0, ha1] with γ hγ0 hγ1
    exact hβ _ hγ0 _ hγ1
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  have hh := (cd_time_renyi_lower μ ν₀ ν₁ π hp h0 K n hn1 t β hb
    (hR n le_rfl t)).trans (renyiIntegral_le_ac_support_volume μ (π.map (fun γ => γ t)) n hn1)
  have hpow := ENNReal.rpow_le_rpow hh hn0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hn0.ne', ENNReal.rpow_one,
    ENNReal.rpow_natCast] at hpow
  exact ⟨π, hπ, hg, hp, hpow⟩

end RegularPointCoordinates

end OAI
