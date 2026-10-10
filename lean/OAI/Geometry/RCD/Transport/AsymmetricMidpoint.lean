import OAI.Geometry.RCD.Transport.HyperbolicDistortion
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Midpoint transport with separately controlled endpoint densities

The distance-Laplacian construction needs concentration of one endpoint
at a pole. Equal endpoint bounds lose all control in that limit. Here the
actual CD inequality retains the two inverse density powers separately.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem cd_midpoint_renyi_lower_asymmetric (μ ν₀ ν₁ : Measure X) [SigmaFinite μ]
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    {C₀ C₁ : ℝ≥0∞} (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₁ • μ)
    (K N D : ℝ) (hN : 1 < N)
    (hD : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    (hR : (∫⁻ γ, tau K N (1 - (1 / 2 : ℝ)) (dist (γ 0) (γ 1)) *
          (ν₀.rnDeriv μ (γ 0)) ^ (-(1 / N)) +
        tau K N (1 / 2) (dist (γ 0) (γ 1)) *
          (ν₁.rnDeriv μ (γ 1)) ^ (-(1 / N)) ∂π) ≤
        renyiIntegral μ (π.map (fun γ => γ midpointTime)) N) :
    midpointFloor K N D * (C₀ ^ (-(1 / N)) + C₁ ^ (-(1 / N))) ≤
      renyiIntegral μ (π.map (fun γ => γ midpointTime)) N := by
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have he0 : ν₀ ≪ μ := h0.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  have he1 : ν₁ ≪ μ := h1.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  have hd0 : ∀ᵐ γ ∂π, ν₀.rnDeriv μ (γ 0) ≤ C₀ := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 0).aemeasurable
      (p := fun x => ν₀.rnDeriv μ x ≤ C₀)
    rw [hend.1]
    exact he0.ae_le (rnDeriv_le_const_of_le_smul μ ν₀ h0)
  have hd1 : ∀ᵐ γ ∂π, ν₁.rnDeriv μ (γ 1) ≤ C₁ := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 1).aemeasurable
      (p := fun x => ν₁.rnDeriv μ x ≤ C₁)
    rw [hend.2]
    exact he1.ae_le (rnDeriv_le_const_of_le_smul μ ν₁ h1)
  have hβ : 0 ≤ 1 / N := (one_div_pos.mpr (zero_lt_one.trans hN)).le
  calc
    _ = ∫⁻ _ : C(Time, X), midpointFloor K N D * C₀ ^ (-(1 / N)) +
        midpointFloor K N D * C₁ ^ (-(1 / N)) ∂π := by simp [mul_add]
    _ ≤ _ := (lintegral_mono_ae (by
      filter_upwards [hd0, hd1, hD] with γ hγ0 hγ1 hγD
      have hτ := midpointFloor_le_tau K N D (dist (γ 0) (γ 1)) hN dist_nonneg hγD
      have hi0 : C₀ ^ (-(1 / N)) ≤ (ν₀.rnDeriv μ (γ 0)) ^ (-(1 / N)) := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hγ0 hβ)
      have hi1 : C₁ ^ (-(1 / N)) ≤ (ν₁.rnDeriv μ (γ 1)) ^ (-(1 / N)) := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hγ1 hβ)
      norm_num only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
      exact add_le_add (mul_le_mul' hτ hi0) (mul_le_mul' hτ hi1))).trans hR

theorem FullCD.exists_midpoint_ac_support_bound_asymmetric (μ : Measure X) [SigmaFinite μ]
    {K : ℝ} {n : ℕ} (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C₁ : ℝ≥0∞} (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₁ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (s₀ s₁ : Set X) (hs0 : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs1 : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (hn : 2 ≤ n) (D : ℝ) (hD : ∀ x ∈ s₀, ∀ y ∈ s₁, dist x y ≤ D) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      (midpointFloor K n D * (C₀ ^ (-(1 / (n : ℝ))) + C₁ ^ (-(1 / (n : ℝ))))) ^ n ≤
        μ {x | (π.map (fun γ => γ midpointTime)).rnDeriv μ x ≠ 0} := by
  have he0 : ν₀ ≪ μ := h0.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  have he1 : ν₁ ≪ μ := h1.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  obtain ⟨π, hπ, hg, hp, hR⟩ := hcd ν₀ ν₁ inferInstance inferInstance he0 he1 hm0 hm1
  let := hπ
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have ha0 : ∀ᵐ γ ∂π, γ 0 ∈ s₀ := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 0).aemeasurable (p := fun x => x ∈ s₀)
    rwa [hend.1]
  have ha1 : ∀ᵐ γ ∂π, γ 1 ∈ s₁ := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 1).aemeasurable (p := fun x => x ∈ s₁)
    rwa [hend.2]
  have hπD : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D := by
    filter_upwards [ha0, ha1] with γ hγ0 hγ1
    exact hD _ hγ0 _ hγ1
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  let : IsProbabilityMeasure (π.map (fun γ => γ midpointTime)) := inferInstance
  have hh := (cd_midpoint_renyi_lower_asymmetric μ ν₀ ν₁ π hp h0 h1 K n D hn1 hπD
    (hR n le_rfl midpointTime)).trans
      (renyiIntegral_le_ac_support_volume μ (π.map (fun γ => γ midpointTime)) n hn1)
  have hpow := ENNReal.rpow_le_rpow hh hn0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hn0.ne', ENNReal.rpow_one,
    ENNReal.rpow_natCast] at hpow
  exact ⟨π, hπ, hg, hp, hpow⟩


/-- The volume factor from the two separately bounded endpoint densities. -/
noncomputable def midpointSupportFactor (K : ℝ) (n : ℕ) (D : ℝ)
    (C₀ C₁ : ℝ≥0∞) : ℝ≥0∞ :=
  (midpointFloor K n D * (C₀ ^ (-(1 / (n : ℝ))) + C₁ ^ (-(1 / (n : ℝ))))) ^ n

theorem midpointSupportFactor_scale (K : ℝ) {n : ℕ} (hn : 0 < n) (D : ℝ)
    {C₀ C₁ m : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC₁ : C₁ ≠ ∞) (hm : m ≠ 0) :
    midpointSupportFactor K n D (C₀ * m⁻¹) (C₁ * m⁻¹) =
      midpointSupportFactor K n D C₀ C₁ * m := by
  have hi : m⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hm
  have hp : (m⁻¹) ^ (-(1 / (n : ℝ))) = m ^ (1 / (n : ℝ)) := by
    rw [ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
  unfold midpointSupportFactor
  rw [ENNReal.mul_rpow_of_ne_top hC₀ hi, ENNReal.mul_rpow_of_ne_top hC₁ hi, hp,
    ← add_mul, ← mul_assoc, mul_pow]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (m ^ (1 / (n : ℝ))) ^ n = m := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div_mul_cancel hn0,
      ENNReal.rpow_one]
  rw [he]

end RegularPointCoordinates

end OAI
