import OAI.Geometry.RCD.Transport.AsymmetricMidpoint

namespace OAI

/-! # Both endpoint volumes in the actual CD midpoint inequality

This form applies to the preimages of Euclidean balls under metric
approximations. No measured limit or volume convergence is assumed.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem FullCD.midpoint_support_volume_bound (μ : Measure X) [SigmaFinite μ]
    {K : ℝ} {n : ℕ} (hcd : FullCD μ K n) (hn : 2 ≤ n)
    (A B C : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hA0 : μ A ≠ 0) (hAtop : μ A ≠ ∞) (hB0 : μ B ≠ 0) (hBtop : μ B ≠ ∞)
    (hMA : FiniteSecondMoment (uniformOn μ A)) (hMB : FiniteSecondMoment (uniformOn μ B))
    (D : ℝ) (hD : ∀ x ∈ A, ∀ y ∈ B, dist x y ≤ D)
    (hmid : ∀ γ : C(Time,X), IsGeodesic γ → γ 0 ∈ A → γ 1 ∈ B → γ midpointTime ∈ C) :
    midpointFloor K n D*((μ A)^(1/(n:ℝ))+(μ B)^(1/(n:ℝ))) ≤ (μ C)^(1/(n:ℝ)) := by
  let := uniformOn_probability μ A hA0 hAtop
  let := uniformOn_probability μ B hB0 hBtop
  obtain ⟨π,hπ,hgeo,hopt,hentropy⟩ := hcd (uniformOn μ A) (uniformOn μ B)
    inferInstance inferInstance (uniformOn_absolutelyContinuous μ A)
    (uniformOn_absolutelyContinuous μ B) hMA hMB
  let := hπ
  obtain ⟨heA,heB⟩ := optimalPlan_endpoints _ _ π hopt
  have h0 : ∀ᵐ γ ∂π, γ 0 ∈ A := by
    apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
    rw [heA]
    exact uniformOn_ae_mem μ A hA
  have h1 : ∀ᵐ γ ∂π, γ 1 ∈ B := by
    apply ae_of_ae_map (measurable_path_eval 1).aemeasurable
    rw [heB]
    exact uniformOn_ae_mem μ B hB
  have hrA : ∀ᵐ γ ∂π,
      ((uniformOn μ A).rnDeriv μ (γ 0))^(-(1/(n:ℝ)))=(μ A)^(1/(n:ℝ)) := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 0).aemeasurable
      (p := fun x => ((uniformOn μ A).rnDeriv μ x)^(-(1/(n:ℝ)))=(μ A)^(1/(n:ℝ)))
    rw [heA]
    exact uniformOn_rnDeriv_neg_power μ A hA n
  have hrB : ∀ᵐ γ ∂π,
      ((uniformOn μ B).rnDeriv μ (γ 1))^(-(1/(n:ℝ)))=(μ B)^(1/(n:ℝ)) := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 1).aemeasurable
      (p := fun x => ((uniformOn μ B).rnDeriv μ x)^(-(1/(n:ℝ)))=(μ B)^(1/(n:ℝ)))
    rw [heB]
    exact uniformOn_rnDeriv_neg_power μ B hB n
  have hs : ∀ᵐ x ∂π.map (fun γ => γ midpointTime), x ∈ C := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable hC).mpr
    filter_upwards [hgeo,h0,h1] with γ hg ha hb
    exact hmid γ hg ha hb
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  calc
    _ = ∫⁻ _ : C(Time,X), midpointFloor K n D*
        ((μ A)^(1/(n:ℝ))+(μ B)^(1/(n:ℝ))) ∂π := by simp
    _ ≤ ∫⁻ γ, tau K n (1-(midpointTime:ℝ)) (dist (γ 0) (γ 1))*
        ((uniformOn μ A).rnDeriv μ (γ 0))^(-(1/(n:ℝ)))+
        tau K n (midpointTime:ℝ) (dist (γ 0) (γ 1))*
        ((uniformOn μ B).rnDeriv μ (γ 1))^(-(1/(n:ℝ))) ∂π := by
      apply lintegral_mono_ae
      filter_upwards [h0,h1,hrA,hrB] with γ ha hb hra hrb
      rw [hra,hrb,mul_add]
      have hτ := midpointFloor_le_tau K n D (dist (γ 0) (γ 1)) hn1 dist_nonneg (hD _ ha _ hb)
      norm_num only [midpointTime,show (1-(1/2:ℝ))=1/2 by norm_num]
      exact add_le_add (mul_le_mul' hτ le_rfl) (mul_le_mul' hτ le_rfl)
    _ ≤ renyiIntegral μ (π.map (fun γ => γ midpointTime)) n := hentropy n le_rfl midpointTime
    _ ≤ (μ C)^(1/(n:ℝ)) := renyiIntegral_le_support_volume μ _ C hC hs n hn1

theorem midpoint_root_bound_to_mass {n : ℕ} (hn : 0 < n)
    {a b c d : ℝ≥0∞}
    (h : c*(a^(1/(n:ℝ))+b^(1/(n:ℝ))) ≤ d^(1/(n:ℝ))) :
    c^n*b ≤ d := by
  have hb : b^(1/(n:ℝ)) ≤ a^(1/(n:ℝ))+b^(1/(n:ℝ)) := le_add_left le_rfl
  have hp := pow_le_pow_left' ((mul_le_mul' (le_refl c) hb).trans h) n
  have he (x : ℝ≥0∞) : (x^(1/(n:ℝ)))^n=x := by
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul,
      one_div_mul_cancel (by exact_mod_cast hn.ne' : (n:ℝ)≠0),ENNReal.rpow_one]
  simpa only [mul_pow,he] using hp

end RegularPointCoordinates

end

end OAI
