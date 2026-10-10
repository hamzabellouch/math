import OAI.Geometry.RCD.Harmonic.WeightedUnitDefect

namespace OAI

/-! # Passing weighted nonnegative errors to the original inner normalization -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem normalized_weighted_core_convergence {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A Ω : ℕ → Set X) (c : ℕ → ℝ) (hc : ∀ k, 0<c k)
    (f e : ℕ → X → ℝ)
    (hfe : ∀ k, IntegrableOn (fun x => f k x*e k x) (Ω k) μ)
    (he0 : ∀ k, ∀ᵐ x ∂μ.restrict (Ω k), 0≤e k x)
    (hf0 : ∀ k, ∀ᵐ x ∂μ.restrict (Ω k), 0≤f k x)
    (hsub : ∀ k, A k⊆Ω k)
    (hplateau : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (A k), f k x=1)
    {v : ℝ} (hv : v≠0)
    (hmass : Tendsto (fun k => c k*μ.real (A k)) atTop (𝓝 v))
    (hlim : Tendsto (fun k => c k*∫ x in Ω k, f k x*e k x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => (μ.real (A k))⁻¹*∫ x in A k, e k x ∂μ) atTop (𝓝 0) := by
  have hcore : Tendsto (fun k => c k*∫ x in A k, e k x ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun k => mul_nonneg (hc k).le
      (integral_nonneg_of_ae (ae_restrict_of_ae_restrict_of_subset (hsub k) (he0 k))))) _ hlim
    filter_upwards [hplateau] with k hk
    apply mul_le_mul_of_nonneg_left _ (hc k).le
    calc
      _ = ∫ x in A k, f k x*e k x ∂μ := integral_congr_ae (hk.mono (fun x hx => by
        change e k x=f k x*e k x
        rw [hx,one_mul]))
      _ ≤ _ := setIntegral_mono_set (hfe k)
        (by filter_upwards [hf0 k,he0 k] with x hf he; exact mul_nonneg hf he)
        (Eventually.of_forall (hsub k))
  have hquot := hcore.div hmass hv
  simp only [zero_div] at hquot
  convert hquot using 1
  funext k
  change (μ.real (A k))⁻¹*(∫ x in A k, e k x ∂μ)=
    (c k*(∫ x in A k, e k x ∂μ))/(c k*μ.real (A k))
  rw [mul_div_mul_left _ _ (hc k).ne',div_eq_inv_mul]

end RegularPointCoordinates

end

end OAI
