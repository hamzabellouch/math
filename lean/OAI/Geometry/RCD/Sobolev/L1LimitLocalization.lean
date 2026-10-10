import OAI.Geometry.RCD.Sobolev.HessianL1LimitUniqueness

namespace OAI

/-! # Bounded localization of strong L1 limits -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem integral_abs_bdd_mul_tendsto_zero (F : ℕ → X → ℝ) (f : X → ℝ)
    (hF : ∀ k, Integrable (F k) μ) (hf : Integrable f μ)
    (hlim : Tendsto (fun k => ∫ x, |F k x-f x| ∂μ) atTop (𝓝 0))
    (χ : X → ℝ) (hχ : AEStronglyMeasurable χ μ) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂μ, |χ x| ≤ D) :
    Tendsto (fun k => ∫ x, |χ x*F k x-χ x*f x| ∂μ) atTop (𝓝 0) := by
  have hb : ∀ᵐ x ∂μ, ‖χ x‖ ≤ D := by simpa only [Real.norm_eq_abs] using hD
  apply squeeze_zero (fun k => integral_nonneg fun x => abs_nonneg _) _
    (by simpa only [mul_zero] using hlim.const_mul (D:ℝ))
  intro k
  calc
    _ = ∫ x, |χ x*(F k x-f x)| ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change |χ x*F k x-χ x*f x| = |χ x*(F k x-f x)|
        rw [mul_sub]
    _ ≤ ∫ x, (D:ℝ)*|F k x-f x| ∂μ := by
      apply integral_mono_ae (((hF k).sub hf).bdd_mul hχ hb).abs
        (((hF k).sub hf).abs.const_mul (D:ℝ))
      filter_upwards [hD] with x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = _ := integral_const_mul _ _

theorem L1_limit_mul_eq (F G : ℕ → X → ℝ) (f g : X → ℝ)
    (hF : ∀ k, Integrable (F k) μ) (hG : ∀ k, Integrable (G k) μ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hFlim : Tendsto (fun k => ∫ x, |F k x-f x| ∂μ) atTop (𝓝 0))
    (hGlim : Tendsto (fun k => ∫ x, |G k x-g x| ∂μ) atTop (𝓝 0))
    (χ : X → ℝ) (hχ : AEStronglyMeasurable χ μ) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂μ, |χ x| ≤ D)
    (heq : ∀ k, F k =ᵐ[μ] fun x => χ x*G k x) :
    f =ᵐ[μ] fun x => χ x*g x := by
  have hb : ∀ᵐ x ∂μ, ‖χ x‖ ≤ D := by simpa only [Real.norm_eq_abs] using hD
  have hχg := hg.bdd_mul hχ hb
  have hχlim := integral_abs_bdd_mul_tendsto_zero μ G g hG hg hGlim χ hχ D hD
  have hFχ : Tendsto (fun k => ∫ x, |F k x-χ x*g x| ∂μ) atTop (𝓝 0) := by
    apply hχlim.congr'
    refine Eventually.of_forall fun k => integral_congr_ae ?_
    filter_upwards [heq k] with x hx
    rw [hx]
  have hFlp : Tendsto (fun k => ∫ x, |F k x-hf.toL1 f x| ∂μ) atTop (𝓝 0) := by
    apply hFlim.congr'
    refine Eventually.of_forall fun k => integral_congr_ae ?_
    filter_upwards [hf.coeFn_toL1] with x hx
    rw [hx]
  exact hf.coeFn_toL1.symm.trans
    (L1_limit_eq_of_convergence μ F hF (hf.toL1 f) hFlp _ hχg hFχ)

end RegularPointCoordinates

end

end OAI
