import OAI.Geometry.EinsteinFour.ScalarL4ProductConvergence
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! The nonlinear Hessian candidate and its strong L2 continuity. This is
the two-term chain rule, with L4 first derivatives and L2 second derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem secondDerivative_continuous (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Continuous (deriv (deriv φ)) :=
  ((contDiff_infty_iff_deriv.mp hφ).2).continuous_deriv (by simp)

def scalarCompositionHessian (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {C₁ C₂ : ℝ} (h₁ : ∀ s, |deriv φ s| ≤ C₁) (h₂ : ∀ s, |deriv (deriv φ) s| ≤ C₂)
    (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (g₁ g₂ : Lp ℝ 4 μ) (h : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  scalarCompositionL2Multiply (fun x => deriv (deriv φ) (u x))
    ((secondDerivative_continuous φ hφ).comp_aestronglyMeasurable hu)
    (fun x => h₂ (u x)) (scalarL4Product (μ := μ) g₁ g₂) +
  scalarCompositionL2Multiply (fun x => deriv φ (u x))
    ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable hu)
    (fun x => h₁ (u x)) h

theorem scalarCompositionHessian_coe (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {C₁ C₂ : ℝ} (h₁ : ∀ s, |deriv φ s| ≤ C₁) (h₂ : ∀ s, |deriv (deriv φ) s| ≤ C₂)
    (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (g₁ g₂ : Lp ℝ 4 μ) (h : Lp ℝ 2 μ) :
    scalarCompositionHessian φ hφ h₁ h₂ u hu g₁ g₂ h =ᵐ[μ]
      fun x => deriv (deriv φ) (u x) * g₁ x * g₂ x + deriv φ (u x) * h x := by
  let A := scalarCompositionL2Multiply (fun x => deriv (deriv φ) (u x))
    ((secondDerivative_continuous φ hφ).comp_aestronglyMeasurable hu)
    (fun x => h₂ (u x)) (scalarL4Product (μ := μ) g₁ g₂)
  let B := scalarCompositionL2Multiply (fun x => deriv φ (u x))
    ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable hu) (fun x => h₁ (u x)) h
  filter_upwards [Lp.coeFn_add A B,
    scalarCompositionL2Multiply_coe _ _ (fun x => h₂ (u x)) (scalarL4Product (μ := μ) g₁ g₂),
    scalarCompositionL2Multiply_coe _ _ (fun x => h₁ (u x)) h,
    scalarL4Product_coe g₁ g₂] with x hs ha hb hg
  change (A + B) x = _
  rw [hs, Pi.add_apply, ha, hb, hg]
  ring

theorem scalarCompositionHessian_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {C₁ C₂ : ℝ} (h₁ : ∀ s, |deriv φ s| ≤ C₁) (h₂ : ∀ s, |deriv (deriv φ) s| ≤ C₂)
    (u : ℕ → X → ℝ) (v : X → ℝ)
    (hu : ∀ n, AEStronglyMeasurable (u n) μ) (hv : AEStronglyMeasurable v μ)
    (huv : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    (g₁ g₂ : ℕ → Lp ℝ 4 μ) (h : ℕ → Lp ℝ 2 μ)
    (G₁ G₂ : Lp ℝ 4 μ) (H : Lp ℝ 2 μ)
    (hg₁ : Tendsto g₁ atTop (𝓝 G₁)) (hg₂ : Tendsto g₂ atTop (𝓝 G₂))
    (hh : Tendsto h atTop (𝓝 H)) :
    Tendsto (fun n => scalarCompositionHessian φ hφ h₁ h₂ (u n) (hu n)
      (g₁ n) (g₂ n) (h n)) atTop
      (𝓝 (scalarCompositionHessian φ hφ h₁ h₂ v hv G₁ G₂ H)) := by
  have hC₁ : 0 ≤ C₁ := (abs_nonneg (deriv φ 0)).trans (h₁ 0)
  have hC₂ : 0 ≤ C₂ := (abs_nonneg (deriv (deriv φ) 0)).trans (h₂ 0)
  have hlim₁ : ∀ᵐ x ∂μ, Tendsto (fun n => deriv φ (u n x)) atTop (𝓝 (deriv φ (v x))) := by
    filter_upwards [huv] with x hx
    exact (hφ.continuous_deriv (by simp)).continuousAt.tendsto.comp hx
  have hlim₂ : ∀ᵐ x ∂μ, Tendsto (fun n => deriv (deriv φ) (u n x)) atTop
      (𝓝 (deriv (deriv φ) (v x))) := by
    filter_upwards [huv] with x hx
    exact (secondDerivative_continuous φ hφ).continuousAt.tendsto.comp hx
  have hfirst := scalarL4Product_coefficient_tendsto
    (fun n => (secondDerivative_continuous φ hφ).comp_aestronglyMeasurable (hu n))
    ((secondDerivative_continuous φ hφ).comp_aestronglyMeasurable hv)
    hC₂ (fun n x => h₂ (u n x)) (fun x => h₂ (v x)) hlim₂ hg₁ hg₂
  have hsecond := scalarCompositionL2Multiply_tendsto
    (fun n => (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable (hu n))
    ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable hv)
    hC₁ (fun n x => h₁ (u n x)) (fun x => h₁ (v x)) hlim₁ hh
  exact hfirst.add hsecond

end
end PositiveEinsteinFour.Geometry

end OAI
