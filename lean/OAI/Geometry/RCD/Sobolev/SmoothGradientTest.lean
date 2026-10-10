import OAI.Geometry.RCD.Sobolev.SmoothLocalLipschitz
import OAI.Geometry.RCD.Sobolev.PhysicalBallMeasuredTests

namespace OAI

/-! # Bounded continuous gradient tests for measured approximation -/

open Set Metric MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

def smoothGradientTest {n : ℕ} {ψ : Euclidean n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) : Euclidean n →ᵇ ℝ := by
  have hc := hψ.continuous_fderiv (by norm_num)
  refine ⟨⟨fun z => ‖fderiv ℝ ψ z‖,hc.norm⟩,?_⟩
  obtain ⟨C,hC⟩ := (hs.fderiv ℝ).exists_bound_of_continuous hc
  refine ⟨2*C,?_⟩
  intro x y
  calc dist ‖fderiv ℝ ψ x‖ ‖fderiv ℝ ψ y‖
      ≤ ‖fderiv ℝ ψ x‖+‖fderiv ℝ ψ y‖ := by
        calc dist ‖fderiv ℝ ψ x‖ ‖fderiv ℝ ψ y‖
            ≤ dist ‖fderiv ℝ ψ x‖ 0+dist 0 ‖fderiv ℝ ψ y‖ := dist_triangle _ _ _
          _ = _ := by simp
    _ ≤ 2*C := by linarith [hC x,hC y]

@[simp] theorem smoothGradientTest_apply {n : ℕ} {ψ : Euclidean n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) (z : Euclidean n) :
    smoothGradientTest hψ hs z=‖fderiv ℝ ψ z‖ := rfl

end RegularPointCoordinates

end

end OAI
