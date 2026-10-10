import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorReference
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorBumpDerivatives
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarEuclideanLaplacian
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.EuclideanConjugacy

namespace OAI

/-! The fixed rational burst duration controls the actual Laplacian of
the inviscid reference, uniformly over its entire computational prefix. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

theorem scalar_second_const_mul {f : EuclideanPlane → ℝ}
    (hf : ContDiff ℝ ∞ f) (a : ℝ) (x : EuclideanPlane) :
    fderiv ℝ (fderiv ℝ (fun y => a * f y)) x =
      a • fderiv ℝ (fderiv ℝ f) x := by
  have he : fderiv ℝ (fun y => a * f y) = fun y => a • fderiv ℝ f y := by
    funext y
    exact ((hf.differentiable (by simp) y).hasFDerivAt.const_mul a).fderiv
  rw [he]
  exact (((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt.const_smul a).fderiv

theorem detectorPhase_range (C L n : ℕ) (t : ℝ) :
    0 ≤ detectorPhase C L n t ∧ detectorPhase C L n t ≤ (n : ℝ) + 1 := by
  have h := smoothRamp_range 0 1
    ((t - 2 * ((n : ℝ) + 1) - (duration C L n : ℝ)) / (duration C L n : ℝ))
  unfold detectorPhase
  constructor
  · exact mul_nonneg (by positivity) h.1
  · simpa only [mul_one] using
      mul_le_mul_of_nonneg_left h.2 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)

theorem detectorReference_laplacian_bound {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hv : PlanarVariations V Ψ)
    (hV : ∀ s, ContDiff ℝ ∞ (V s))
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    (L : ℕ) (hL : 0 < L)
    (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
    (h₂ : ∀ s x, ‖fderiv ℝ (fderiv ℝ (euclideanMap (V s))) x‖ ≤ (L : ℝ))
    (n : ℕ) (t : ℝ) (x : Plane) :
    |scalarLaplacian (detectorReference Ψ detectorBumpDerivativeBound L n t) x| ≤
      (laplacianBound detectorBumpDerivativeBound L n : ℝ) := by
  let C := detectorBumpDerivativeBound
  let b : ℝ := width L n
  let σ := detectorPhase C L n t
  let g : EuclideanPlane → ℝ := fun y => detectorBump b (planeCoordinates y)
  let φ := euclideanMap (Ψ σ (-σ))
  let θ := detectorInjectionFraction C L n t
  have hb : 0 < b := by
    dsimp only [b]
    exact_mod_cast width_pos L n
  have hb₁ : b ≤ 1 / 16 := detector_width_small L n
  have hg : ContDiff ℝ ∞ g := scalarEuclidean_smooth (detectorBump_smooth hb)
  have hφ : ContDiff ℝ ∞ φ := euclideanMap_smooth (hv.smooth σ (-σ))
  have hσ := detectorPhase_range C L n t
  have hσn : σ ≤ ((n + 1 : ℕ) : ℝ) := by simpa only [Nat.cast_add, Nat.cast_one] using hσ.2
  have hflow := inverse_flow_block_bounds (hv.euclidean hV) L (n + 1) hL h₁ h₂
    σ (planeCoordinates.symm x) hσ.1 hσn
  have hbound := transported_hessian_bound hg hφ (planeCoordinates.symm x) C L (n + 1)
    hb (by linarith) (detectorBump_euclidean_derivative_bounds hb hb₁ (φ (planeCoordinates.symm x))).1
    (detectorBump_euclidean_derivative_bounds hb hb₁ (φ (planeCoordinates.symm x))).2
    hflow.1 hflow.2
  have he : scalarEuclidean (detectorReference Ψ C L n t) =
      fun y => θ * (g ∘ φ) y := by
    funext y
    simp only [scalarEuclidean, detectorReference, pullbackScalar, g, φ, θ, σ, b,
      euclideanMap, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hθ := smoothRamp_range 0 1
    ((t - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ))
  change θ ∈ Set.Icc (0 : ℝ) 1 at hθ
  have hnorm : ‖fderiv ℝ (fderiv ℝ
      (scalarEuclidean (detectorReference Ψ C L n t))) (planeCoordinates.symm x)‖ ≤
      (C : ℝ) * b⁻¹ ^ 2 * (1 + ((n + 1 : ℕ) : ℝ) * L) *
        (expansion L : ℝ) ^ (3 * (n + 1)) := by
    rw [he, scalar_second_const_mul (hg.comp hφ)]
    apply (ContinuousLinearMap.opNorm_smul_le θ _).trans
    rw [Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hθ.2).trans hbound
  have hlap := scalarLaplacian_bound_of_euclidean_hessian
    ((detectorReference_smooth hback C L n).comp (contDiff_const.prodMk contDiff_id)) x hnorm
  apply hlap.trans_eq
  dsimp only [C, b]
  simp only [laplacianBound, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  ring

end ForcedComputation.VelocityDetector

end

end OAI
