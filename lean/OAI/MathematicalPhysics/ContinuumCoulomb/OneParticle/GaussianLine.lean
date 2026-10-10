import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GaussianPoincare
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalMode

namespace OAI

/-! Identifying the one-dimensional Euclidean Gaussian form with the real
line. This fixes the normalization and derivative constants for the oscillator. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace ContinuumCoulomb
open LeanBlast.KLS

def gaussianLineEquiv : Space 1 ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toLinearEquiv
  norm_map' x := by
    change ‖x 0‖ = ‖x‖
    have h : ‖x‖^2 = (x 0)^2 := by
      simpa only [Fin.sum_univ_one] using EuclideanSpace.real_norm_sq_eq x
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (x 0),norm_nonneg x,abs_nonneg (x 0)]

@[simp] theorem gaussianLineEquiv_apply (x : Space 1) : gaussianLineEquiv x=x 0 := rfl

theorem gaussianLine_integral (f : ℝ → ℝ) :
    (∫ x : Space 1, f (gaussianLineEquiv x)) = ∫ y : ℝ, f y :=
  gaussianLineEquiv.measurePreserving.integral_comp
    gaussianLineEquiv.toHomeomorph.measurableEmbedding f

theorem gaussianLine_norm_sq (x : Space 1) : ‖x‖^2=(gaussianLineEquiv x)^2 := by
  rw [← gaussianLineEquiv.norm_map,Real.norm_eq_abs,sq_abs]

theorem gaussianLine_gradient_sq {f : ℝ → ℝ} (hf : Differentiable ℝ f) (x : Space 1) :
    ‖gradient (fun y => f (gaussianLineEquiv y)) x‖^2 =
      (deriv f (gaussianLineEquiv x))^2 := by
  have hd := ((hf (gaussianLineEquiv x)).hasDerivAt.hasFDerivAt.comp x
    gaussianLineEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
  change ‖(InnerProductSpace.toDual ℝ (Space 1)).symm
    (fderiv ℝ (f ∘ gaussianLineEquiv) x)‖^2 = _
  rw [hd]
  rw [(InnerProductSpace.toDual ℝ (Space 1)).symm.norm_map]
  have hder : (ContinuousLinearMap.toSpanSingleton ℝ (deriv f (gaussianLineEquiv x))).comp
      gaussianLineEquiv.toContinuousLinearEquiv.toContinuousLinearMap =
      deriv f (gaussianLineEquiv x) • gaussianLineEquiv.toContinuousLinearEquiv.toContinuousLinearMap := by
    ext y
    simp
    ring
  rw [hder,norm_smul,gaussianLineEquiv.norm_toContinuousLinearMap]
  simp [sq_abs]

end ContinuumCoulomb

end

end OAI
