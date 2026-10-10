import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.EuclideanReverseVariations
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarVariations

namespace OAI

/-! The Euclidean variational equations are transported from the planar
variational equations by the coordinate isometry. -/

noncomputable section
namespace ForcedComputation
open ShearFlows
open scoped ContDiff

def euclideanLinearOperator : (Plane →L[ℝ] Plane) →L[ℝ]
    (EuclideanPlane →L[ℝ] EuclideanPlane) :=
  (ContinuousLinearMap.compL ℝ EuclideanPlane Plane EuclideanPlane
    planeCoordinates.symm.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℝ EuclideanPlane Plane Plane).flip
      planeCoordinates.toContinuousLinearMap)

@[simp] theorem euclideanLinearOperator_apply (A : Plane →L[ℝ] Plane) :
    euclideanLinearOperator A = euclideanLinear A := rfl

theorem euclideanMap_smooth {f : Plane → Plane} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (euclideanMap f) :=
  planeCoordinates.symm.toContinuousLinearMap.contDiff.comp
    (hf.comp planeCoordinates.toContinuousLinearMap.contDiff)

theorem euclideanMap_second_fderiv {f : Plane → Plane} (hf : ContDiff ℝ ∞ f)
    (x v w : EuclideanPlane) :
    fderiv ℝ (fderiv ℝ (euclideanMap f)) x v w =
      planeCoordinates.symm (fderiv ℝ (fderiv ℝ f) (planeCoordinates x)
        (planeCoordinates v) (planeCoordinates w)) := by
  have he : fderiv ℝ (euclideanMap f) =
      fun y => euclideanLinearOperator (fderiv ℝ f (planeCoordinates y)) := by
    funext y
    exact euclideanMap_fderiv (hf.differentiable (by simp) _)
  rw [he]
  have hd := euclideanLinearOperator.hasFDerivAt.comp x
    (((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) _).hasFDerivAt.comp x
      planeCoordinates.toContinuousLinearMap.hasFDerivAt)
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe] at hd
  rw [hd.fderiv]
  rfl

theorem PlanarVariations.euclidean {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hv : PlanarVariations V Ψ)
    (hV : ∀ t, ContDiff ℝ ∞ (V t)) :
    EuclideanVariations (fun t => euclideanMap (V t))
      (fun a t => euclideanMap (Ψ a t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    funext x
    simp only [euclideanMap, hv.initial, id_eq, ContinuousLinearEquiv.symm_apply_apply]
  · intro a t
    exact euclideanMap_smooth (hv.smooth a t)
  · intro a x v t
    have hd := planeCoordinates.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hv.first a (planeCoordinates x) (planeCoordinates v) t)
    have he : (fun s => fderiv ℝ (euclideanMap (Ψ a s)) x v) =
        fun s => planeCoordinates.symm
          (fderiv ℝ (Ψ a s) (planeCoordinates x) (planeCoordinates v)) := by
      funext s
      rw [euclideanMap_fderiv ((hv.smooth a s).differentiable (by simp) _)]
      rfl
    rw [he]
    simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe] at hd
    convert hd using 1
    rw [euclideanMap_fderiv ((hV (a + t)).differentiable (by simp) _),
      euclideanMap_fderiv ((hv.smooth a t).differentiable (by simp) _)]
    simp only [euclideanLinear, euclideanMap, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  · intro a x v w t
    have hd := planeCoordinates.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hv.second a (planeCoordinates x) (planeCoordinates v) (planeCoordinates w) t)
    have he : (fun s => fderiv ℝ (fderiv ℝ (euclideanMap (Ψ a s))) x v w) =
        fun s => planeCoordinates.symm (fderiv ℝ (fderiv ℝ (Ψ a s))
          (planeCoordinates x) (planeCoordinates v) (planeCoordinates w)) := by
      funext s
      exact euclideanMap_second_fderiv (hv.smooth a s) x v w
    rw [he]
    simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe] at hd
    convert hd using 1
    rw [euclideanMap_fderiv ((hV (a + t)).differentiable (by simp) _),
      euclideanMap_second_fderiv (hv.smooth a t),
      euclideanMap_second_fderiv (hV (a + t))]
    simp_rw [euclideanMap_fderiv ((hv.smooth a t).differentiable (by simp) _)]
    simp only [euclideanLinear, euclideanMap, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, map_add]

end ForcedComputation

end

end OAI
