import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothing
import Mathlib.Geometry.Manifold.VectorBundle.Hom

namespace OAI

/-! Smooth pointwise inversion for the actual tensor bundle. This is the
local analytic operation used to correct a finite perturbed primitive sum. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing

local instance inverseTensorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inverseTensorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance inverseTensorFiberComplete : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance inverseTensorDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inverseTensorDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance inverseTensorSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inverseTensorSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

private def tensorEndomorphismCoordinates
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (p x : M) :
    TensorFiber →L[ℝ] TensorFiber :=
  ContinuousLinearMap.inCoordinates TensorFiber (CovariantTwoTensor (M := M))
    TensorFiber (CovariantTwoTensor (M := M)) p x p x (A x)

private lemma tensorEndomorphismCoordinates_smoothAt
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (p : M)
    (hA : ContMDiffAt planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun x => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) x (A x)) p) :
    ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber) ∞
      (tensorEndomorphismCoordinates A p) p :=
  (contMDiffAt_hom_bundle
    (fun x => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) x (A x))).mp hA |>.2

private lemma tensorEndomorphismCoordinates_invertible
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (p : M)
    (hinv : (A p).IsInvertible) : (tensorEndomorphismCoordinates A p p).IsInvertible := by
  unfold tensorEndomorphismCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' p)
    (FiberBundle.mem_baseSet_trivializationAt' p)]
  exact ContinuousLinearMap.isInvertible_equiv.comp
    (hinv.comp ContinuousLinearMap.isInvertible_equiv)

private lemma tensorEndomorphismCoordinates_inverse
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (p : M) :
    (fun x => (tensorEndomorphismCoordinates A p x).inverse) =ᶠ[𝓝 p]
      tensorEndomorphismCoordinates (fun x => (A x).inverse) p := by
  filter_upwards [(trivializationAt TensorFiber (CovariantTwoTensor (M := M)) p).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' p)] with x hx
  unfold tensorEndomorphismCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hx hx,ContinuousLinearMap.inCoordinates_eq hx hx]
  simp only [ContinuousLinearMap.inverse_equiv_comp,ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearEquiv.symm_symm]
  rfl

private lemma tensorEndomorphismCoordinates_inverse_smoothAt
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (p : M)
    (hA : ContMDiffAt planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun x => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) x (A x)) p)
    (hinv : (A p).IsInvertible) :
    ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber) ∞
      (tensorEndomorphismCoordinates (fun x => (A x).inverse) p) p := by
  have hc := tensorEndomorphismCoordinates_smoothAt A p hA
  have hi := tensorEndomorphismCoordinates_invertible A p hinv
  exact (hi.contDiffAt_map_inverse.contMDiffAt.comp p hc).congr_of_eventuallyEq
    (tensorEndomorphismCoordinates_inverse A p).symm

/-- A smooth invertible field of tensor endomorphisms sends a smooth target
section to a smooth inverse section. No global trivialization is chosen. -/
theorem tensorBundle_inverse_apply_smooth
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p)
    (hA : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun p => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) p (A p)))
    (hinv : ∀ p, (A p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p ((A p).inverse (u p))) := by
  intro p
  have hc := tensorEndomorphismCoordinates_inverse_smoothAt A p (hA p) (hinv p)
  exact ContMDiffAt.clm_apply_of_inCoordinates (b₁ := id) (b₂ := id)
    (ϕ := fun x => (A x).inverse) (v := u) hc (hu p) contMDiffAt_id

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
