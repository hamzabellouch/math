import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothing
import OAI.Geometry.Immersion.ClosedSurface.TensorCoordinates
import OAI.Geometry.Immersion.ClosedSurface.ChartModel

namespace OAI

/-! The three independent coordinates of a symmetric surface tensor, with
an explicit continuous linear reconstruction into the full tensor fiber. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean

local instance coordinateFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coordinateFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

local instance coordinateDualAdd : ContinuousAdd (Plane →L[ℝ] ℝ) := inferInstance
local instance coordinateDualSmul : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance coordinateFiberGroup : AddCommGroup (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
  coordinateFiberNormed.toAddCommGroup

def planeFirst : Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp planeCoordinates.toContinuousLinearMap

def planeSecond : Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp planeCoordinates.toContinuousLinearMap

def fiberToThree : TensorFiber →L[ℝ] Tensor :=
  LinearMap.toContinuousLinearMap {
    toFun := fun B k => B (planeCoordinates.symm (firstDirection k))
      (planeCoordinates.symm (secondDirection k))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

lemma fiberToThree_apply (B : TensorFiber) (k : Fin 3) :
    fiberToThree B k = B (planeCoordinates.symm (firstDirection k))
      (planeCoordinates.symm (secondDirection k)) := rfl

def fiberFromThree : Tensor →L[ℝ] TensorFiber :=
  (ContinuousLinearMap.proj 0).smulRight (planeFirst.smulRight planeFirst) +
  (ContinuousLinearMap.proj 1).smulRight
    (planeFirst.smulRight planeSecond + planeSecond.smulRight planeFirst) +
  (ContinuousLinearMap.proj 2).smulRight (planeSecond.smulRight planeSecond)

lemma fiberFromThree_apply (H : Tensor) (v w : Plane) :
    fiberFromThree H v w = evaluate H (planeCoordinates v) (planeCoordinates w) := by
  simp [fiberFromThree, planeFirst, planeSecond, evaluate]
  ring

lemma fiberToThree_fromThree (H : Tensor) : fiberToThree (fiberFromThree H) = H := by
  ext k
  change fiberFromThree H (planeCoordinates.symm (firstDirection k))
    (planeCoordinates.symm (secondDirection k)) = H k
  rw [fiberFromThree_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  fin_cases k <;> simp [evaluate, firstDirection, secondDirection, SmallModes.dx, SmallModes.dy]

lemma plane_basis_expansion (v : Plane) :
    v = (planeCoordinates v).1 • planeCoordinates.symm SmallModes.dx +
      (planeCoordinates v).2 • planeCoordinates.symm SmallModes.dy := by
  apply planeCoordinates.injective
  simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  exact RealModes.base_decomposition (planeCoordinates v)

lemma fiberFromThree_toThree (B : TensorFiber) (hB : ∀ v w, B v w = B w v) :
    fiberFromThree (fiberToThree B) = B := by
  ext v w
  rw [fiberFromThree_apply]
  have hcross := hB (planeCoordinates.symm SmallModes.dy) (planeCoordinates.symm SmallModes.dx)
  conv_rhs => rw [plane_basis_expansion v, plane_basis_expansion w]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  simp only [evaluate, fiberToThree_apply]
  simp only [firstDirection, secondDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]
  dsimp
  rw [hcross]
  ring

lemma fiberFromThree_symmetric (H : Tensor) (v w : Plane) :
    fiberFromThree H v w = fiberFromThree H w v := by
  rw [fiberFromThree_apply, fiberFromThree_apply]
  simp only [evaluate]
  ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
