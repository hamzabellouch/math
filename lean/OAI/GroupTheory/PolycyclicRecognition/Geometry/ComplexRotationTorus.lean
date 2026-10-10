import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexCartanRotations
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Subgroup

namespace OAI

/-! # The compact group containing the Cartan rotations

Diagonal unit scalars are invertible on the generalized weight decomposition.
The equations for preserving the bracket and fixing the Cartan algebra cut out
an actual closed subgroup of a finite torus, giving a compact action.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan

open LieAlgebra LieModule Module Set

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- Linear dependence of a block diagonal operator on its coefficients. -/
def weightOperatorLinear : (Weight ℂ H L → ℂ) →ₗ[ℂ] Module.End ℂ L where
  toFun := weightOperator H
  map_add' z w := by
    ext x
    apply root_induction H (x := x)
    · intro χ v hv
      simp only [LinearMap.add_apply, weightOperator_apply H _ χ hv, Pi.add_apply, add_smul]
    · simp
    · intro v w hv hw
      simp only [map_add, LinearMap.add_apply, hv, hw]
  map_smul' r z := by
    ext x
    apply root_induction H (x := x)
    · intro χ v hv
      simp only [LinearMap.smul_apply, weightOperator_apply H _ χ hv, Pi.smul_apply,
        smul_eq_mul, smul_smul, RingHom.id_apply]
    · simp
    · intro v w hv hw
      simp only [map_add, LinearMap.smul_apply, hv, hw]

/-- A unit diagonal coefficient vector acts on the entire algebra. -/
def torusOperator (z : Weight ℂ H L → Circle) : Module.End ℂ L :=
  weightOperator H (fun χ => (z χ : ℂ))

@[simp] theorem torusOperator_one (x : L) : torusOperator H 1 x = x := by
  apply root_induction H (x := x)
  · intro χ v hv
    rw [torusOperator, weightOperator_apply H _ χ hv]
    simp
  · simp [torusOperator]
  · intro v w hv hw
    simp only [map_add, hv, hw]

@[simp] theorem torusOperator_mul (z w : Weight ℂ H L → Circle) (x : L) :
    torusOperator H (z * w) x = torusOperator H z (torusOperator H w x) := by
  apply root_induction H (x := x)
  · intro χ v hv
    simp only [torusOperator, weightOperator_apply H _ χ hv, Pi.mul_apply, Circle.coe_mul,
      map_smul, smul_smul, mul_comm]
  · simp [torusOperator]
  · intro v w hv hw
    simp only [map_add, hv, hw]

theorem torusOperator_injective (z : Weight ℂ H L → Circle) :
    Function.Injective (torusOperator H z) := by
  intro x y he
  have h := congrArg (torusOperator H z⁻¹) he
  simpa only [← torusOperator_mul, inv_mul_cancel, torusOperator_one] using h

/-- Bracket-preserving unit coefficient vectors that fix the Cartan algebra. -/
def rotationTorus : Subgroup (Weight ℂ H L → Circle) where
  carrier := {z | (∀ x y : L, torusOperator H z ⁅x, y⁆ =
      ⁅torusOperator H z x, torusOperator H z y⁆) ∧
    ∀ h : H, torusOperator H z h = h}
  one_mem' := by simp
  mul_mem' := by
    rintro z w ⟨hz, hzf⟩ ⟨hw, hwf⟩
    constructor
    · intro x y
      rw [torusOperator_mul, hw, hz, torusOperator_mul, torusOperator_mul]
    · intro h
      rw [torusOperator_mul, hwf, hzf]
  inv_mem' := by
    rintro z ⟨hz, hzf⟩
    constructor
    · intro x y
      apply torusOperator_injective H z
      simp only [← torusOperator_mul, mul_inv_cancel, torusOperator_one]
      rw [hz]
      simp only [← torusOperator_mul, mul_inv_cancel, torusOperator_one]
    · intro h
      apply torusOperator_injective H z
      rw [← torusOperator_mul, mul_inv_cancel, torusOperator_one, hzf]

/-- Each element of the compact coefficient group is a Lie automorphism. -/
def torusAutomorphism (z : rotationTorus H) : L ≃ₗ⁅ℂ⁆ L where
  toFun := torusOperator H z.val
  map_add' := (torusOperator H z.val).map_add
  map_smul' := (torusOperator H z.val).map_smul
  invFun := torusOperator H z.val⁻¹
  left_inv x := by rw [← torusOperator_mul, inv_mul_cancel, torusOperator_one]
  right_inv x := by rw [← torusOperator_mul, mul_inv_cancel, torusOperator_one]
  map_lie' := fun {x y} => z.property.1 x y

/-- The genuine Cartan rotations belong to this subgroup. -/
def phaseVector (h : H) : rotationTorus H := by
  let z : Weight ℂ H L → Circle := fun χ => Circle.exp (χ h).im
  have he : torusOperator H z = rotationLinear H h := by
    apply LinearMap.ext
    intro x
    rfl
  refine ⟨z, ?_, ?_⟩
  · intro x y
    rw [he]
    exact rotationLinear_map_lie H h x y
  · intro k
    rw [he, rotationLinear_apply_genWeight H h 0]
    · simp [phase]
    · change (k : L) ∈ rootSpace H 0
      rw [rootSpace_zero_eq]
      exact k.property

section Topology

local instance rotationNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℂ L).equivFun.toLinearMap
    (finBasis ℂ L).equivFun.injective
local instance rotationNormedSpace : NormedSpace ℂ L :=
  NormedSpace.induced ℂ _ _ (finBasis ℂ L).equivFun.toLinearMap

private def bracketOperator : L →L[ℂ] (L →L[ℂ] L) :=
  (show L →ₗ[ℂ] (L →L[ℂ] L) from
    { toFun := fun x => Module.End.toContinuousLinearMap (𝕜 := ℂ) L (LieModule.toEnd ℂ L L x)
      map_add' := by intro x y; ext z; exact add_lie x y z
      map_smul' := by intro c x; ext z; exact smul_lie c x z }).toContinuousLinearMap

/-- The continuous operator associated to the finite coefficient vector. -/
def coefficientOperator : (Weight ℂ H L → ℂ) →ₗ[ℂ] (L →L[ℂ] L) :=
  (LinearMap.toContinuousLinearMap : Module.End ℂ L ≃ₗ[ℂ] (L →L[ℂ] L)).toLinearMap.comp
    (weightOperatorLinear H)

@[simp] theorem coefficientOperator_apply (z : Weight ℂ H L → ℂ) (x : L) :
    coefficientOperator H z x = weightOperator H z x := rfl

theorem continuous_torusOperator (x : L) :
    Continuous (fun z : Weight ℂ H L → Circle => torusOperator H z x) := by
  have hc : Continuous (fun z : Weight ℂ H L → Circle => fun χ => (z χ : ℂ)) :=
    continuous_pi (fun χ => continuous_subtype_val.comp (continuous_apply χ))
  exact ((coefficientOperator H).continuous_of_finiteDimensional.comp hc).clm_apply continuous_const

theorem rotationTorus_isClosed : IsClosed (rotationTorus H : Set (Weight ℂ H L → Circle)) := by
  apply IsClosed.inter
  · change IsClosed {z : Weight ℂ H L → Circle | ∀ x y : L,
        torusOperator H z ⁅x, y⁆ = ⁅torusOperator H z x, torusOperator H z y⁆}
    simp_rw [ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
      isClosed_eq (continuous_torusOperator H ⁅x, y⁆)
        ((bracketOperator.continuous.comp (continuous_torusOperator H x)).clm_apply
          (continuous_torusOperator H y))))
  · change IsClosed {z : Weight ℂ H L → Circle | ∀ h : H, torusOperator H z h = h}
    simp_rw [ofPred_forall]
    exact isClosed_iInter (fun h => isClosed_eq (continuous_torusOperator H h) continuous_const)

instance rotationTorus_compactSpace : CompactSpace (rotationTorus H) :=
  isCompact_iff_compactSpace.mp (rotationTorus_isClosed H).isCompact

end Topology
end PolycyclicRecognition.ComplexCartan

end

end OAI
