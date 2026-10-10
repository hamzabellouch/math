import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilradicalRotationAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAutomorphismAction

namespace OAI

/-! # The compact rotations on the closed nilpotent factor -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  (N : NilpotentLieModel T.kernelIdeal)

/-- The compact rotation on the chosen nilpotent model's tangent algebra. -/
def modelNilradicalRotation (z : realRotationTorus L H) :
    GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier ≃ₗ⁅ℝ⁆
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier :=
  N.equiv.symm.trans ((T.nilradicalRotation H z).trans N.equiv)

@[simp] theorem modelNilradicalRotation_apply (z : realRotationTorus L H)
    (x : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
    modelNilradicalRotation T H N z x =
      N.equiv (T.nilradicalRotation H z (N.equiv.symm x)) := rfl

@[simp] theorem modelNilradicalRotation_one
    (x : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
    modelNilradicalRotation T H N 1 x = x := by
  have h : T.nilradicalRotation H 1 (N.equiv.symm x) = N.equiv.symm x := by
    apply Subtype.ext
    exact realTorusOperator_one L H (N.equiv.symm x)
  rw [modelNilradicalRotation_apply, h, N.equiv.apply_symm_apply]

@[simp] theorem modelNilradicalRotation_mul (z w : realRotationTorus L H)
    (x : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
    modelNilradicalRotation T H N (z * w) x =
      modelNilradicalRotation T H N z (modelNilradicalRotation T H N w x) := by
  have h : T.nilradicalRotation H (z * w) (N.equiv.symm x) =
      T.nilradicalRotation H z (T.nilradicalRotation H w (N.equiv.symm x)) := by
    apply Subtype.ext
    exact realTorusOperator_mul L H z w (N.equiv.symm x)
  simp only [modelNilradicalRotation_apply, N.equiv.symm_apply_apply, h]

/-- The transported linear representation. -/
def modelNilradicalLinearAction : realRotationTorus L H →*
    (GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier ≃ₗ[ℝ]
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) where
  toFun z := (modelNilradicalRotation T H N z).toLinearEquiv
  map_one' := by ext x; exact modelNilradicalRotation_one T H N x
  map_mul' z w := by ext x; exact modelNilradicalRotation_mul T H N z w x

@[simp] theorem modelNilradicalLinearAction_apply (z : realRotationTorus L H)
    (x : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
    modelNilradicalLinearAction T H N z x = modelNilradicalRotation T H N z x := rfl

section Topology
variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

local instance modelKernelTopologicalAddGroup : IsTopologicalAddGroup T.kernelIdeal :=
  Submodule.isTopologicalAddGroup T.kernelIdeal.toSubmodule

theorem continuous_modelNilradicalRotation :
    Continuous (fun p : realRotationTorus L H ×
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier =>
        modelNilradicalRotation T H N p.1 p.2) := by
  have he : Continuous (N.equiv : T.kernelIdeal →
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :=
    N.equiv.toLinearMap.continuous_of_finiteDimensional
  have hi : Continuous (N.equiv.symm :
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → T.kernelIdeal) :=
    N.equiv.symm.toLinearMap.continuous_of_finiteDimensional
  have hr := (T.continuous_nilradicalRotation H).comp
    (continuous_fst.prodMk (hi.comp continuous_snd))
  simpa only [modelNilradicalRotation_apply, Function.comp_def] using he.comp hr

theorem exists_integrated_nilradical_rotations
    (Exp : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier)
    (hExp : IsGroupExponential Exp) :
    ∃ α : realRotationTorus L H →* MulAut N.carrier,
      Continuous (fun p : realRotationTorus L H × N.carrier => α p.1 p.2) ∧
      (∀ (z : realRotationTorus L H) (x : T.kernelIdeal),
        α z (Exp (N.equiv x)) = Exp (N.equiv (T.nilradicalRotation H z x))) ∧
      ∀ z, ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, N.modelSpace)) ∞ (α z) := by
  obtain ⟨α, hα, he, hs⟩ := exists_nilpotent_automorphism_action
    N T.kernelIdeal_nilpotent Exp hExp (modelNilradicalLinearAction T H N)
    (fun z x y => (modelNilradicalRotation T H N z).map_lie x y)
    (continuous_modelNilradicalRotation T H N)
  refine ⟨α, hα, ?_, hs⟩
  intro z x
  have h := he z (N.equiv x)
  simpa only [modelNilradicalLinearAction_apply, modelNilradicalRotation_apply,
    N.equiv.symm_apply_apply] using h

/-- A fixed choice of the integrated compact action. -/
def nilradicalRotations
    (Exp : GroupLieAlgebra (𝓘(ℝ,N.modelSpace)) N.carrier → N.carrier)
    (hExp : IsGroupExponential Exp) : realRotationTorus L H →* MulAut N.carrier :=
  (exists_integrated_nilradical_rotations T H N Exp hExp).choose

theorem continuous_nilradicalRotations
    (Exp : GroupLieAlgebra (𝓘(ℝ,N.modelSpace)) N.carrier → N.carrier)
    (hExp : IsGroupExponential Exp) :
    Continuous (fun p : realRotationTorus L H × N.carrier =>
      nilradicalRotations T H N Exp hExp p.1 p.2) :=
  (exists_integrated_nilradical_rotations T H N Exp hExp).choose_spec.1

theorem nilradicalRotations_exp
    (Exp : GroupLieAlgebra (𝓘(ℝ,N.modelSpace)) N.carrier → N.carrier)
    (hExp : IsGroupExponential Exp) (z : realRotationTorus L H) (x : T.kernelIdeal) :
    nilradicalRotations T H N Exp hExp z (Exp (N.equiv x)) =
      Exp (N.equiv (T.nilradicalRotation H z x)) :=
  (exists_integrated_nilradical_rotations T H N Exp hExp).choose_spec.2.1 z x

end Topology
end PolycyclicRecognition

end

end OAI
