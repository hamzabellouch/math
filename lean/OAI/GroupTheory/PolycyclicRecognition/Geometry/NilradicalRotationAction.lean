import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexNilradical
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealTorusContinuity

namespace OAI

/-! # The compact rotation action on the actual nilpotent kernel -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

/-- Restrict the real rotations to the intrinsic nilpotent adjoint kernel. -/
def nilradicalRotation (z : realRotationTorus L H) : T.kernelIdeal ≃ₗ⁅ℝ⁆ T.kernelIdeal where
  toFun x := ⟨realTorusOperator L H z x,
    T.map_mem_kernelIdeal (realTorusAutomorphism L H z) x.property⟩
  invFun x := ⟨realTorusOperator L H z⁻¹ x,
    T.map_mem_kernelIdeal (realTorusAutomorphism L H z⁻¹) x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (realTorusAutomorphism L H z).left_inv x
  right_inv x := by
    apply Subtype.ext
    exact (realTorusAutomorphism L H z).right_inv x
  map_add' x y := by apply Subtype.ext; exact (realTorusOperator L H z).map_add x y
  map_smul' r x := by apply Subtype.ext; exact (realTorusOperator L H z).map_smul r x
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact realTorusOperator_lie L H z x y

/-- The restricted linear representation has the same compact parameter group. -/
def nilradicalLinearAction : realRotationTorus L H →* (T.kernelIdeal ≃ₗ[ℝ] T.kernelIdeal) where
  toFun z := (T.nilradicalRotation H z).toLinearEquiv
  map_one' := by
    ext x
    exact realTorusOperator_one L H x
  map_mul' z w := by
    ext x
    exact realTorusOperator_mul L H z w x

section Topology
variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem continuous_nilradicalRotation :
    Continuous (fun p : realRotationTorus L H × T.kernelIdeal =>
      T.nilradicalRotation H p.1 p.2) :=
  ((continuous_realTorusOperator L H).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

end Topology
end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
