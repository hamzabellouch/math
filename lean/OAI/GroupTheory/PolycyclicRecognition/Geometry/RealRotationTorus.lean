import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealCartanRotations

namespace OAI

/-! # A compact torus of automorphisms preserving the real form

Commuting with the canonical conjugation is a closed subgroup condition.
The resulting compact subgroup contains every real Cartan rotation.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module Set
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

abbrev complexCartanTorus := ComplexCartan.rotationTorus (complexifiedSubalgebra L H)

/-- Those compact diagonal automorphisms which preserve the original real
Lie algebra, expressed by commutation with conjugation. -/
def realRotationTorus : Subgroup (complexCartanTorus L H) where
  carrier := {z | ∀ x : ℂ ⊗[ℝ] L,
    complexificationConjugation L
        (ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val x) =
      ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val
        (complexificationConjugation L x)}
  one_mem' := by simp
  mul_mem' := by
    intro z w hz hw x
    change complexificationConjugation L
      (ComplexCartan.torusOperator _ (z.val * w.val) x) =
      ComplexCartan.torusOperator _ (z.val * w.val) (complexificationConjugation L x)
    rw [ComplexCartan.torusOperator_mul, hz, hw, ComplexCartan.torusOperator_mul]
  inv_mem' := by
    intro z hz x
    change complexificationConjugation L
      (ComplexCartan.torusOperator _ z.val⁻¹ x) =
      ComplexCartan.torusOperator _ z.val⁻¹ (complexificationConjugation L x)
    apply ComplexCartan.torusOperator_injective (complexifiedSubalgebra L H) z.val
    rw [← hz, ← ComplexCartan.torusOperator_mul, mul_inv_cancel,
      ComplexCartan.torusOperator_one, ← ComplexCartan.torusOperator_mul,
      mul_inv_cancel, ComplexCartan.torusOperator_one]

section Topology

local instance complexNormedAddCommGroup : NormedAddCommGroup (ℂ ⊗[ℝ] L) :=
  ComplexCartan.rotationNormedAddCommGroup
local instance complexNormedSpace : NormedSpace ℂ (ℂ ⊗[ℝ] L) :=
  ComplexCartan.rotationNormedSpace
local instance realNormedSpace : NormedSpace ℝ (ℂ ⊗[ℝ] L) :=
  { norm_smul_le := fun r x => by
      rw [← algebraMap_smul ℂ r x, norm_smul]
      simp }

/-- Conjugation commutation cuts out a closed subgroup of the compact torus. -/
theorem realRotationTorus_isClosed : IsClosed (realRotationTorus L H : Set (complexCartanTorus L H)) := by
  change IsClosed {z : complexCartanTorus L H | ∀ x : ℂ ⊗[ℝ] L,
    complexificationConjugation L
      (ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val x) =
    ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val
      (complexificationConjugation L x)}
  rw [ofPred_forall]
  apply isClosed_iInter
  intro x
  have hc : Continuous (complexificationConjugation L) :=
    (complexificationConjugation L).toLinearMap.continuous_of_finiteDimensional
  exact isClosed_eq
    (hc.comp ((ComplexCartan.continuous_torusOperator (complexifiedSubalgebra L H) x).comp
      continuous_subtype_val))
    ((ComplexCartan.continuous_torusOperator (complexifiedSubalgebra L H)
      (complexificationConjugation L x)).comp continuous_subtype_val)

instance realRotationTorus_compactSpace : CompactSpace (realRotationTorus L H) :=
  isCompact_iff_compactSpace.mp (realRotationTorus_isClosed L H).isCompact

end Topology

/-- The genuine rotations by real Cartan parameters lie in the compact
subgroup preserving the real form. -/
def realPhaseVector (h : H) : realRotationTorus L H := by
  refine ⟨ComplexCartan.phaseVector (complexifiedSubalgebra L H) (realCartanInComplex L H h), ?_⟩
  intro x
  change complexificationConjugation L
    (ComplexCartan.rotationLinear (complexifiedSubalgebra L H) (realCartanInComplex L H h) x) =
    ComplexCartan.rotationLinear (complexifiedSubalgebra L H) (realCartanInComplex L H h)
      (complexificationConjugation L x)
  exact complex_rotation_conjugation L H h x

end PolycyclicRecognition

end

end OAI
