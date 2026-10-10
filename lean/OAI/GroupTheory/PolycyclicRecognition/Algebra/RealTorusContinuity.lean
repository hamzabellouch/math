import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealTorusAction

namespace OAI

/-! # Continuity of the real compact rotation action -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

theorem realTorusOperator_fixes_cartan (z : realRotationTorus L H) (h : H) :
    realTorusOperator L H z h = h := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] _
  rw [realTorusOperator_complexify]
  exact z.val.property.2 (realCartanInComplex L H h)

/-- Additive Cartan parameters act through the compact rotation group. -/
def realPhaseHom : Multiplicative H →* realRotationTorus L H where
  toFun h := realPhaseVector L H h.toAdd
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    funext χ
    apply Subtype.ext
    change ComplexCartan.phase (complexifiedSubalgebra L H)
      (realCartanInComplex L H 0) χ = 1
    rw [realCartanInComplex_zero, ComplexCartan.phase_zero]
  map_mul' h k := by
    apply Subtype.ext
    apply Subtype.ext
    funext χ
    apply Subtype.ext
    change ComplexCartan.phase (complexifiedSubalgebra L H)
      (realCartanInComplex L H (h.toAdd + k.toAdd)) χ =
        ComplexCartan.phase (complexifiedSubalgebra L H)
          (realCartanInComplex L H h.toAdd) χ *
        ComplexCartan.phase (complexifiedSubalgebra L H)
          (realCartanInComplex L H k.toAdd) χ
    rw [realCartanInComplex_add, ComplexCartan.phase_add]

section Topology
variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

local instance cartanTopologicalAddGroup : IsTopologicalAddGroup H :=
  Submodule.isTopologicalAddGroup H.toSubmodule

local instance actionComplexNormedAddCommGroup : NormedAddCommGroup (ℂ ⊗[ℝ] L) :=
  ComplexCartan.rotationNormedAddCommGroup
local instance actionComplexNormedSpace : NormedSpace ℂ (ℂ ⊗[ℝ] L) :=
  ComplexCartan.rotationNormedSpace
local instance complexRealNormedSpace : NormedSpace ℝ (ℂ ⊗[ℝ] L) :=
  { norm_smul_le := fun r x => by
      rw [← algebraMap_smul ℂ r x, norm_smul]
      simp }

/-- The compact real torus acts jointly continuously on the real algebra. -/
theorem continuous_realTorusOperator :
    Continuous (fun p : realRotationTorus L H × L => realTorusOperator L H p.1 p.2) := by
  have hc : Continuous (fun z : realRotationTorus L H =>
      fun χ : Weight ℂ (complexifiedSubalgebra L H) (ℂ ⊗[ℝ] L) =>
        (z.val.val χ : ℂ)) :=
    continuous_pi (fun χ => continuous_subtype_val.comp
      ((continuous_apply χ).comp (continuous_subtype_val.comp continuous_subtype_val)))
  have hj : Continuous (complexificationLieHom L) :=
    (complexificationLieHom L).toLinearMap.continuous_of_finiteDimensional
  have hr : Continuous (complexificationRealPart L) :=
    (complexificationRealPart L).continuous_of_finiteDimensional
  exact hr.comp
    ((((ComplexCartan.coefficientOperator (complexifiedSubalgebra L H)).continuous_of_finiteDimensional.comp
      hc).comp continuous_fst).clm_apply (hj.comp continuous_snd))

/-- Cartan rotations depend continuously on the real Cartan parameter. -/
theorem continuous_realPhaseVector : Continuous (realPhaseVector L H) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro χ
  let j : H →ₗ[ℝ] complexifiedSubalgebra L H :=
    { toFun := realCartanInComplex L H
      map_add' := realCartanInComplex_add L H
      map_smul' := by
        intro r h
        apply Subtype.ext
        exact (complexificationLieHom L).map_smul r (h : L) }
  let f : H →ₗ[ℝ] ℂ :=
    ((χ : complexifiedSubalgebra L H →ₗ[ℂ] ℂ).restrictScalars ℝ).comp j
  exact Circle.exp.continuous.comp (Complex.continuous_im.comp f.continuous_of_finiteDimensional)

end Topology
end PolycyclicRecognition

end

end OAI
