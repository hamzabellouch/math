import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ClassFieldRealization
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ExceptionalUniverse

namespace OAI

/-!
# Unconditional odd-degree exceptional-zero exclusion

Artin reciprocity supplies even ray characters for each cyclic fixed
field in the normal-closure argument.
The resulting zero exclusion is transported to arbitrary universes.
-/

noncomputable section
open scoped NumberField Classical

namespace DukePrimeDegree

universe u

lemma hasCyclicRayRealizations_unconditional
    (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    [NumberField.IsTotallyReal E] : HasCyclicRayRealizations E := by
  intro C hC
  let : IsCyclic C := hC
  let : IsCyclic (E ≃ₐ[IntermediateField.fixedField C] E) :=
    (IntermediateField.subgroupEquivAlgEquiv C).isCyclic.mp hC
  let : NumberField.IsTotallyReal (IntermediateField.fixedField C) :=
    NumberField.IsTotallyReal.of_algebra _ E
  exact exists_cyclic_ray_family_unconditional (IntermediateField.fixedField C) E

/-- Stark's real-zero exclusion in the exact odd-degree form needed by
prime-degree packets. -/
theorem exceptionalRealZeroExclusion_unconditional (d : ℕ) (hodd : Odd (d + 1)) :
    ExceptionalRealZeroExclusion.{u} d :=
  exceptionalRealZeroExclusion_lift d
    (exceptionalRealZeroExclusion_of_ray_realizations d hodd
      hasCyclicRayRealizations_unconditional)

end DukePrimeDegree

end

end OAI
