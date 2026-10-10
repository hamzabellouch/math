import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubgroupInductionExact
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedSyzygyFunctor
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

namespace OAI

/-! # Exact subgroup induction preserves finite projective-dimension bounds -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (H : Subgroup G)

theorem subgroupInduction_projectiveDimension_le (A : Rep.{0} ℤ H) (d : ℕ)
    (hA : HasProjectiveDimensionLE A d) :
    HasProjectiveDimensionLE (Rep.ind H.subtype A) d := by
  induction d generalizing A with
  | zero =>
    have hp : Projective A := (projective_iff_hasProjectiveDimensionLE_zero A).mpr hA
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp
      ((Rep.indFunctor ℤ H.subtype).projective_obj_of_projective hp)
  | succ d ih =>
    let S := normalizedSyzygySequence A
    have hS := normalizedSyzygySequence_shortExact A
    have hk : HasProjectiveDimensionLE (normalizedSyzygy A) d :=
      hS.hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge (normalizedFreeRepresentation A) 1 (d + 1) (by omega)) hA
    have hki := ih (normalizedSyzygy A) hk
    let F := Rep.indFunctor ℤ H.subtype
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    have hFS := hS.map F
    let : Projective (F.obj (normalizedFreeRepresentation A)) :=
      F.projective_obj_of_projective (inferInstance : Projective (normalizedFreeRepresentation A))
    exact hFS.hasProjectiveDimensionLT_X₃ (d + 1) hki
      (hasProjectiveDimensionLT_of_ge (F.obj (normalizedFreeRepresentation A)) 1 (d + 2) (by omega))

end PolycyclicRecognition

end

end OAI
