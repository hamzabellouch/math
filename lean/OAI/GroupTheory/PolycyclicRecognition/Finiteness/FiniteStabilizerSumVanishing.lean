import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentationSumExact
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InducedFiniteRationalVanishing
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompleteCohomologyFiniteResolution

namespace OAI

/-! # Direct sums of the finite-stabilizer rational coefficients

The integral projective dimension bound is uniform, so arbitrary direct
sums still have projective dimension at most one. No countability or
finiteness-presentation hypothesis is needed for this base case.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G ι : Type} [Group G]

theorem integralRepresentationSum_projectiveDimension_one (A : ι → Rep.{0} ℤ G)
    (hA : ∀ i, HasProjectiveDimensionLE (A i) 1) :
    HasProjectiveDimensionLE (integralRepresentationSum A) 1 := by
  let : ∀ i, Projective (normalizedSyzygy (A i)) := fun i => by
    apply (projective_iff_hasProjectiveDimensionLE_zero _).mpr
    exact (normalizedSyzygySequence_shortExact (A i)).hasProjectiveDimensionLT_X₁ 1
      (show HasProjectiveDimensionLT (normalizedFreeRepresentation (A i)) 1 from inferInstance)
      (hA i)
  let S := integralRepresentationSumSequence (fun i => normalizedSyzygySequence (A i))
  have hS : S.ShortExact := integralRepresentationSumSequence_shortExact _
    (fun i => normalizedSyzygySequence_shortExact (A i))
  have h₁ : Projective S.X₁ := by
    change Projective (integralRepresentationSum (fun i => normalizedSyzygy (A i)))
    infer_instance
  have h₂ : Projective S.X₂ := by
    change Projective (integralRepresentationSum (fun i => normalizedFreeRepresentation (A i)))
    infer_instance
  let := h₁
  let := h₂
  change HasProjectiveDimensionLE S.X₃ 1
  exact hS.hasProjectiveDimensionLT_X₃ 1
    (show HasProjectiveDimensionLT S.X₁ 1 from inferInstance)
    (hasProjectiveDimensionLT_of_ge S.X₂ 1 2 (by omega))

theorem finiteStabilizerSum_projectiveDimension_one (H : ι → Subgroup G)
    [∀ i, Finite (H i)] :
    HasProjectiveDimensionLE
      (integralRepresentationSum (fun i => Rep.ind (H i).subtype (Rep.trivial ℤ (H i) ℚ))) 1 :=
  integralRepresentationSum_projectiveDimension_one _
    (fun i => finiteSubgroup_induced_rational_projectiveDimension_le_one (H i))

theorem finiteStabilizerSum_completeCohomology (H : ι → Subgroup G)
    [∀ i, Finite (H i)] (p : ℕ) :
    Subsingleton (ShiftedCompletedCohomology p
      (integralRepresentationSum (fun i => Rep.ind (H i).subtype (Rep.trivial ℤ (H i) ℚ)))) := by
  let := finiteStabilizerSum_projectiveDimension_one H
  exact shiftedCompleteCohomology_subsingleton_of_finite_projectiveDimension p _ 1

end PolycyclicRecognition

end

end OAI
