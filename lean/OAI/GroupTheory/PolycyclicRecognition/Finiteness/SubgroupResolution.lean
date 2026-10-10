import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteResolutionTruncation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalInductionDimension
import Mathlib.RepresentationTheory.Coinduced

namespace OAI

/-! # Restricting integral resolutions to subgroups

Restriction is exact and preserves projectives. Truncating at a projective
syzygy before restriction gives the cohomological-dimension bound for every
subgroup, without a finite-generation hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

variable {G : Type} [Group G] (H : Subgroup G)

/-- Restrict an actual integral resolution, retaining its augmentation. -/
def subgroupResolution (P : ProjectiveResolution (trivialIntegral G)) :
    ProjectiveResolution (trivialIntegral H) :=
  (Rep.resFunctor H.subtype).mapProjectiveResolution P

/-- Integral cohomological dimension cannot increase on passing to a subgroup. -/
theorem subgroup_cohomologicalDimension_le (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral G) d] :
    HasProjectiveDimensionLE (trivialIntegral H) d := by
  let P := finiteProjectiveResolution (Rep.standardResolution ℤ G) d
  apply projectiveDimension_of_boundedResolution (subgroupResolution H P) d
  intro i hi
  exact (Rep.resFunctor H.subtype).map_isZero
    (finiteTruncation_isZero (Rep.standardResolution ℤ G) d i hi)

theorem HasFiniteIntegralCohomologicalDimension.subgroup
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    HasFiniteIntegralCohomologicalDimension H := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  exact ⟨d, subgroup_cohomologicalDimension_le H d⟩

end PolycyclicRecognition

end

end OAI
