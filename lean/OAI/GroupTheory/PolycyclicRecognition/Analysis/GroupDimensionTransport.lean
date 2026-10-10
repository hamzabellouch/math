import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupResolution
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RestrictionEquivalence

namespace OAI

/-! # Integral dimension bounds under embeddings and group isomorphisms -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory

theorem cohomologicalDimension_le_of_equiv {G J : Type} [Group G] [Group J]
    (e : G ≃* J) (d : ℕ) [HasProjectiveDimensionLE (trivialIntegral G) d] :
    HasProjectiveDimensionLE (trivialIntegral J) d := by
  let P := Rep.standardResolution ℤ G
  let R := finiteProjectiveResolution P d
  let F : Rep ℤ G ⥤ Rep ℤ J := Rep.resFunctor e.symm.toMonoidHom
  let : F.IsEquivalence := (restrictionEquivalence ℤ e.symm).isEquivalence_functor
  apply projectiveDimension_of_boundedResolution (F.mapProjectiveResolution R) d
  intro i hi
  exact F.map_isZero (finiteTruncation_isZero P d i hi)

theorem cohomologicalDimension_le_of_injective {G J : Type} [Group G] [Group J]
    (f : G →* J) (hf : Function.Injective f) (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral J) d] :
    HasProjectiveDimensionLE (trivialIntegral G) d := by
  let := subgroup_cohomologicalDimension_le f.range d
  exact cohomologicalDimension_le_of_equiv (MonoidHom.ofInjective hf).symm d

end PolycyclicRecognition

end

end OAI
