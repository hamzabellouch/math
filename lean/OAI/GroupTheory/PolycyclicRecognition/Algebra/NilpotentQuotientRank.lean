import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentGeneratorRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAbelianQuotientRank

namespace OAI

/-! # Uniform rank bounds persist in nilpotent quotients

The inverse image of a subgroup need not be finitely generated. For the
generator bound we lift only a finite generating set. The abelian rank bound
uses the full inverse image and needs no finite-generation assumption.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G Q : Type} [Group G] [Group.IsNilpotent G] [Group Q]

def quotientSubgroupMap (q : G →* Q) (K : Subgroup Q) : K.comap q →* K where
  toFun g := ⟨q g, g.property⟩
  map_one' := Subtype.ext q.map_one
  map_mul' x y := Subtype.ext (q.map_mul x y)

omit [Group.IsNilpotent G] in
theorem quotientSubgroupMap_surjective (q : G →* Q) (hq : Function.Surjective q)
    (K : Subgroup Q) : Function.Surjective (quotientSubgroupMap q K) := by
  intro k
  obtain ⟨g, hg⟩ := hq k
  have hgK : g ∈ K.comap q := by change q g ∈ K; rw [hg]; exact k.property
  exact ⟨⟨g, hgK⟩, Subtype.ext hg⟩

theorem nilpotent_quotient_subgroup_generator_rank_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (q : G →* Q) (hq : Function.Surjective q) (K : Subgroup Q) [Group.FG K] :
    Group.rank K ≤ d := by
  obtain ⟨H, hH, hs⟩ := exists_fg_subgroup_surjective
    (quotientSubgroupMap q K) (quotientSubgroupMap_surjective q hq K)
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  let := subgroup_cohomologicalDimension_le (K.comap q) d
  exact (Group.rank_le_of_surjective _ hs).trans (nilpotent_subgroup_generator_rank_le d H)

theorem nilpotent_quotient_abelian_subgroup_rank_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (q : G →* Q) (hq : Function.Surjective q) (K : Subgroup Q) [IsMulCommutative K] :
    Module.rank ℤ (Additive K) ≤ d := by
  let := subgroup_cohomologicalDimension_le (K.comap q) d
  exact nilpotent_abelian_quotient_rank_le d (quotientSubgroupMap q K)
    (quotientSubgroupMap_surjective q hq K)

end PolycyclicRecognition

end

end OAI
