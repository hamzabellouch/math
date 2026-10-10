import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicQuotientRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FinitelyGeneratedLift
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianSubgroupRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Nilpotent

namespace OAI

/-! # Rank bounds for abelian quotients of nilpotent groups

A finite independent family in a quotient lifts inside a finitely generated
nilpotent subgroup. Its lattice quotient is bounded by the cohomological
dimension of that subgroup. No finite generation of the original kernel or
quotient is required.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G A : Type} [Group G] [Group.IsNilpotent G] [CommGroup A]

theorem nilpotent_abelian_quotient_lattice_rank_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (q : G →* A) (hq : Function.Surjective q) (n : ℕ)
    (i : IntegralLatticeGroup n →* A) (hi : Function.Injective i) : n ≤ d := by
  let P := i.range.comap q
  let qP : P →* i.range :=
    { toFun := fun x => ⟨q x, x.property⟩
      map_one' := Subtype.ext q.map_one
      map_mul' := fun x y => Subtype.ext (q.map_mul x y) }
  have hqP : Function.Surjective qP := by
    intro a
    obtain ⟨g, hg⟩ := hq a
    have hgP : g ∈ P := by change q g ∈ i.range; rw [hg]; exact a.property
    exact ⟨⟨g, hgP⟩, Subtype.ext hg⟩
  let e := MonoidHom.ofInjective hi
  let : Group.FG (IntegralLatticeGroup n) := inferInstance
  let : Group.FG i.range := Group.fg_of_surjective e.surjective
  obtain ⟨H, hH, hsurj⟩ := exists_fg_subgroup_surjective qP hqP
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  let := subgroup_cohomologicalDimension_le P d
  let := subgroup_cohomologicalDimension_le H d
  exact (isPolycyclic_of_finitelyGenerated_nilpotent H).lattice_quotient_rank_le d n
    (e.symm.toMonoidHom.comp (qP.comp H.subtype)) (e.symm.surjective.comp hsurj)

theorem nilpotent_abelian_quotient_rank_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (q : G →* A) (hq : Function.Surjective q) : Module.rank ℤ (Additive A) ≤ d := by
  by_contra hd
  have hlt : (d : Cardinal) < Module.rank ℤ (Additive A) := lt_of_not_ge hd
  have hle : ((d + 1 : ℕ) : Cardinal) ≤ Module.rank ℤ (Additive A) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Cardinal.natCast_add_one_le_iff.mpr hlt
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank hle
  have hbound := nilpotent_abelian_quotient_lattice_rank_le d q hq (d + 1)
    (independentLatticeHom b) (independentLatticeHom_injective hb)
  omega

end PolycyclicRecognition

end

end OAI
