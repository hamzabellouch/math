import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Model

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation

lemma blockSubgroup_commute {X : Type*} {M N : Set X} (h : Disjoint M N)
    {g k : Equiv.Perm X} (hg : g ∈ blockSubgroup M) (hk : k ∈ blockSubgroup N) :
    Commute g k := by
  apply Equiv.Perm.Disjoint.commute
  intro x
  by_cases hx : x ∈ M
  · right
    exact hk x (fun hn => Set.disjoint_left.mp h hx hn)
  · exact Or.inl (hg x hx)

lemma jointFactors_generate {G : Type*} [Group G] {b : ℕ} (H : Fin b → Subgroup G) :
    ⨆ i, (H i).subgroupOf (⨆ j, H j) = ⊤ := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_iSup]
  simp only [Subgroup.map_subgroupOf_eq_of_le (le_iSup H _),
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

lemma jointFactors_commute {G : Type*} [Group G] {b : ℕ} (H : Fin b → Subgroup G)
    (h : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k) :
    ∀ i j, i ≠ j → ∀ g ∈ (H i).subgroupOf (⨆ j, H j),
      ∀ k ∈ (H j).subgroupOf (⨆ j, H j), Commute g k := by
  intro i j hij g hg k hk
  apply Subtype.ext
  exact h i j hij g hg k hk

end PartialPermutation

end

end OAI
