import OAI.Analysis.CircleDomains.Rigidity.SeededMaskedSelection

namespace OAI

/-! Compatibility against the whole ordered selected family implies
admissibility for the same greedy open selection. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem seed_and_selected_subset_ordered_range
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate base π) {T : Type*}
    (data : T → SelectableMaskedCoordinate base π)
    (S : ℕ → Set T) (q : ℕ → Option T)
    (hpref : ∀ n c, c ∈ S n ↔ ∃ k < n, q k = some c) :
    range seed ∪ data '' (⋃ n, S n) ⊆ range (orderedSelectedCoordinates seed data q) := by
  rintro c (⟨n, rfl⟩ | ⟨t, ht, rfl⟩)
  · exact ⟨Sum.inlₗ n, rfl⟩
  · obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    obtain ⟨k, _, hk⟩ := (hpref n t).mp hn
    exact ⟨Sum.inrₗ k, by simp only [orderedSelectedCoordinates, ofLex_toLex, hk, Option.elim_some]⟩

 theorem seeded_allowed_of_ordered_compatible
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate base π) {T : Type*}
    (data : T → SelectableMaskedCoordinate base π)
    (S : ℕ → Set T) (q : ℕ → Option T)
    (hpref : ∀ n c, c ∈ S n ↔ ∃ k < n, q k = some c)
    (t : T) (ht : (data t).CompatibleWith (range (orderedSelectedCoordinates seed data q))) :
    seededMaskedAllowed seed data (⋃ n, S n) t :=
  ht.mono (seed_and_selected_subset_ordered_range seed data S q hpref)

end CircleDomainRigidity

end

end OAI
