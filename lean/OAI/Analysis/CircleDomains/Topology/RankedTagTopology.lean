import OAI.Analysis.CircleDomains.Topology.TagPairTopology
import OAI.Analysis.CircleDomains.Selection.RankedTuplePairs

namespace OAI

/-! Free tag contacts are excluded by the largest inherited label in a
finite tuple, irrespective of the enumeration used to encode the tuple. -/
open Set Function
open scoped Topology Classical
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem tag_impossible_below_ranked_level
    {I : Type*} [LinearOrder I] (rank : ℕ → I)
    (H : ℕ → Set (UnitAddCircle × X)) (hH : ∀ i, IsClosed (H i))
    (γ : C(PathTime, X)) (q : TagData)
    (hshape : (γ, Sum.inr q) ∈ validTagShape)
    (hcontain : (γ, Sum.inr q) ∈ tagContainment H)
    (t : PathTime) (hl : tagLeft (Sum.inr q) < t) (hr : t < tagRight (Sum.inr q))
    (j : ℕ)
    (hbelow : ∀ k, (q.2.2.1 k, γ t) ∈ H (q.2.1 k) → rank (q.2.1 k) < rank j)
    (hcompat : ∀ A : Finset (Fin (q.1 + 1)), (∀ k ∈ A, rank (q.2.1 k) < rank j) →
      ¬ (connectedComponentIn (⋃ k ∈ A, {x | (q.2.2.1 k, x) ∈ H (q.2.1 k)})
        (γ t)).Nontrivial) : False := by
  let L : Fin (q.1 + 1) → Set X := fun k => {x | (q.2.2.1 k, x) ∈ H (q.2.1 k)}
  let A : Finset (Fin (q.1 + 1)) := Finset.univ.filter (fun k => γ t ∈ L k)
  have hx : γ t ∈ ⋃ k, L k := mem_iUnion.mpr (hcontain t hl hr)
  have hxA : γ t ∈ ⋃ k ∈ A, L k := by
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact mem_iUnion₂.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩, hk⟩
  have he : (⋃ k ∈ (Finset.univ : Finset (Fin (q.1 + 1))),
      ⋃ (_ : γ t ∈ L k), L k) = ⋃ k ∈ A, L k := by
    ext x
    simp only [mem_iUnion, exists_prop, Finset.mem_univ, true_and, A, Finset.mem_filter]
  have hsmall : connectedComponentIn (⋃ k ∈ A, L k) (γ t) = {γ t} :=
    (Set.not_nontrivial_iff.mp (hcompat A (fun k hk =>
      hbelow k (Finset.mem_filter.mp hk).2))).eq_singleton_of_mem (mem_connectedComponentIn hxA)
  have hsingle : connectedComponentIn (⋃ k, L k) (γ t) = {γ t} := by
    have h := component_finite_union_eq_singleton Finset.univ L
      (fun k _ => (hH _).preimage (continuous_const.prodMk continuous_id))
      (by simpa only [Finset.mem_univ, iUnion_true] using hx)
      (by rw [he]; exact hsmall)
    simpa only [Finset.mem_univ, iUnion_true] using h
  have hn := active_tag_nontrivial_component H γ q hshape hcontain t hl hr
  rw [hsingle] at hn
  exact Set.not_nontrivial_singleton hn

theorem incompatible_ranked_tag_pair_at_point
    {I : Type*} [LinearOrder I] (rank : ℕ → I) (hrank : Injective rank)
    (H : ℕ → Set (UnitAddCircle × X)) (hH : ∀ i, IsClosed (H i))
    (γ δ : C(PathTime, X)) (q r : TagData)
    (hqshape : (γ, Sum.inr q) ∈ validTagShape)
    (hrshape : (δ, Sum.inr r) ∈ validTagShape)
    (hqcontain : (γ, Sum.inr q) ∈ tagContainment H)
    (hrcontain : (δ, Sum.inr r) ∈ tagContainment H)
    (t u : PathTime) (htl : tagLeft (Sum.inr q) < t) (htr : t < tagRight (Sum.inr q))
    (hul : tagLeft (Sum.inr r) < u) (hur : u < tagRight (Sum.inr r))
    (heq : δ u = γ t)
    (hunique : ∀ i a b, (a, γ t) ∈ H i → (b, γ t) ∈ H i → a = b)
    (hcross : ∀ i j, q.2.1 i = r.2.1 j → q.2.2.1 i ≠ r.2.2.1 j)
    (hleft : ∀ j, (r.2.2.1 j, γ t) ∈ H (r.2.1 j) →
      ∀ A : Finset (Fin (q.1 + 1)), (∀ k ∈ A, rank (q.2.1 k) < rank (r.2.1 j)) →
        ¬ (connectedComponentIn (⋃ k ∈ A, {x | (q.2.2.1 k, x) ∈ H (q.2.1 k)})
          (γ t)).Nontrivial)
    (hright : ∀ i, (q.2.2.1 i, δ u) ∈ H (q.2.1 i) →
      ∀ A : Finset (Fin (r.1 + 1)), (∀ k ∈ A, rank (r.2.1 k) < rank (q.2.1 i)) →
        ¬ (connectedComponentIn (⋃ k ∈ A, {x | (r.2.2.1 k, x) ∈ H (r.2.1 k)})
          (δ u)).Nontrivial) : False := by
  let L := Finset.univ.filter (fun i : Fin (q.1 + 1) => (q.2.2.1 i, γ t) ∈ H (q.2.1 i))
  let R := Finset.univ.filter (fun j : Fin (r.1 + 1) => (r.2.2.1 j, γ t) ∈ H (r.2.1 j))
  have hL : L.Nonempty := by
    obtain ⟨i, hi⟩ := hqcontain t htl htr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hR : R.Nonempty := by
    have hr' : ∃ j, (r.2.2.1 j, γ t) ∈ H (r.2.1 j) := by
      simpa only [heq, tagLevelGraph, activeTagLevelGraph, mem_ofPred_eq] using hrcontain u hul hur
    obtain ⟨j, hj⟩ := hr'
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨i, hi, hmaxi⟩ := L.exists_max_image (rank ∘ q.2.1) hL
  obtain ⟨j, hj, hmaxj⟩ := R.exists_max_image (rank ∘ r.2.1) hR
  have hqi : (q.2.2.1 i, γ t) ∈ H (q.2.1 i) := (Finset.mem_filter.mp hi).2
  have hrj : (r.2.2.1 j, γ t) ∈ H (r.2.1 j) := (Finset.mem_filter.mp hj).2
  rcases lt_trichotomy (rank (q.2.1 i)) (rank (r.2.1 j)) with hlt | he | hgt
  · apply tag_impossible_below_ranked_level rank H hH γ q hqshape hqcontain t htl htr
      (r.2.1 j) _ (hleft j hrj)
    intro k hk
    exact (hmaxi k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)).trans_lt hlt
  · have heq := hrank he
    exact hcross i j heq (hunique (q.2.1 i) _ _ hqi (heq ▸ hrj))
  · apply tag_impossible_below_ranked_level rank H hH δ r hrshape hrcontain u hul hur
      (q.2.1 i) _ (hright i (heq ▸ hqi))
    intro k hk
    have hk' : (r.2.2.1 k, γ t) ∈ H (r.2.1 k) := heq ▸ hk
    exact (hmaxj k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩)).trans_lt hgt


end CircleDomainRigidity

end

end OAI
