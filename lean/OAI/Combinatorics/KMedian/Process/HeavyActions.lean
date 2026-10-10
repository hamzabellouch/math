import Mathlib
import OAI.Combinatorics.KMedian.Process.SourceGenerator
import OAI.Combinatorics.KMedian.Process.ActionDegrees

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I : Type*} [DecidableEq I] [Fintype I]

abbrev HeavyAction (Full : Actions I I) (H : Finset I) :=
  {h : I // h ∉ H} ⊕ {p : I × I // p.1 ∈ H ∧ p.2 ∈ Full.erase p.1}

instance (Full : Actions I I) (H : Finset I) : Fintype (HeavyAction Full H) := by
  unfold HeavyAction
  infer_instance

instance (Full : Actions I I) (H : Finset I) : DecidableEq (HeavyAction Full H) := by
  unfold HeavyAction
  infer_instance

def heavyParent (Full : Actions I I) (H : Finset I) : HeavyAction Full H → I
  | .inl h => h
  | .inr p => p.val.1

noncomputable def heavyActions (Full : Actions I I) (H : Finset I) : Actions I (HeavyAction Full H) := by
  classical
  exact {
    source := fun e => Full.source (heavyParent Full H e)
    erase := Sum.elim (fun h => Full.erase h) (fun p => {p.val.2})
    ordinary := univ.filter (fun e : HeavyAction Full H => e.isLeft = true) }

 theorem ordinary_heavyActions (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    e ∈ (heavyActions Full H).ordinary ↔ e.isLeft := by simp [heavyActions]

omit [Fintype I] in
 theorem heavyParent_membership (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    heavyParent Full H e ∈ H ↔ ¬ e.isLeft := by
  cases e with
  | inl h => simp [heavyParent, h.property]
  | inr p => simp [heavyParent, p.property.1]

 theorem same_parent_eraser (Full : Actions I I) (H : Finset I)
    (e f : HeavyAction Full H) {i : I}
    (hpar : heavyParent Full H e=heavyParent Full H f)
    (he : i ∈ (heavyActions Full H).erase e) (hf : i ∈ (heavyActions Full H).erase f) : e=f := by
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (Subtype.ext hpar)
    | inr f =>
      change e.val=f.val.1 at hpar
      exact (e.property (hpar.symm ▸ f.property.1)).elim
  | inr e =>
    cases f with
    | inl f =>
      change e.val.1=f.val at hpar
      exact (f.property (hpar ▸ e.property.1)).elim
    | inr f =>
      have he' : i=e.val.2 := mem_singleton.mp he
      have hf' : i=f.val.2 := mem_singleton.mp hf
      exact congrArg Sum.inr (Subtype.ext (Prod.ext hpar (he'.symm.trans hf')))

 theorem heavy_partition_disjoint (Full : Actions I I) (H : Finset I) (h : I) :
    (↑(univ.filter (fun e => heavyParent Full H e=h)) : Set (HeavyAction Full H)).PairwiseDisjoint
      (heavyActions Full H).erase := by
  intro e he f hf hne
  apply disjoint_left.mpr
  intro i hie hif
  exact hne (same_parent_eraser Full H e f
    ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm) hie hif)

 theorem heavy_partition_union (Full : Actions I I) (H : Finset I) (h : I) :
    (univ.filter (fun e => heavyParent Full H e=h)).biUnion (heavyActions Full H).erase=Full.erase h := by
  ext i
  simp only [mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hi⟩
    cases e with
    | inl e => exact he ▸ hi
    | inr e =>
      change e.val.1=h at he
      have hi' : i=e.val.2 := mem_singleton.mp hi
      exact he ▸ (hi'.symm ▸ e.property.2)
  · intro hi
    by_cases hh : h ∈ H
    · exact ⟨.inr ⟨(h,i), hh, hi⟩, rfl, mem_singleton_self _⟩
    · exact ⟨.inl ⟨h,hh⟩, rfl, hi⟩

 theorem heavy_nonheavy_fiber (Full : Actions I I) (H : Finset I) {h : I} (hh : h ∉ H) :
    univ.filter (fun e => heavyParent Full H e=h)=({Sum.inl ⟨h,hh⟩} : Finset (HeavyAction Full H)) := by
  classical
  apply Finset.ext
  intro e
  rw [Finset.mem_singleton]
  simp only [mem_filter, mem_univ, true_and]
  cases e with
  | inl e => simp only [heavyParent, Sum.inl.injEq, Subtype.ext_iff]
  | inr e =>
    constructor
    · intro he
      change e.val.1=h at he
      exact (hh (he ▸ e.property.1)).elim
    · intro he
      cases he

theorem heavy_charge_le (G : I → Finset I) (H S : Finset I)
    (hHS : Disjoint H S) (x g b : ℝ) (d : I → ℝ)
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i) :
    (∑ e ∈ relevant (heavyActions (graphActions G) H) S,
      charge (heavyActions (graphActions G) H) x g b d S e) ≤
    ∑ h ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S h := by
  apply split_actions_le _ _ (heavyParent (graphActions G) H) x g b d S hg hd
    (heavy_partition_disjoint _ _) (heavy_partition_union _ _) (fun _ => rfl)
  · intro e
    rw [ordinary_heavyActions]
    constructor
    · rintro ⟨_, hs⟩
      exact ⟨mem_univ _, hs⟩
    · rintro ⟨_, hs⟩
      refine ⟨?_, hs⟩
      by_contra he
      exact disjoint_left.mp hHS ((heavyParent_membership _ _ e).mpr he) hs
  · intro h hh
    have hn : h ∉ H := fun he => disjoint_left.mp hHS he hh.2
    exact ⟨_, heavy_nonheavy_fiber _ _ hn⟩

 theorem heavy_incoming_degree (G : I → Finset I) (H : Finset I) (Δ : ℕ)
    (hG : ∀ i, (G i).card ≤ Δ) (i : I) :
    (FiniteGraph.incoming (heavyActions (graphActions G) H).erase i).card ≤ Δ := by
  have hh := split_incoming_bound (heavyActions (graphActions G) H) (graphActions G)
    (heavyParent (graphActions G) H) (heavy_partition_disjoint _ _) (heavy_partition_union _ _) i
  have he : FiniteGraph.incoming (graphActions G).erase i=G i := by
    ext h
    simp [FiniteGraph.incoming, mem_graph_erase]
  rw [he] at hh
  exact hh.trans (hG i)

 theorem heavy_ordinary_injective (G : I → Finset I) (H : Finset I) :
    Set.InjOn (heavyActions (graphActions G) H).source
      (↑(heavyActions (graphActions G) H).ordinary : Set (HeavyAction (graphActions G) H)) := by
  intro e he f hf hpar
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (Subtype.ext hpar)
    | inr f => simp [heavyActions] at hf
  | inr e => simp [heavyActions] at he

end MetricKMedian.FixedBatch
end
end

end OAI
