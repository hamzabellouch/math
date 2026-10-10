import Mathlib
import OAI.Combinatorics.KMedian.Process.HeavyActions

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential FiniteGraph
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

noncomputable def balancedActions (D : Actions I E) (Δ : ℕ) : Finset E :=
  D.ordinary.filter (fun e => (D.erase e).card=Δ)

noncomputable def balancedConflicts (D : Actions I E) (Δ : ℕ) (e : E) : Finset E :=
  if e ∈ balancedActions D Δ then conflicts D.erase (balancedActions D Δ) e else ∅

omit [Fintype I] in
 theorem balancedConflicts_bound (D : Actions I E) (Δ : ℕ)
    (hin : ∀ i, (incoming D.erase i).card ≤ Δ) (e : E) :
    (balancedConflicts D Δ e).card ≤ Δ^2 := by
  unfold balancedConflicts
  split_ifs with he
  · apply conflicts_card _ _ _ (le_of_eq (mem_filter.mp he).2)
    intro i _
    exact hin i
  · simp

omit [Fintype I] in
 theorem balancedConflicts_self (D : Actions I E) (Δ : ℕ) (e : E) :
    e ∉ balancedConflicts D Δ e := by
  unfold balancedConflicts
  split_ifs
  · exact self_not_conflict _ _ _
  · simp

theorem heavy_incoming_card (G : I → Finset I) (H : Finset I) (i : I) :
    (incoming (heavyActions (graphActions G) H).erase i).card=(G i).card := by
  apply card_bij (fun e _ => heavyParent (graphActions G) H e)
  · intro e he
    have hi := (mem_filter.mp he).2
    have hu := heavy_partition_union (graphActions G) H (heavyParent (graphActions G) H e)
    have hic : i ∈ (graphActions G).erase (heavyParent (graphActions G) H e) := by
      rw [← hu]
      exact mem_biUnion.mpr ⟨e,mem_filter.mpr ⟨mem_univ _,rfl⟩,hi⟩
    exact (mem_graph_erase _ _ _).mp hic
  · intro e he f hf heq
    exact same_parent_eraser (graphActions G) H e f heq (mem_filter.mp he).2 (mem_filter.mp hf).2
  · intro h hh
    have hh' := (mem_graph_erase G h i).mpr hh
    rw [← heavy_partition_union (graphActions G) H h] at hh'
    obtain ⟨e,he,hi⟩ := mem_biUnion.mp hh'
    exact ⟨e,mem_filter.mpr ⟨mem_univ _,hi⟩,(mem_filter.mp he).2⟩

 theorem full_incoming_card (G : I → Finset I) (i : I) :
    (incoming (graphActions G).erase i).card=(G i).card := by
  congr 1
  ext h
  simp [incoming,mem_graph_erase]

 theorem heavy_relevant_bound (G : I → Finset I) (H S : Finset I) {Δ : ℕ}
    (hS : S.card ≤ Δ) (hG : ∀ i, (G i).card=Δ) :
    (relevant (heavyActions (graphActions G) H) S).card ≤ Δ^2+Δ := by
  apply relevant_card_bound _ _ hS (heavy_ordinary_injective G H)
  intro i _
  exact le_of_eq ((heavy_incoming_card G H i).trans (hG i))

 theorem full_relevant_bound (G : I → Finset I) (S : Finset I) {Δ : ℕ}
    (hS : S.card ≤ Δ) (hG : ∀ i, (G i).card=Δ) :
    (relevant (graphActions G) S).card ≤ Δ^2+Δ := by
  apply relevant_card_bound _ _ hS (fun _ _ _ _ h => h)
  intro i _
  exact le_of_eq ((full_incoming_card G i).trans (hG i))

 theorem nonordinary_parent_heavy (G : I → Finset I) (H : Finset I)
    (e : HeavyAction (graphActions G) H) (he : e ∉ (heavyActions (graphActions G) H).ordinary) :
    (heavyActions (graphActions G) H).source e ∈ H := by
  apply (heavyParent_membership _ _ e).mpr
  simpa only [ordinary_heavyActions] using he

end MetricKMedian.FixedBatch
end
end

end OAI
