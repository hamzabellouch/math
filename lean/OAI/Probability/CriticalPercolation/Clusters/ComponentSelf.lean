import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.ClusterDeletion
variable {V : Type*}

lemma component_self (H : SimpleGraph V) (s : V) : s ∈ component H s :=
  SimpleGraph.Reachable.refl s

lemma mem_component_symm {H : SimpleGraph V} {s t : V} :
    t ∈ component H s ↔ s ∈ component H t :=
  ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩

lemma roots_singleton (H : SimpleGraph V) (s : V) : roots H {s} = component H s := by
  ext v
  simp [roots, component]

lemma component_eq_of_mem {H : SimpleGraph V} {s t : V}
    (h : t ∈ component H s) : component H t = component H s := by
  ext v
  exact ⟨fun hv => h.trans hv, fun hv => h.symm.trans hv⟩

lemma not_mem_roots_iff_disjoint (H : SimpleGraph V) (S : Set V) (s : V) :
    s ∉ roots H S ↔ Disjoint (component H s) S := by
  rw [Set.disjoint_left]
  constructor
  · intro hs t ht hS
    exact hs ⟨t, hS, ht.symm⟩
  · intro hd ⟨t, ht, hts⟩
    exact hd hts.symm ht

lemma component_delete_component (H : SimpleGraph V) (s t : V)
    (h : t ∉ component H s) :
    component (delete H (component H s)) t = component H t := by
  simpa only [roots_singleton] using
    (delete_roots_component H {s} t (by simpa only [roots_singleton] using h))

lemma roots_delete_component (H : SimpleGraph V) (S : Set V) (s : V)
    (h : s ∉ roots H S) : roots (delete H (component H s)) S = roots H S := by
  ext v
  constructor
  · intro hv
    exact roots_mono (delete_le H _) S hv
  · rintro ⟨t, ht, htv⟩
    refine ⟨t, ht, ?_⟩
    have hts : t ∉ component H s := fun hg => h ⟨t, ht, hg.symm⟩
    change v ∈ component (delete H (component H s)) t
    rw [component_delete_component H s t hts]
    exact htv

lemma delete_empty (H : SimpleGraph V) : delete H ∅ = H := by
  ext v w
  simp only [delete, Set.mem_empty_iff_false, not_false_eq_true, and_true]

lemma component_delete_self (H : SimpleGraph V) (U : Set V) (s : V)
    (hs : s ∈ U) : component (delete H U) s = {s} := by
  ext v
  constructor
  · intro h
    have hadj : ∀ t, ¬ (delete H U).Adj s t := fun t ht => ht.2.1 hs
    have he : v = s := by
      rcases h with ⟨p⟩
      cases p with
      | nil => rfl
      | cons hst _ => exact (hadj _ hst).elim
    exact he
  · rintro rfl
    exact component_self _ _

end CriticalPercolation.ClusterDeletion

end
end

end OAI
