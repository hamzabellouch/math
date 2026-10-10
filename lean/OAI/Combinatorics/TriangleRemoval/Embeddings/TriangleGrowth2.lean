import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.Attachment
import OAI.Combinatorics.TriangleRemoval.Process.EdgeMatching
import OAI.Combinatorics.TriangleRemoval.Process.OlderSeed

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

lemma root_edges_adj (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G) :
    ∀ e ∈ c.focus, ∀ x ∈ e, ∀ y ∈ e, x ≠ y → (lookupGraph G).Adj x y := by
  intro e he x hx y hy hne
  refine ⟨hne,?_⟩
  have hp : ({x,y} : Finset (Fin n)) = e := Finset.eq_of_subset_of_card_le
    (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hy)
    (by rw [hM.1 e he,Finset.card_pair hne])
  rw [hp]
  exact hG he

noncomputable def toTriangleGrowth (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G) :
    TriangleGrowth (lookupGraph G) F.vertexCount F.rootCount where
  label := F.vertexLabel
  seed := matchingSeed F.vertexLabel c.focus hM F.vertexLabel_injective_roots
  seed_small := fun v _ => matchingSeed_small _ _ _ _ v
  seed_root := fun v u hu _ => matchingSeed_root _ _ _ _ v u hu
  seed_labels := fun v _ u hu => matchingSeed_labels _ _ _ _ (lookupGraph G)
    (root_edges_adj hM hG) v u hu
  roots_injective := F.vertexLabel_injective_roots
  attach := F.attachment
  parent := F.birthParent
  parent_lt := by
    intro v p hv hp
    obtain ⟨hh,rfl⟩ := F.birthParent_some v p hv hp
    have ht := F.birthIndex_lt _ _ hh (F.callIndex_nonroot v hv)
      (F.parent_lt (F.callIndex v hv) (F.callIndex_nonroot v hv))
    simpa only [F.birthIndex_callIndex] using ht
  parent_nonroot := by
    intro v p hv hp
    obtain ⟨hh,rfl⟩ := F.birthParent_some v p hv hp
    exact F.birthIndex_nonroot _ hh
  attach_card := by
    intro v hv
    rw [F.attachment_nonroot v hv]
    exact F.incoming_card _ _
  new_label := by
    intro v hv
    rw [F.attachment_nonroot v hv,F.vertexLabel_nonroot v hv]
    exact (F.newVertex_spec _ _).1
  triangle := by
    intro v hv
    rw [F.newTriangle v hv]
    exact lookupGraph_triangle (F.incoming_graph _ _).2.1
  root_attach := by
    intro v hv hp
    have hm := (F.incoming_graph (F.callIndex v hv) (F.callIndex_nonroot v hv)).1
    rw [F.birthParent_none v hv hp,F.root_eq] at hm
    rw [F.attachment_nonroot v hv]
    exact matchingSeed_covers _ _ _ _ (F.vertexLabel_covers) _ hm
  child_attach := by
    intro v p hv hp
    obtain ⟨hh,rfl⟩ := F.birthParent_some v p hv hp
    rw [F.attachment_nonroot v hv,F.vertexLabel_birth,F.attachment_birth]
    exact ⟨(F.incoming_of_nonroot_parent _ _ hh).1,
      (F.incoming_of_nonroot_parent _ _ hh).2.1⟩
  omission := by
    intro v p hv hp
    obtain ⟨hh,rfl⟩ := F.birthParent_some v p hv hp
    rw [F.newTriangle v hv,F.vertexLabel_birth,F.attachment_birth,
      ← (F.newVertex_spec _ hh).2]
    exact (F.incoming_of_nonroot_parent _ _ hh).2.2
  distinct_children := F.attachments_distinct

theorem toTriangleGrowth_spawnRules (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G) :
    (F.toTriangleGrowth hM hG).birthGraph.SpawnRules (lookupGraph G) F.vertexLabel :=
  (F.toTriangleGrowth hM hG).spawnRules

end SharpTerminalLeave.RecordedCallForest

end

end OAI
