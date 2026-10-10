import Mathlib
import OAI.Geometry.HyperbolicGroups.TreeHull

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
variable {V : Type*}

/-- The unique actual tree path; uniqueness is proved, not assumed by a
surrogate tree structure. The distance-minimizing library witness fixes it. -/
def rootedTreePath (G : SimpleGraph V) (hG : G.IsTree) (r a : V) : G.Walk r a :=
  (hG.connected.exists_path_of_dist r a).choose

lemma rootedTreePath_isPath (G : SimpleGraph V) (hG : G.IsTree) (r a : V) :
    (rootedTreePath G hG r a).IsPath :=
  (hG.connected.exists_path_of_dist r a).choose_spec.1

lemma rootedTreePath_length (G : SimpleGraph V) (hG : G.IsTree) (r a : V) :
    (rootedTreePath G hG r a).length = G.dist r a :=
  (hG.connected.exists_path_of_dist r a).choose_spec.2

variable [DecidableEq V]

/-- Union of the root paths to a finite collection of terminals. -/
def treePathHull (G : SimpleGraph V) (hG : G.IsTree) (r : V) (A : Finset V) : Finset V :=
  A.biUnion (fun a => (rootedTreePath G hG r a).support.toFinset)

lemma mem_treePathHull {G : SimpleGraph V} {hG : G.IsTree} {r v : V} {A : Finset V} :
    v ∈ treePathHull G hG r A ↔ ∃ a ∈ A, v ∈ (rootedTreePath G hG r a).support := by
  simp only [treePathHull,Finset.mem_biUnion,List.mem_toFinset]

lemma subset_treePathHull (G : SimpleGraph V) (hG : G.IsTree) (r : V) (A : Finset V) :
    A ⊆ treePathHull G hG r A := by
  intro a ha
  exact mem_treePathHull.mpr ⟨a,ha,(rootedTreePath G hG r a).end_mem_support⟩

lemma treePathHull_rootClosed (G : SimpleGraph V) (hG : G.IsTree) (r : V) (A : Finset V) :
    RootClosed G r (treePathHull G hG r A : Set V) := by
  intro v hv w hvw hd
  obtain ⟨a,ha,hva⟩ := mem_treePathHull.mp hv
  let p := rootedTreePath G hG r a
  have hp : p.IsPath := rootedTreePath_isPath G hG r a
  have hw : w ∈ (p.takeUntil v hva).support :=
    tree_closer_neighbor_mem_path hG (p.takeUntil v hva) (hp.takeUntil hva) hvw hd
  exact mem_treePathHull.mpr ⟨a,ha,p.support_takeUntil_subset_support hva hw⟩

/-- The bounded-radius part of the planar-separator size estimate. A face
with at most three distinct corners contributes at most 3*(radius+1)
vertices to its rooted path hull. No bound on the number of other vertices
or on the tree's valence is imposed. -/
theorem treePathHull_card_le (G : SimpleGraph V) (hG : G.IsTree) (r : V) (A : Finset V)
    (R : ℕ) (hR : ∀ a ∈ A, G.dist r a ≤ R) :
    (treePathHull G hG r A).card ≤ A.card * (R+1) := by
  calc
    (treePathHull G hG r A).card ≤ ∑ a ∈ A, (rootedTreePath G hG r a).support.toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ A, (R+1) := by
      apply Finset.sum_le_sum
      intro a ha
      have hh := (rootedTreePath G hG r a).support.toFinset_card_le
      rw [Walk.length_support,rootedTreePath_length] at hh
      exact hh.trans (Nat.add_le_add_right (hR a ha) 1)
    _ = A.card * (R+1) := by simp

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
