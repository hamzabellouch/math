import Mathlib
import OAI.Geometry.HyperbolicGroups.TreePathHull

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem tree_path_band_card_le (G : SimpleGraph V) (hG : G.IsTree)
    (r a : V) (L H : ℕ) :
    ((rootedTreePath G hG r a).support.toFinset.filter
      (fun v => L ≤ G.dist r v ∧ G.dist r v ≤ H)).card ≤ H+1-L := by
  classical
  let p := rootedTreePath G hG r a
  have hp : p.IsPath := rootedTreePath_isPath G hG r a
  have hsub : (p.support.toFinset.filter (fun v => L ≤ G.dist r v ∧ G.dist r v ≤ H)) ⊆
      (Finset.Icc L H).image p.getVert := by
    intro v hv
    obtain ⟨hv,hd⟩ := Finset.mem_filter.mp hv
    have hvp := List.mem_toFinset.mp hv
    have he := p.getVert_length_takeUntil hvp
    rw [tree_path_length_eq_dist hG _ (hp.takeUntil hvp)] at he
    exact Finset.mem_image.mpr ⟨G.dist r v,Finset.mem_Icc.mpr hd,he⟩
  exact ((Finset.card_le_card hsub).trans Finset.card_image_le).trans_eq (Nat.card_Icc L H)

omit [Fintype V] in
/-- Every root path has at most one vertex at each depth. Thus the part of
k root paths inside a selected BFS band has at most k times its width,
regardless of their total length. This avoids any contraction surrogate. -/
theorem treePathHull_band_card_le (G : SimpleGraph V) (hG : G.IsTree)
    (r : V) (A : Finset V) (L H : ℕ) :
    ((treePathHull G hG r A).filter
      (fun v => L ≤ G.dist r v ∧ G.dist r v ≤ H)).card ≤ A.card*(H+1-L) := by
  classical
  have he : (treePathHull G hG r A).filter
      (fun v => L ≤ G.dist r v ∧ G.dist r v ≤ H) =
      A.biUnion (fun a => (rootedTreePath G hG r a).support.toFinset.filter
        (fun v => L ≤ G.dist r v ∧ G.dist r v ≤ H)) := by
    ext v
    simp only [Finset.mem_filter,mem_treePathHull,Finset.mem_biUnion,List.mem_toFinset]
    aesop
  rw [he]
  calc
    _ ≤ ∑ a ∈ A, ((rootedTreePath G hG r a).support.toFinset.filter
      (fun v => L ≤ G.dist r v ∧ G.dist r v ≤ H)).card := Finset.card_biUnion_le
    _ ≤ ∑ a ∈ A, (H+1-L) := Finset.sum_le_sum (fun a _ => tree_path_band_card_le G hG r a L H)
    _ = A.card*(H+1-L) := by simp

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
