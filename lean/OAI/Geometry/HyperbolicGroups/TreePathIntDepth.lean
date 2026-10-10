import Mathlib
import OAI.Geometry.HyperbolicGroups.TreePathHull

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
variable {V : Type*} [DecidableEq V]

lemma rootedTreePath_depth_injOn (G : SimpleGraph V) (hG : G.IsTree) (r a : V) :
    Set.InjOn (fun v => G.dist r v) ((rootedTreePath G hG r a).support.toFinset : Set V) := by
  intro v hv w hw he
  have hv' := List.mem_toFinset.mp hv
  have hw' := List.mem_toFinset.mp hw
  have hvget := (rootedTreePath G hG r a).getVert_length_takeUntil hv'
  have hwget := (rootedTreePath G hG r a).getVert_length_takeUntil hw'
  rw [tree_path_length_eq_dist hG _ ((rootedTreePath_isPath G hG r a).takeUntil hv')] at hvget
  rw [tree_path_length_eq_dist hG _ ((rootedTreePath_isPath G hG r a).takeUntil hw')] at hwget
  exact hvget.symm.trans ((congrArg (rootedTreePath G hG r a).getVert he).trans hwget)

lemma tree_path_intBand_card_le (G : SimpleGraph V) (hG : G.IsTree) (r a : V) (L H : ℤ) :
    ((rootedTreePath G hG r a).support.toFinset.filter
      (fun v => L ≤ (G.dist r v : ℤ) ∧ (G.dist r v : ℤ) ≤ H)).card ≤ (H-L+1).toNat := by
  classical
  calc
    _ ≤ (Finset.Icc L H).card := by
      apply Finset.card_le_card_of_injOn (fun v => (G.dist r v : ℤ))
      · intro v hv
        exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hv).2
      · intro v hv w hw he
        apply rootedTreePath_depth_injOn G hG r a
          (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1
        change (G.dist r v : ℤ) = (G.dist r w : ℤ) at he
        exact_mod_cast he
    _ = (H-L+1).toNat := by rw [Int.card_Icc]; congr 1; omega

/-- Integer-level version including empty negative BFS levels. -/
theorem treePathHull_intBand_card_le (G : SimpleGraph V) (hG : G.IsTree)
    (r : V) (A : Finset V) (L H : ℤ) :
    ((treePathHull G hG r A).filter
      (fun v => L ≤ (G.dist r v : ℤ) ∧ (G.dist r v : ℤ) ≤ H)).card ≤ A.card*(H-L+1).toNat := by
  classical
  have he : (treePathHull G hG r A).filter
      (fun v => L ≤ (G.dist r v : ℤ) ∧ (G.dist r v : ℤ) ≤ H) =
      A.biUnion (fun a => (rootedTreePath G hG r a).support.toFinset.filter
        (fun v => L ≤ (G.dist r v : ℤ) ∧ (G.dist r v : ℤ) ≤ H)) := by
    ext v
    simp only [Finset.mem_filter,mem_treePathHull,Finset.mem_biUnion,List.mem_toFinset]
    aesop
  rw [he]
  calc
    _ ≤ ∑ a ∈ A, ((rootedTreePath G hG r a).support.toFinset.filter
      (fun v => L ≤ (G.dist r v : ℤ) ∧ (G.dist r v : ℤ) ≤ H)).card := Finset.card_biUnion_le
    _ ≤ ∑ a ∈ A, (H-L+1).toNat :=
      Finset.sum_le_sum (fun a _ => tree_path_intBand_card_le G hG r a L H)
    _ = A.card*(H-L+1).toNat := by simp

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
