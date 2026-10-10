import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.TreePathIntDepth
import OAI.Geometry.HyperbolicGroups.AnnularSeparator
import OAI.Geometry.HyperbolicGroups.PictureBFSSeparator
import OAI.Geometry.HyperbolicGroups.PictureRootSeparator

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D)

/-- A sqrt-cardinality separator of EVERY specified vertex carrier in a
connected literal genus-zero map. Unlike the radius precursor, this has no
tree, diameter, radius, or separator assumption. -/
theorem sqrt_component_separator (hG : M.GenusZero) (hc : M.underlyingGraph.Connected)
    (k : ℕ) (hdegree : ∀ x : D, Fintype.card {y : D // M.face.SameCycle x y} ≤ k)
    (U : Finset M.GraphVertex) :
    ∃ S : Finset M.GraphVertex, S ⊆ U ∧ S.card ≤ (3*k+2)*Nat.sqrt U.card ∧
      ∀ W : Finset M.GraphVertex, W ⊆ U → Disjoint W S →
        (M.underlyingGraph.induce (W : Set M.GraphVertex)).Preconnected →
        2*W.card ≤ U.card := by
  classical
  let root : M.GraphVertex := M.vertexClass (Classical.choice inferInstance)
  obtain ⟨q,hq,hspan,hb,hd⟩ := M.bfs_subpairing hc root
  let T := M.subpairingGraph q (M.subpairing_sq q hq)
  have hT : T.IsTree := M.subpairing_isTree hG q hq hspan hb
  let weight : M.GraphVertex → ℝ := fun v => if v ∈ U then 1 else 0
  have hw : ∀ v, 0 ≤ weight v := by intro v; dsimp [weight]; split_ifs <;> norm_num
  obtain ⟨f,hf⟩ := M.root_path_weighted_separator q hq hG hspan hb root weight hw
  let B := treePathHull T hT root (M.faceCorners f)
  apply sqrt_separator_of_banded_hull M.underlyingGraph U B (M.underlyingGraph.dist root) k
    (graph_dist_int_adj M.underlyingGraph root)
  · intro L H
    have he : ∀ v, M.underlyingGraph.dist root v = T.dist root v := fun v => (hd v).symm
    simp only [he]
    exact (treePathHull_intBand_card_le T hT root (M.faceCorners f) L H).trans
      (Nat.mul_le_mul_right _ (M.faceCorners_card_le k (fun dart => by
        simpa only [← Nat.card_eq_fintype_card] using hdegree dart) f))
  · intro W hWU hWB hconn
    have hh := hf W hWB hconn
    have htotal : ∑ v : M.GraphVertex, weight v = (U.card : ℝ) := by
      simp [weight]
    have hpart : ∑ v ∈ W, weight v = (W.card : ℝ) := by
      calc
        _ = ∑ v ∈ W, (1 : ℝ) := Finset.sum_congr rfl (fun vertex hvertex => ite_eq_left (hWU hvertex))
        _ = _ := by simp
    rw [htotal,hpart] at hh
    exact_mod_cast hh

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
