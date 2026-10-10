import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.BFSTree
import OAI.Geometry.HyperbolicGroups.TreeSubpairingLift
import OAI.Geometry.HyperbolicGroups.PictureRadiusSeparator

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D)

/-- Radius-preserving literal dart-tree producer. The finite graph BFS
construction is lifted without forgetting actual parallel edge copies. -/
theorem bfs_subpairing (hc : M.underlyingGraph.Connected) (root : M.GraphVertex) :
    ∃ q : Perm D, ∃ hq : ∀ x, q x = x ∨ q x = M.edge x,
      SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤ ∧
      cycles (M.vertex*q) = 1 ∧
      ∀ v, (M.subpairingGraph q (M.subpairing_sq q hq)).dist root v =
        M.underlyingGraph.dist root v := by
  obtain ⟨T,hle,hT,hdepth⟩ := exists_bfs_tree M.underlyingGraph hc root
  obtain ⟨q,hq,hspan,hb,he⟩ := M.lift_spanning_tree T hle hT
  exact ⟨q,hq,hspan,hb,fun v => by rw [he]; exact hdepth v⟩

/-- Bounded-radius weighted separator with NO provided tree or separator
assumption: the radius is that of the actual planar graph itself. -/
theorem separator_of_graph_radius (hG : M.GenusZero) (hc : M.underlyingGraph.Connected)
    (k : ℕ) (hdegree : ∀ x : D, Fintype.card {y : D // M.face.SameCycle x y} ≤ k)
    (root : M.GraphVertex) (R : ℕ) (hR : ∀ v, M.underlyingGraph.dist root v ≤ R)
    (weight : M.GraphVertex → ℝ) (hw : ∀ v, 0 ≤ weight v) :
    ∃ S : Finset M.GraphVertex, S.card ≤ k*(R+1) ∧
      ∀ U : Finset M.GraphVertex, Disjoint U S →
        (M.underlyingGraph.induce (U : Set M.GraphVertex)).Preconnected →
        2 * ∑ v ∈ U, weight v ≤ ∑ v : M.GraphVertex, weight v := by
  obtain ⟨q,hq,hspan,hb,hd⟩ := M.bfs_subpairing hc root
  exact M.bounded_radius_weighted_separator q hq hG hspan hb k hdegree root R
    (fun v => (hd v).trans_le (hR v)) weight hw

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
