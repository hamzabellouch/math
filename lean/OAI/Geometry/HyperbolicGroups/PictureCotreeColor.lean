import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.PictureUnderlyingGraph
import OAI.Geometry.HyperbolicGroups.PictureDual
import OAI.Geometry.HyperbolicGroups.PictureBoundaryHull
import OAI.Geometry.HyperbolicGroups.TreePathHull

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D)

omit [DecidableEq D] [Fintype D] in
lemma vertexClass_vertex (x : D) : M.vertexClass (M.vertex x) = M.vertexClass x :=
  (M.vertexClass_eq_iff _ _).mpr SameCycle.rfl.apply_left

omit [DecidableEq D] [Fintype D] in
lemma dual_vertexClass_face (x : D) : M.dual.vertexClass (M.face x) = M.dual.vertexClass x := by
  apply (M.dual.vertexClass_eq_iff _ _).mpr
  rw [M.dual_vertex]
  exact SameCycle.rfl.apply_left

/-- The actual corners of a selected dual vertex (primal face). -/
def faceCorners (f : M.dual.GraphVertex) : Finset M.GraphVertex :=
  (Finset.univ.filter (fun x => M.dual.vertexClass x = f)).image M.vertexClass

omit [DecidableEq D] in
lemma corner_mem (f : M.dual.GraphVertex) (x : D) (hx : M.dual.vertexClass x = f) :
    M.vertexClass x ∈ M.faceCorners f :=
  Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩

omit [DecidableEq D] in
lemma corner_opposite_mem (f : M.dual.GraphVertex) (x : D)
    (hx : M.dual.vertexClass (M.edge x) = f) : M.vertexClass x ∈ M.faceCorners f := by
  have hh := M.corner_mem f (M.face (M.edge x)) ((M.dual_vertexClass_face _).trans hx)
  change M.vertexClass (M.vertex x) ∈ M.faceCorners f at hh
  rwa [M.vertexClass_vertex] at hh

variable (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)

def cotreeGraph : SimpleGraph M.dual.GraphVertex :=
  M.dual.subpairingGraph (q*M.edge) (M.subpairing_sq (q*M.edge) (M.complement_subpairing q hq))

/-- Colors are ACTUAL components of the complementary dual graph after
isolating one specified face; the face itself receives its isolated color. -/
def cotreeColor (f : M.dual.GraphVertex) (x : D) :
    ((M.cotreeGraph q hq).deleteIncidenceSet f).ConnectedComponent :=
  ((M.cotreeGraph q hq).deleteIncidenceSet f).connectedComponentMk (M.dual.vertexClass x)

omit [DecidableEq D] [Fintype D] in
lemma cotreeColor_face (f : M.dual.GraphVertex) (x : D) :
    M.cotreeColor q hq f (M.face x) = M.cotreeColor q hq f x := by
  unfold cotreeColor
  rw [M.dual_vertexClass_face]

omit [DecidableEq D] [Fintype D] in
lemma cotreeColor_fixed_edge (f : M.dual.GraphVertex) (x : D)
    (hx : q x = x) (hf : M.dual.vertexClass x ≠ f)
    (he : M.dual.vertexClass (M.edge x) ≠ f) :
    M.cotreeColor q hq f (M.edge x) = M.cotreeColor q hq f x := by
  by_cases hc : M.dual.vertexClass x = M.dual.vertexClass (M.edge x)
  · exact congrArg (((M.cotreeGraph q hq).deleteIncidenceSet f).connectedComponentMk) hc.symm
  · apply SimpleGraph.ConnectedComponent.sound
    apply SimpleGraph.Adj.reachable
    apply SimpleGraph.deleteIncidenceSet_adj.mpr
    refine ⟨?_,he,hf⟩
    apply SimpleGraph.Adj.symm
    refine ⟨hc,x,rfl,?_⟩
    rw [mul_apply,M.subpairing_edge q hq,hx]

variable [Nonempty D]

/-- The rooted paths to the corners of a dual-tree vertex contain every
edge across which the associated deleted-dual-component color changes.
Unlike an abstract Jordan-curve assumption, this follows from the exact
rotation permutations, genus-zero Euler formula and tree copy counts. -/
theorem cotree_color_boundary_in_path_hull (hG : M.GenusZero)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1) (root : M.GraphVertex)
    (f : M.dual.GraphVertex) :
    ∀ x, M.cotreeColor q hq f (M.edge x) ≠ M.cotreeColor q hq f x →
      M.vertexClass x ∈ treePathHull (M.subpairingGraph q (M.subpairing_sq q hq))
        (M.subpairing_isTree hG q hq hspan hboundary) root (M.faceCorners f) := by
  apply M.face_color_boundary_in_hull q hq hG hspan hboundary root _
    (treePathHull_rootClosed _ _ root _) (M.cotreeColor q hq f) (M.cotreeColor_face q hq f)
  intro x hx hc
  by_cases hf : M.dual.vertexClass x = f
  · exact subset_treePathHull _ _ _ _ (M.corner_mem f x hf)
  · by_cases he : M.dual.vertexClass (M.edge x) = f
    · exact subset_treePathHull _ _ _ _ (M.corner_opposite_mem f x he)
    · exact (hc (M.cotreeColor_fixed_edge q hq f x hx hf he)).elim

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
