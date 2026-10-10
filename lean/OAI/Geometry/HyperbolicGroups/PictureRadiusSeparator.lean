import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.PictureCotreeTree
import OAI.Geometry.HyperbolicGroups.PictureFaceCorners
import OAI.Geometry.HyperbolicGroups.PictureOutsideColor
import OAI.Geometry.HyperbolicGroups.TreePathHull
import OAI.Geometry.HyperbolicGroups.TreeCentroidComponents
import OAI.Geometry.HyperbolicGroups.FiniteMassTransfer

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D) (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)

/-- Weighted bounded-radius planar separator for LITERAL genus-zero
rotation systems. If faces have at most k sides and a spanning tree has
radius R, at most k*(R+1) actual vertices separate every connected remainder
into mass at most one half. Loops and parallel edges are allowed in the
original map. No planar drawing/separator conclusion is assumed. -/
theorem bounded_radius_weighted_separator (hG : M.GenusZero)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1)
    (k : ℕ) (hdegree : ∀ x : D, Fintype.card {y : D // M.face.SameCycle x y} ≤ k)
    (root : M.GraphVertex) (R : ℕ)
    (hR : ∀ v, (M.subpairingGraph q (M.subpairing_sq q hq)).dist root v ≤ R)
    (weight : M.GraphVertex → ℝ) (hw : ∀ v, 0 ≤ weight v) :
    ∃ S : Finset M.GraphVertex, S.card ≤ k*(R+1) ∧
      ∀ U : Finset M.GraphVertex, Disjoint U S →
        (M.underlyingGraph.induce (U : Set M.GraphVertex)).Preconnected →
        2 * ∑ v ∈ U, weight v ≤ ∑ v : M.GraphVertex, weight v := by
  classical
  let T := M.subpairingGraph q (M.subpairing_sq q hq)
  have hT : T.IsTree := M.subpairing_isTree hG q hq hspan hboundary
  let A : M.GraphVertex → M.dual.GraphVertex :=
    fun v => M.dual.vertexClass (M.vertexRepresentative v)
  let mass := pushMass A weight
  have hm : ∀ f, 0 ≤ mass f := pushMass_nonneg A weight hw
  obtain ⟨f,hf⟩ := weighted_tree_component_separator (M.cotreeGraph q hq)
    (M.cotree_isTree q hq hG hspan hboundary) mass hm
  let S := treePathHull T hT root (M.faceCorners f)
  have hS : S.card ≤ k*(R+1) := by
    calc
      S.card ≤ (M.faceCorners f).card * (R+1) :=
        treePathHull_card_le T hT root (M.faceCorners f) R (fun vertex _ => hR vertex)
      _ ≤ k*(R+1) := Nat.mul_le_mul_right (R+1)
        (M.faceCorners_card_le k (fun dart => by
          simpa only [← Nat.card_eq_fintype_card] using hdegree dart) f)
  refine ⟨S,hS,?_⟩
  intro U hUS hconn
  have hout : ∀ v ∈ U, v ∉ (S : Set M.GraphVertex) := by
    intro v hv hs
    exact Finset.disjoint_left.mp hUS hv hs
  have hbound : ∀ x, M.cotreeColor q hq f (M.edge x) ≠ M.cotreeColor q hq f x →
      M.vertexClass x ∈ (S : Set M.GraphVertex) :=
    M.cotree_color_boundary_in_path_hull q hq hG hspan hboundary root f
  have hcolor := M.vertexColor_connected_outside (M.cotreeColor q hq f)
    (M.cotreeColor_face q hq f) (S : Set M.GraphVertex) hbound
    (U : Set M.GraphVertex) hout hconn
  by_cases hU : U.Nonempty
  · obtain ⟨v,hv⟩ := hU
    let H := (M.cotreeGraph q hq).deleteIncidenceSet f
    let C := H.connectedComponentMk (A v)
    have hAf : A v ≠ f := by
      intro he
      have hcorner := M.corner_mem f (M.vertexRepresentative v) he
      rw [M.vertexClass_representative] at hcorner
      exact hout v hv (subset_treePathHull T hT root (M.faceCorners f) hcorner)
    have hC : C ≠ H.connectedComponentMk f := by
      intro he
      exact hAf ((deleteIncidence_center_component_iff (M.cotreeGraph q hq) f (A v)).mp he)
    have hUC : ∀ w ∈ U, A w ∈ C.supp.toFinset := by
      intro w hwU
      rw [Set.mem_toFinset]
      exact hcolor w hwU v hv
    calc
      2 * ∑ v ∈ U, weight v ≤ 2 * ∑ g ∈ C.supp.toFinset, mass g :=
        mul_le_mul_of_nonneg_left (mass_le_pushMass A weight hw U C.supp.toFinset hUC) (by norm_num)
      _ ≤ ∑ g : M.dual.GraphVertex, mass g := hf C hC
      _ = ∑ v : M.GraphVertex, weight v := pushMass_total A weight
  · rw [Finset.not_nonempty_iff_eq_empty.mp hU]
    simp only [Finset.sum_empty,mul_zero]
    exact Finset.sum_nonneg (fun v _ => hw v)

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
