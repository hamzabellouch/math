import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureEuler
import OAI.Geometry.HyperbolicGroups.ColoredApex
import OAI.Geometry.HyperbolicGroups.PictureUnderlyingGraph
import OAI.Geometry.HyperbolicGroups.PicturePlanarSeparator

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion SimpleGraph
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D) (C : M.underlyingGraph.ConnectedComponent)

def componentDarts (x : D) : Prop := M.vertexClass x ∈ C.supp

omit [DecidableEq D] in
lemma componentDarts_face (x : D) : M.componentDarts C (M.face x) ↔ M.componentDarts C x := by
  have hh := ConnectedComponent.sound ((M.underlying_reachable_iff (M.face x) x).mpr
    (M.face_le_components SameCycle.rfl.apply_left))
  change M.underlyingGraph.connectedComponentMk (M.vertexClass (M.face x)) = C ↔
    M.underlyingGraph.connectedComponentMk (M.vertexClass x) = C
  rw [hh]

omit [DecidableEq D] in
lemma componentDarts_edge (x : D) : M.componentDarts C (M.edge x) ↔ M.componentDarts C x := by
  have hh := ConnectedComponent.sound ((M.underlying_reachable_iff (M.edge x) x).mpr
    (M.edge_le_components SameCycle.rfl.apply_left))
  change M.underlyingGraph.connectedComponentMk (M.vertexClass (M.edge x)) = C ↔
    M.underlyingGraph.connectedComponentMk (M.vertexClass x) = C
  rw [hh]

def componentPicture : PictureMap {x : D // M.componentDarts C x} :=
  M.restrict (M.componentDarts C) (M.componentDarts_face C) (M.componentDarts_edge C)

lemma componentPicture_genusZero (hG : M.GenusZero) : (M.componentPicture C).GenusZero :=
  M.restrict_genusZero _ hG _ _

omit [DecidableEq D] in
lemma componentPicture_cycle (x y : {x : D // M.componentDarts C x}) :
    (M.componentPicture C).vertex.SameCycle x y ↔ M.vertex.SameCycle x.val y.val := by
  unfold componentPicture
  rw [M.restrict_vertex]
  exact sameCycle_subtypePerm_iff _ _ x y

instance componentDarts_nonempty : Nonempty {x : D // M.componentDarts C x} := by
  obtain ⟨v,hv⟩ := C.connected_toSimpleGraph.nonempty
  obtain ⟨x,hx⟩ := Quotient.exists_rep v
  change M.vertexClass x = v at hx
  exact ⟨⟨x,by change M.vertexClass x ∈ C.supp; rw [hx]; exact hv⟩⟩

omit [DecidableEq D] in
lemma componentPicture_connected : (M.componentPicture C).underlyingGraph.Connected := by
  have : Nonempty (M.componentPicture C).GraphVertex :=
    ⟨(M.componentPicture C).vertexClass (Classical.choice (M.componentDarts_nonempty C))⟩
  apply Connected.mk
  intro v w
  induction v using Quotient.inductionOn with | _ x =>
    induction w using Quotient.inductionOn with | _ y =>
      apply ((M.componentPicture C).underlying_reachable_iff x y).mpr
      change (M.restrict (M.componentDarts C) _ _).components x y
      rw [M.restrict_components]
      exact (M.underlying_reachable_iff x.val y.val).mp
        (C.reachable_of_mem_supp x.property y.property)

/-- Original graph-component vertices are carried to the actual restricted
rotation system, using representatives only to define the quotient map. -/
def componentVertex (v : C.supp) : (M.componentPicture C).GraphVertex :=
  (M.componentPicture C).vertexClass ⟨M.vertexRepresentative v.val,by
    change M.vertexClass (M.vertexRepresentative v.val) ∈ C.supp
    rw [M.vertexClass_representative]
    exact v.property⟩

omit [DecidableEq D] in
lemma componentVertex_class (x : D) (hx : M.componentDarts C x) :
    M.componentVertex C ⟨M.vertexClass x,hx⟩ =
      (M.componentPicture C).vertexClass ⟨x,hx⟩ := by
  apply Quotient.sound
  apply (M.componentPicture_cycle C _ _).mpr
  exact Quotient.exact (M.vertexClass_representative (M.vertexClass x))

omit [DecidableEq D] in
lemma componentVertex_injective : Function.Injective (M.componentVertex C) := by
  intro v w h
  apply Subtype.ext
  have hh := (M.componentPicture_cycle C _ _).mp (Quotient.exact h)
  have he : M.vertexClass (M.vertexRepresentative v.val) =
      M.vertexClass (M.vertexRepresentative w.val) := Quotient.sound hh
  simpa only [M.vertexClass_representative] using he

def componentHom : C.toSimpleGraph →g (M.componentPicture C).underlyingGraph where
  toFun := M.componentVertex C
  map_rel' := by
    intro v w h
    obtain ⟨hne,x,hx,he⟩ := h
    have hxp : M.componentDarts C x := by change M.vertexClass x ∈ C.supp; rw [hx]; exact v.property
    have hep : M.componentDarts C (M.edge x) := by change M.vertexClass (M.edge x) ∈ C.supp; rw [he]; exact w.property
    have hxv : (⟨M.vertexClass x,hxp⟩ : C.supp) = v := Subtype.ext hx
    have hew : (⟨M.vertexClass (M.edge x),hep⟩ : C.supp) = w := Subtype.ext he
    refine ⟨fun hh => hne (congrArg Subtype.val (M.componentVertex_injective C hh)),⟨x,hxp⟩,?_,?_⟩
    · rw [← hxv,M.componentVertex_class]
    · rw [← hew,M.componentVertex_class]
      rfl

/-- Every graph component has the separator produced by its literal
restricted genus-zero map. In particular no embedding of an induced graph
is being assumed. -/
theorem graph_component_separator (hG : M.GenusZero) (U : Finset C.supp) :
    ∃ S : Finset C.supp, S ⊆ U ∧ S.card ≤ 11*Nat.sqrt U.card ∧
      ∀ W : Finset C.supp, W ⊆ U → Disjoint W S →
        (C.toSimpleGraph.induce (W : Set C.supp)).Preconnected → 2*W.card ≤ U.card := by
  exact component_separator_pullback C.toSimpleGraph (M.componentPicture C).underlyingGraph
    (M.componentHom C) (M.componentVertex_injective C) 11
    ((M.componentPicture C).planar_component_separator (M.componentPicture_genusZero C hG)
      (M.componentPicture_connected C)) U

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
