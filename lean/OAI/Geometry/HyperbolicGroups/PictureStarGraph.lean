import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.PictureUnderlyingGraph
import OAI.Geometry.HyperbolicGroups.PictureTriangulationEuler

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D)

def starOldVertex : M.GraphVertex → M.triangulation.GraphVertex :=
  Quotient.map Sum.inl (fun _ _ h => M.star_vertex_lift h)

omit [DecidableEq D] in
lemma starOldVertex_class (x : D) : M.starOldVertex (M.vertexClass x) =
    M.triangulation.vertexClass (.inl x) := rfl

omit [DecidableEq D] in
lemma starOldVertex_injective : Function.Injective M.starOldVertex := by
  intro v w
  induction v using Quotient.inductionOn with | _ x =>
    induction w using Quotient.inductionOn with | _ y =>
      intro h
      have hh := (M.star_vertex_cycle (.inl x) (.inl y)).mp (Quotient.exact h)
      exact Sum.inl.inj hh

def starOldHom : M.underlyingGraph →g M.triangulation.underlyingGraph where
  toFun := M.starOldVertex
  map_rel' := by
    intro v w h
    obtain ⟨hne,x,rfl,rfl⟩ := h
    exact ⟨fun he => hne (M.starOldVertex_injective he),.inl x,rfl,rfl⟩

omit [DecidableEq D] in
lemma triangulation_connected (hc : M.underlyingGraph.Connected) :
    M.triangulation.underlyingGraph.Connected := by
  have : Nonempty M.triangulation.GraphVertex := by
    obtain ⟨v⟩ := hc.nonempty
    exact ⟨M.starOldVertex v⟩
  apply SimpleGraph.Connected.mk
  intro v w
  induction v using Quotient.inductionOn with | _ x =>
    induction w using Quotient.inductionOn with | _ y =>
      apply (M.triangulation.underlying_reachable_iff x y).mpr
      apply (M.star_components x y).mpr
      exact Quotient.sound ((M.underlying_reachable_iff _ _).mp (hc _ _))

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
