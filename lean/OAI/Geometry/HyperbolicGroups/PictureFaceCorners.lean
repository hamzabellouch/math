import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.PictureCotreeColor
import OAI.Geometry.HyperbolicGroups.PictureOutsideColor

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D]
variable (M : PictureMap D)

lemma faceCorners_card_le_fiber (f : M.dual.GraphVertex) :
    (M.faceCorners f).card ≤ Nat.card {x : D // M.dual.vertexClass x = f} := by
  have hh := Finset.card_image_le (f := M.vertexClass)
    (s := Finset.univ.filter (fun x => M.dual.vertexClass x = f))
  change (M.faceCorners f).card ≤ _ at hh
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact hh

/-- A bound on the literal side-degree of each face bounds the number of
its distinct corner vertices, even for faces touching the same vertex
repeatedly or traversing both sides of a loop. -/
theorem faceCorners_card_le (k : ℕ)
    (hdegree : ∀ x : D, Fintype.card {y : D // M.face.SameCycle x y} ≤ k)
    (f : M.dual.GraphVertex) : (M.faceCorners f).card ≤ k := by
  have hh := M.faceCorners_card_le_fiber f
  let x := M.dual.vertexRepresentative f
  have hx : M.dual.vertexClass x = f := M.dual.vertexClass_representative f
  have he : Nat.card {y : D // M.dual.vertexClass y = f} =
      Nat.card {y : D // M.face.SameCycle x y} := by
    rw [← hx,Nat.card_congr (M.dual.vertex_fiber_equiv x),M.dual_vertex]
  rw [he,Nat.card_eq_fintype_card] at hh
  exact hh.trans (hdegree x)

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
