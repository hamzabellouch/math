import Mathlib
import OAI.Geometry.HyperbolicGroups.FaceSplice
import OAI.Geometry.HyperbolicGroups.BigonRemove

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap
variable (M : PictureMap D) {a b : D} (hab : a ≠ b) (hnext : M.face a = b)

/-- Pinch the two consecutive boundary sides off as a genuine bigon. The
other side pairs are unchanged, and the remaining boundary bypasses them. -/
def boundaryPinch (_ : a ≠ b) (_ : M.face a = b) : PictureMap D := M.splice b (M.face⁻¹ a)

omit [Fintype D] in
lemma boundaryPinch_bigon : (M.boundaryPinch hab hnext).Bigon a b := by
  have har : a ≠ M.face⁻¹ a := by
    intro h
    have hh := congrArg M.face h
    simp only [Perm.inv_def,Equiv.apply_symm_apply] at hh
    exact hab (hnext.symm.trans hh).symm
  refine ⟨hab,?_,?_⟩
  · change M.face (swap b (M.face⁻¹ a) a) = b
    rw [swap_apply_of_ne_of_ne hab har,hnext]
  · change M.face (swap b (M.face⁻¹ a) b) = a
    rw [swap_apply_left,Perm.inv_def,Equiv.apply_symm_apply]

lemma boundaryPinch_genusZero (hG : M.GenusZero) : (M.boundaryPinch hab hnext).GenusZero := by
  by_cases he : b = M.face⁻¹ a
  · have he' : M.boundaryPinch hab hnext = M := by
      apply PictureMap.ext
      · ext x
        simp [boundaryPinch,splice,he]
      · rfl
    rwa [he']
  · apply M.split_genusZero hG b (M.face⁻¹ a) he
    have h₁ : M.face.SameCycle a b := hnext ▸ (SameCycle.rfl (f := M.face) (x := a)).apply_right
    have h₂ : M.face.SameCycle (M.face⁻¹ a) a := by
      simpa only [Perm.inv_def,Equiv.apply_symm_apply] using (SameCycle.rfl (f := M.face) (x := M.face⁻¹ a)).apply_right
    exact h₁.symm.trans h₂.symm

variable {L V : Type*} {label : D → L} {start : L → V} {rev : L → L}

omit [Fintype D] in
lemma boundaryPinch_respects (hM : M.Respects label start rev)
    (hc : label a = rev (label b)) :
    (M.boundaryPinch hab hnext).Respects label start rev := by
  have hr : start (label (M.edge (M.face⁻¹ a))) = start (label a) := by
    have h := hM.1 (M.edge (M.face⁻¹ a))
    simpa only [vertex,mul_apply,M.edge_edge,Perm.inv_def,Equiv.apply_symm_apply] using h.symm
  have hv : start (label (M.edge b)) = start (label (M.edge (M.face⁻¹ a))) := by
    rw [hr,hM.2 b,← hc]
  constructor
  · intro x
    rw [boundaryPinch,M.splice_vertex,mul_apply,hM.1]
    exact Equiv.apply_swap_eq_self (v := start ∘ label) hv x
  · exact hM.2

/-- Literal free boundary cancellation, valid even when either canceled
side was paired to an interior side or to another part of the outside.
It is a genus-zero operation, not an assumed disk replacement. -/
def boundaryFold : PictureMap {x // OffPair a b x} :=
  (M.boundaryPinch_bigon hab hnext).remove

lemma boundaryFold_genusZero (hG : M.GenusZero) : (M.boundaryFold hab hnext).GenusZero :=
  (M.boundaryPinch_bigon hab hnext).remove_genusZero (M.boundaryPinch_genusZero hab hnext hG)

omit [Fintype D] in
lemma boundaryFold_respects (hM : M.Respects label start rev)
    (hc : label a = rev (label b)) :
    (M.boundaryFold hab hnext).Respects (label ∘ Subtype.val) start rev :=
  (M.boundaryPinch_bigon hab hnext).remove_respects (M.boundaryPinch_respects hab hnext hM hc) hc

omit [Fintype D] in
lemma boundaryFold_face (x : {x // OffPair a b x}) :
    (M.boundaryFold hab hnext).face x = erasePair M.face hab x := by
  apply Subtype.ext
  change M.face (swap b (M.face⁻¹ a) x.val) = bypassPair M.face a b x.val
  rw [bypassPair,bypass_away _ b x.val x.property.2,bypass_away M.face a x.val x.property.1]
  by_cases hx : M.face x.val = a
  · have hxr : x.val = M.face⁻¹ a := M.face.injective (by simpa only [Perm.inv_def,Equiv.apply_symm_apply] using hx)
    have hba : M.face b ≠ a := by
      intro h
      exact x.property.2 (M.face.injective (hx.trans h.symm))
    rw [ite_eq_left hx,hnext,ite_eq_left rfl,bypass_away M.face a b hab.symm,ite_eq_right hba,
      hxr,swap_apply_right]
  · have hxr : x.val ≠ M.face⁻¹ a := by intro h; apply hx; rw [h,Perm.inv_def,Equiv.apply_symm_apply]
    have hxb : M.face x.val ≠ b := by
      intro h
      exact x.property.1 (M.face.injective (h.trans hnext.symm))
    rw [swap_apply_of_ne_of_ne x.property.2 hxr,ite_eq_right hx,ite_eq_right hxb]

lemma boundaryFold_face_orbits (x y : {x // OffPair a b x}) :
    (M.boundaryFold hab hnext).face.SameCycle x y ↔ M.face.SameCycle x.val y.val := by
  have he : (M.boundaryFold hab hnext).face = erasePair M.face hab := by
    apply Equiv.ext
    exact M.boundaryFold_face hab hnext
  rw [he]
  exact erasePair_orbits M.face hab x y

omit [Fintype D] in
/-- No cell-side index on another face changes. This is the compatibility
needed to turn algebraic free reduction into an actual mapped disk picture. -/
lemma boundaryFold_other_face (x : {x // OffPair a b x})
    (hx : ¬ M.face.SameCycle a x.val) :
    ((M.boundaryFold hab hnext).face x).val = M.face x.val := by
  change M.face (swap b (M.face⁻¹ a) x.val) = M.face x.val
  apply congrArg M.face
  apply swap_apply_of_ne_of_ne x.property.2
  intro he
  apply hx
  rw [he]
  have hr : M.face.SameCycle (M.face⁻¹ a) a := by
    simpa only [Perm.inv_def,Equiv.apply_symm_apply] using
      (SameCycle.rfl (f := M.face) (x := M.face⁻¹ a)).apply_right
  exact hr.symm

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
