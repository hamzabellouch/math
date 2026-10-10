import OAI.Algebra.Finitistic.Localization.SourceCornerEvaluation
import OAI.Algebra.Finitistic.Selection.SelectionIteration

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedImageComparison
open QuadraticEncoding SourceImageEvaluation
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

/-- The evaluator's range is canonically the primary's actual H(Y), as a complex vector space. -/
def equiv : imageSpace (k := ℂ) (Y := Y) (selectionIdempotent 0) ≃ₗ[ℂ]
    complexObject (selectionStep (ModuleCat.of SelectionRing Y)) where
  toFun x := ⟨x.val.down, by
    obtain ⟨z,hz⟩ := x.property
    have hz' : selectionIdempotent 0 • z.down = x.val.down := congrArg ULift.down hz
    change selectionIdempotent 0 • x.val.down = x.val.down
    rw [← hz',← mul_smul,selectionIdempotent_square]⟩
  invFun x := ⟨ULift.up x.val, ⟨ULift.up x.val, by
    change ULift.up (selectionIdempotent 0 • x.val) = ULift.up x.val
    exact congrArg ULift.up x.property⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by rfl
  map_add' x y := rfl
  map_smul' c x := by
    apply Subtype.ext
    change c • x.val.down = selectionAutomorphism 1 (algebraMap ℂ SelectionRing c) • x.val.down
    rw [AlgEquiv.commutes,algebraMap_smul]

abbrev moduleAction (r : SelectionRing) (x : selectionStep (ModuleCat.of SelectionRing Y)) :
    selectionStep (ModuleCat.of SelectionRing Y) := r • x

/-- The evaluator's compressed alpha action is precisely the action on the primary's H(Y). -/
theorem equiv_action (r : SelectionRing)
    (x : imageSpace (k := ℂ) (Y := Y) (selectionIdempotent 0)) :
    equiv (Y := Y) ((imageCornerEnd (action (k := ℂ) (Y := Y) (selectionIdempotent 0)).hom
      (action (k := ℂ) (Y := Y) (selectionAutomorphism 1 r)).hom) x) =
    moduleAction (Y := Y) r (equiv (Y := Y) x) := by
  apply Subtype.ext
  have h := imageCorner_restriction (k := ℂ) (Y := Y) (selectionIdempotent 0)
    (selectionAutomorphism 1 r) (selectionIdempotent_square 0)
    (selectionIdempotent_central 0 (selectionAutomorphism 1 r)).eq x
  exact congrArg ULift.down h

theorem image_nontrivial_of (h : Nontrivial (selectionStep (ModuleCat.of SelectionRing Y))) :
    Nontrivial (imageSpace (k := ℂ) (Y := Y) (selectionIdempotent 0)) := by
  let i := equiv (Y := Y)
  obtain ⟨x,y,hxy⟩ := h.exists_pair_ne
  exact ⟨⟨i.symm x,i.symm y,fun h => hxy (i.symm.injective h)⟩⟩

theorem image_subsingleton_of (h : Subsingleton (selectionStep (ModuleCat.of SelectionRing Y))) :
    Subsingleton (imageSpace (k := ℂ) (Y := Y) (selectionIdempotent 0)) :=
  ⟨fun first second => (equiv (Y := Y)).injective
    (h.elim (equiv (Y := Y) first) (equiv (Y := Y) second))⟩
end LittleFinitistic.SelectedImageComparison

end

end OAI
