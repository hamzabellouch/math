import OAI.CategoryTheory.Globular.CylinderObjects

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] (B : GlobularFrame K)

theorem homGlob_faceMap (Y : K) {j k : ℕ} (h : j < k) (ε : Bool)
    (a : B.obj k ⟶ Y) : (B.homGlob Y).faceMap h ε a = B.diagram.face h ε ≫ a := by
  induction k, h using Nat.le_induction with
  | base =>
    rw [GlobularSet.faceMap_succ, CoGlobularObject.face_succ]
    cases ε <;> rfl
  | succ k h ih =>
    erw [(B.homGlob Y).faceMap_source h ε, ih,
      ← B.diagram.face_adjacent h ε false]
    exact (Category.assoc _ _ _).symm

theorem homGlob_eval (Y : K) {j k : ℕ} (f : Globe.Face j k) (a : B.obj k ⟶ Y) :
    (B.homGlob Y).evalFace f a = B.diagram.eval f ≫ a := by
  cases f with
  | id => exact (Category.id_comp a).symm
  | face h ε => exact B.homGlob_faceMap Y h ε a

noncomputable def homGlobPresheafIso (Y : K) :
    (B.homGlob Y).presheaf ≅ (Presheaf.restrictedULiftYoneda.{v} B.diagram.functor).obj Y :=
  NatIso.ofComponents (fun _ => Equiv.toIso Equiv.ulift.symm) (by
    intro j k f
    apply ConcreteCategory.hom_ext
    intro a
    change ULift.up ((B.homGlob Y).evalFace f.unop a) = ULift.up (B.diagram.eval f.unop ≫ a)
    exact congrArg ULift.up (B.homGlob_eval Y f.unop a))

variable [HasColimitsOfSize.{0,v} K]
noncomputable abbrev realization : GlobularPresheaf.{v} ⥤ K := B.diagram.realization
noncomputable abbrev cell (S : GlobularPresheaf.{v}) (k : ℕ) (x : S.underlying.Cell k) :
    B.obj k ⟶ B.realization.obj S := B.diagram.cell S k x

noncomputable def desc {S : GlobularPresheaf.{v}} {Y : K}
    (f : GlobularSet.Hom S.underlying (B.homGlob Y)) : B.realization.obj S ⟶ Y :=
  (B.diagram.homEquiv S Y).symm
    (S.underlyingPresheafIso.inv ≫ f.presheafMap ≫ (B.homGlobPresheafIso Y).hom)

@[reassoc (attr := simp)] theorem cell_desc {S : GlobularPresheaf.{v}} {Y : K}
    (f : GlobularSet.Hom S.underlying (B.homGlob Y)) (k : ℕ) (x : S.underlying.Cell k) :
    B.cell S k x ≫ B.desc f = f.app k x := by
  have e := (B.diagram.homEquiv S Y).apply_symm_apply
    (S.underlyingPresheafIso.inv ≫ f.presheafMap ≫ (B.homGlobPresheafIso Y).hom)
  have h := congrArg (fun t : S ⟶ (Presheaf.restrictedULiftYoneda.{v} B.diagram.functor).obj Y =>
    t.app (op (Globe.mk k)) x) e
  erw [CoGlobularObject.homEquiv_app] at h
  exact congrArg ULift.down h

@[reassoc] theorem cell_face (S : GlobularPresheaf.{v}) {j k : ℕ} (f : Globe.Face j k)
    (x : S.underlying.Cell k) :
    B.diagram.eval f ≫ B.cell S k x = B.cell S j (S.map (show Globe.mk j ⟶ Globe.mk k from f).op x) := by
  have e := B.diagram.globeIso_naturality f
  have e' : B.diagram.eval f ≫ (B.diagram.globeIso k).inv =
      (B.diagram.globeIso j).inv ≫ B.realization.map (uliftYoneda.map f) := by
    rw [← Iso.inv_hom_id_assoc (B.diagram.globeIso j) (B.diagram.eval f), ← e]
    erw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  unfold cell CoGlobularObject.cell
  erw [← Category.assoc, e', Category.assoc, ← Functor.map_comp]
  congr 2
  exact (uliftYonedaEquiv_symm_map (show Globe.mk j ⟶ Globe.mk k from f).op x).symm

noncomputable def cellMap (S : GlobularPresheaf.{v}) :
    GlobularSet.Hom S.underlying (B.homGlob (B.realization.obj S)) where
  app := B.cell S
  source_app k x := by
    change B.cell S k (S.map (Globe.source k).op x) = B.diagram.source k ≫ B.cell S (k+1) x
    simpa only [CoGlobularObject.eval, Globe.source, Globe.face, CoGlobularObject.face_succ,
      CoGlobularObject.adjacent, Bool.false_eq_true, ite_false, diagram] using
      (B.cell_face S (Globe.source k) x).symm
  target_app k x := by
    change B.cell S k (S.map (Globe.target k).op x) = B.diagram.target k ≫ B.cell S (k+1) x
    simpa only [CoGlobularObject.eval, Globe.target, Globe.face, CoGlobularObject.face_succ,
      CoGlobularObject.adjacent, ite_true, diagram] using
      (B.cell_face S (Globe.target k) x).symm

noncomputable def realizeHom {S : GlobularPresheaf.{v}} {Y : K}
    (f : B.realization.obj S ⟶ Y) : GlobularSet.Hom S.underlying (B.homGlob Y) :=
  (B.cellMap S).comp (post f)

theorem hom_ext {S : GlobularPresheaf.{v}} {Y : K} {f g : B.realization.obj S ⟶ Y}
    (h : ∀ k x, B.cell S k x ≫ f = B.cell S k x ≫ g) : f = g := B.diagram.hom_ext h

@[simp] theorem realizeHom_desc {S : GlobularPresheaf.{v}} {Y : K}
    (f : GlobularSet.Hom S.underlying (B.homGlob Y)) : B.realizeHom (B.desc f) = f := by
  ext k x
  exact B.cell_desc f k x

@[simp] theorem desc_realizeHom {S : GlobularPresheaf.{v}} {Y : K}
    (f : B.realization.obj S ⟶ Y) : B.desc (B.realizeHom f) = f := by
  apply B.hom_ext
  intro k x
  exact B.cell_desc (B.realizeHom f) k x

end GlobularFrame
end Grothendieck

end OAI
