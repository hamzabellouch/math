import OAI.NumberTheory.PiExponent.Approximation.FrameSections
import OAI.NumberTheory.PiExponent.Approximation.TensorPure
import OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingTransitions

namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}} {ι : Type} {U : ι → X.Opens} (c : Cocycle U)

def globalSection (s : sections c ⊤) : O X ⟶ sheaf c :=
  (moduleSectionEquiv (sheaf c)).symm
    ((((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)).app (op ⊤)) s)

lemma sheafification_unit_counit_map (Z : Scheme.{0})
    (P : PresheafOfModules Z.ringCatSheaf.obj) (M : Z.Modules) (e : P ⟶ M.val) :
    (TensorPure.adj Z).unit.app P ≫
      ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map e).val ≫
      ((TensorPure.adj Z).counit.app M).val = e := by
  let F : PresheafOfModules Z.ringCatSheaf.obj ⥤ Z.Modules :=
    PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)
  let G : Z.Modules ⥤ PresheafOfModules Z.ringCatSheaf.obj :=
    SheafOfModules.forget Z.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)
  let a : F ⊣ G := TensorPure.adj Z
  have h := (a.unit_comp_map_eq_iff (F.map e ≫ a.counit.app M) e).mpr rfl
  have hm := congrArg (fun q => a.unit.app P ≫ q)
    (G.map_comp (F.map e) (a.counit.app M))
  exact hm.symm.trans h

lemma module_comp_val {Z : Scheme.{0}} {M N P : Z.Modules} (a : M ⟶ N) (b : N ⟶ P) :
    (a ≫ b).val = a.val ≫ b.val := rfl

lemma openFrame_unit (i : ι) (W : X.Opens) (hW : W ≤ U i) :
    (modulePresheafRestrict W.ι).map
        ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)) ≫
      (openFrame c i W hW).hom.val = (openPresheafFrame c i W hW).hom := by
  simp only [openFrame]
  let R := modulePresheafRestrict W.ι
  let F : PresheafOfModules W.toScheme.ringCatSheaf.obj ⥤ W.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 W.toScheme.ringCatSheaf.obj)
  let a : (sheaf c).restrict W.ι ⟶ F.obj (R.obj (presheaf c)) :=
    (moduleSheafificationRestrict W.ι).hom.app (presheaf c)
  let b : F.obj (O W.toScheme).val ⟶ O W.toScheme :=
    (TensorPure.adj W.toScheme).counit.app (O W.toScheme)
  let e := (openPresheafFrame c i W hW).hom
  change R.map ((TensorPure.adj X).unit.app (presheaf c)) ≫
    a.val ≫ (F.map e).val ≫ b.val = e
  have h := TensorPure.sheafify_restrict_unit W.ι (presheaf c)
  have h₁ := Category.assoc
    (R.map ((TensorPure.adj X).unit.app (presheaf c))) a.val ((F.map e).val ≫ b.val)
  have h₂ := congrArg (fun q => q ≫ (F.map e).val ≫ b.val) h
  have h₃ := sheafification_unit_counit_map W.toScheme _ (O W.toScheme) e
  exact h₁.symm.trans (h₂.trans h₃)

lemma openFrame_unit_apply (i : ι) (W : X.Opens) (hW : W ≤ U i)
    (V : W.toScheme.Opens) (s : sections c (W.ι ''ᵁ V)) :
    (openFrame c i W hW).hom.app V
      ((((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)).app (op (W.ι ''ᵁ V))) s) =
      s.val ⟨i,W.ι ''ᵁ V,le_rfl,(W.ι_image_le V).trans hW⟩ := by
  have h := congrArg (fun q => q.app (op V) s) (openFrame_unit c i W hW)
  exact h

lemma globalSection_app_one (s : sections c ⊤) (V : X.Opens) :
    (globalSection c s).app V (1 : Γ(X,V)) =
      (((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)).app (op V)
          (restrict c le_top s)) := by
  have ht := (moduleSectionEquiv (sheaf c)).apply_symm_apply
    ((((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)).app (op ⊤)) s)
  change (globalSection c s).app ⊤ (1 : Γ(X,⊤)) = _ at ht
  rw [← section_value_natural (globalSection c s) (homOfLE (show V ≤ ⊤ from le_top)), ht]
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c))
        (homOfLE (show V ≤ ⊤ from le_top)).op s).symm

theorem globalSection_coefficient (s : sections c ⊤) (i : ι)
    (W : X.Opens) (hW : W ≤ U i) :
    W.topIso.hom (coefficient (openFrame c i W hW)
      (restrictSection W.ι (globalSection c s))) = s.val ⟨i,W,le_top,hW⟩ := by
  change W.topIso.hom ((openFrame c i W hW).hom.app ⊤
    ((globalSection c s).app (W.ι ''ᵁ ⊤)
      ((W.ι.appIso ⊤).inv (1 : Γ(W.toScheme,⊤))))) = _
  rw [map_one, globalSection_app_one, openFrame_unit_apply]
  change W.topIso.hom (s.val ⟨i,W.ι ''ᵁ ⊤,le_top,(W.ι_image_le ⊤).trans hW⟩) = _
  rw [← s.property.1 i W (W.ι ''ᵁ ⊤) le_top hW (W.ι_image_le ⊤)]
  simp only [Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) (s.val ⟨i,W,le_top,hW⟩) = _
  erw [← Functor.map_comp]
  change X.presheaf.map (𝟙 (op W)) (s.val ⟨i,W,le_top,hW⟩) = _
  exact congrArg (fun q => q (s.val ⟨i,W,le_top,hW⟩)) (X.presheaf.map_id (op W))

end
end PiExponentSeshadri.LineBundleGluing

end OAI
