import OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing
import OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients

namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

def multiply (W : X.Opens) (a : Γ(X,W)) :
    SheafOfModules.unit W.toScheme.ringCatSheaf ⟶
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
  (SheafOfModules.unit W.toScheme.ringCatSheaf).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun V => X.presheaf.map (homOfLE (W.ι_image_le V.unop)).op a)
      (fun {V V'} f => by
        change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
        erw [← Functor.map_comp]
        rfl))

lemma multiply_endValue (W : X.Opens) (a : Γ(X,W)) :
    W.topIso.hom (endValue (multiply W a)) = a := by
  change W.topIso.hom ((1 : Γ(X,W.ι ''ᵁ ⊤)) * X.presheaf.map (homOfLE (W.ι_image_le ⊤)).op a) = a
  rw [one_mul]
  simp only [Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) a = a
  erw [← Functor.map_comp]
  change X.presheaf.map (𝟙 (op W)) a = a
  exact congrArg (fun q => q a) (X.presheaf.map_id (op W))

variable (c : Cocycle U)

lemma openPresheafFrame_change (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    (openPresheafFrame c i W hi).hom =
      (openPresheafFrame c j W hj).hom ≫
        (multiply W (c.transition i j W hi hj : Γ(X,W))).val := by
  ext V s
  change chartEquiv c i ((W.ι_image_le V.unop).trans hi) s =
    chartEquiv c j ((W.ι_image_le V.unop).trans hj) s *
      X.presheaf.map (homOfLE (W.ι_image_le V.unop)).op
        (c.transition i j W hi hj : Γ(X,W))
  rw [c.restriction]
  exact (chartEquiv_change c i j ((W.ι_image_le V.unop).trans hi)
    ((W.ι_image_le V.unop).trans hj) s).trans (mul_comm _ _)

lemma openFrame_change (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    (openFrame c i W hi).hom =
      (openFrame c j W hj).hom ≫ multiply W (c.transition i j W hi hj : Γ(X,W)) := by
  simp only [openFrame]
  let F : PresheafOfModules W.toScheme.ringCatSheaf.obj ⥤ W.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 W.toScheme.ringCatSheaf.obj)
  let O : W.toScheme.Modules := SheafOfModules.unit W.toScheme.ringCatSheaf
  let a : (sheaf c).restrict W.ι ⟶ F.obj ((modulePresheafRestrict W.ι).obj (presheaf c)) :=
    (moduleSheafificationRestrict W.ι).hom.app (presheaf c)
  let b : F.obj O.val ⟶ O :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 W.toScheme.ringCatSheaf.obj)).counit.app O
  let f := (openPresheafFrame c i W hi).hom
  let g := (openPresheafFrame c j W hj).hom
  let t : O ⟶ O := multiply W (c.transition i j W hi hj : Γ(X, W))
  have hf : f = g ≫ t.val := openPresheafFrame_change c i j W hi hj
  have hb : F.map t.val ≫ b = b ≫ t :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 W.toScheme.ringCatSheaf.obj)).counit.naturality t
  change a ≫ F.map f ≫ b = (a ≫ F.map g ≫ b) ≫ t
  calc
    _ = a ≫ F.map (g ≫ t.val) ≫ b := congrArg (fun h => a ≫ F.map h ≫ b) hf
    _ = a ≫ F.map g ≫ (F.map t.val ≫ b) := by rw [F.map_comp, Category.assoc]
    _ = a ≫ F.map g ≫ (b ≫ t) := congrArg (fun h => a ≫ F.map g ≫ h) hb
    _ = _ := by simp only [Category.assoc]

lemma openFrame_frameChange (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    W.topIso.hom (frameChange (openFrame c j W hj) (openFrame c i W hi) : Γ(W.toScheme,⊤)) =
      (c.transition i j W hi hj : Γ(X,W)) := by
  change W.topIso.hom (endValue ((openFrame c j W hj).inv ≫ (openFrame c i W hi).hom)) = _
  have h := congrArg (fun t => (openFrame c j W hj).inv ≫ t)
    (openFrame_change c i j W hi hj)
  have he := h.trans ((openFrame c j W hj).inv_hom_id_assoc
    (multiply W (c.transition i j W hi hj : Γ(X, W))))
  exact (congrArg (fun t => W.topIso.hom (endValue t)) he).trans (multiply_endValue W _)

end
end PiExponentSeshadri.LineBundleGluing

end OAI
