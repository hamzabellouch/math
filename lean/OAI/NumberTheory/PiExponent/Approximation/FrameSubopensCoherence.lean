import OAI.NumberTheory.PiExponent.Approximation.FrameSubopens

namespace OAI

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X : Scheme} {M : X.Modules} {U V W : X.Opens}

lemma restrictOpenFrame_app (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme)
    (A : V.toScheme.Opens) (x : Γ(M.restrict V.ι,A)) :
    (restrictOpenFrame h e).hom.app A x =
      X.presheaf.map (homOfLE (show V.ι ''ᵁ A ≤ U.ι ''ᵁ (X.homOfLE h ''ᵁ A) from by
        simp [← Scheme.Hom.comp_image])).op
        (e.hom.app (X.homOfLE h ''ᵁ A)
          (M.presheaf.map (homOfLE
            (show U.ι ''ᵁ (X.homOfLE h ''ᵁ A) ≤ V.ι ''ᵁ A from by
              simp [← Scheme.Hom.comp_image])).op x)) := by
  simp only [restrictOpenFrame, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, Iso.app_inv, Iso.app_hom,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  change ((X.homOfLE h).appIso A).hom (e.hom.app (X.homOfLE h ''ᵁ A)
    ((M.presheaf.map _ ≫ M.presheaf.map _) x)) = _
  simp only [Scheme.Hom.appIso_hom', Scheme.homOfLE_appLE]
  erw [← Functor.map_comp]
  rfl

lemma restrictOpenFrame_trans (h : W ≤ V) (k : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) :
    restrictOpenFrame h (restrictOpenFrame k e) = restrictOpenFrame (h.trans k) e := by
  apply Iso.ext
  ext A x
  have hh := restrictOpenFrame_app h (restrictOpenFrame k e) A x
  let y := M.presheaf.map (homOfLE
    (show V.ι ''ᵁ (X.homOfLE h ''ᵁ A) ≤ W.ι ''ᵁ A from by
      simp [← Scheme.Hom.comp_image])).op x
  have hk := restrictOpenFrame_app k e (X.homOfLE h ''ᵁ A) y
  have hhk := congrArg (X.presheaf.map (homOfLE
    (show W.ι ''ᵁ A ≤ V.ι ''ᵁ (X.homOfLE h ''ᵁ A) from by
      simp [← Scheme.Hom.comp_image])).op) hk
  have hc := restrictOpenFrame_app (h.trans k) e A x
  refine hh.trans (hhk.trans (Eq.trans ?_ hc.symm))
  change (X.presheaf.map _ ≫ X.presheaf.map _)
    (e.hom.app (X.homOfLE k ''ᵁ (X.homOfLE h ''ᵁ A))
      ((M.presheaf.map _ ≫ M.presheaf.map _) x)) =
    X.presheaf.map _ (e.hom.app (X.homOfLE (h.trans k) ''ᵁ A)
      (M.presheaf.map _ x))
  erw [← Functor.map_comp, ← Functor.map_comp]
  let B := X.homOfLE k ''ᵁ (X.homOfLE h ''ᵁ A)
  let C := X.homOfLE (h.trans k) ''ᵁ A
  have hA : C ≤ B := by
    simp only [B, C, ← Scheme.Hom.comp_image, Scheme.homOfLE_homOfLE]
    exact le_rfl
  have hB : U.ι ''ᵁ B ≤ W.ι ''ᵁ A := by
    simp [B, ← Scheme.Hom.comp_image]
  have hC : W.ι ''ᵁ A ≤ U.ι ''ᵁ C := by
    simp [C, ← Scheme.Hom.comp_image]
  have hn := CategoryTheory.congr_fun
    (e.hom.mapPresheaf.naturality (homOfLE hA).op)
    (M.presheaf.map (homOfLE hB).op x)
  change e.hom.app C ((M.restrict U.ι).presheaf.map (homOfLE hA).op
    (M.presheaf.map (homOfLE hB).op x)) =
    U.toScheme.presheaf.map (homOfLE hA).op
      (e.hom.app B (M.presheaf.map (homOfLE hB).op x)) at hn
  refine Eq.trans ?_ (Eq.trans (congrArg (X.presheaf.map (homOfLE hC).op) hn).symm ?_)
  · change X.presheaf.map _ (e.hom.app B (M.presheaf.map _ x)) =
      (X.presheaf.map _ ≫ X.presheaf.map _) (e.hom.app B (M.presheaf.map _ x))
    erw [← Functor.map_comp]
    rfl
  · apply congrArg (X.presheaf.map (homOfLE hC).op)
    apply congrArg (e.hom.app C)
    change (M.presheaf.map _ ≫ M.presheaf.map _) x = M.presheaf.map _ x
    erw [← Functor.map_comp]
    rfl
end
end PiExponentSeshadri.Frames

end OAI
