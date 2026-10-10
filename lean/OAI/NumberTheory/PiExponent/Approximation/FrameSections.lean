import OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Frames

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

def scalarEnd (r : Γ(X, ⊤)) : O X ⟶ O X where
  val.app U := by
    let S := X.ringCatSheaf.obj.obj U
    letI : CommRing S := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom (LinearMap.mulLeft S
      ((X.presheaf.map (homOfLE le_top).op) r))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Γ(X, U.unop) at a
    change (X.presheaf.map (homOfLE le_top).op r) * (X.presheaf.map i a) =
      X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r * a)
    rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp] lemma endValue_scalarEnd (r : Γ(X, ⊤)) : endValue (scalarEnd r) = r := by
  change X.presheaf.map (𝟙 _) r * 1 = r
  simp

lemma endValue_injective : Function.Injective (endValue (X := X)) := by
  intro f g h
  ext U a
  change Γ(X, U) at a
  change f.app U a = g.app U a
  rw [end_apply f U a, end_apply g U a]
  rw [end_naturality f U, end_naturality g U, h]

lemma end_isIso_iff (f : O X ⟶ O X) : IsIso f ↔ IsUnit (endValue f) := by
  constructor
  · intro h
    let := h
    refine isUnit_iff_exists_inv.mpr ⟨endValue (inv f), ?_⟩
    rw [← endValue_comp]
    simp
  · rintro ⟨u, hu⟩
    refine ⟨⟨scalarEnd ↑u⁻¹, ?_, ?_⟩⟩
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.val_inv u
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.inv_val u

lemma coefficient_isUnit_iff {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    IsUnit (coefficient e s) ↔ IsIso s := by
  change IsUnit (endValue (s ≫ e.hom)) ↔ _
  rw [← end_isIso_iff]
  exact isIso_comp_right_iff s e.hom

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleSectionsTopEquiv {T : TopCat} (R : Sheaf (Opens.grothendieckTopology T) RingCat)
    (M : SheafOfModules R) : M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op t)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) t)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv t := by
    change M.val.map (𝟙 (op ⊤)) t = t
    rw [M.val.map_id]
    rfl

def moduleSectionEquiv (M : X.Modules) : (O X ⟶ M) ≃ Γ(M, ⊤) :=
  M.unitHomEquiv.trans (moduleSectionsTopEquiv X.ringCatSheaf M)

@[simp] lemma moduleSectionEquiv_apply (M : X.Modules) (s : O X ⟶ M) :
    moduleSectionEquiv M s = s.app ⊤ (1 : Γ(X, ⊤)) := rfl

def openSectionEquiv (M : X.Modules) (U : X.Opens) :
    (O U.toScheme ⟶ M.restrict U.ι) ≃ Γ(M, U) :=
  (moduleSectionEquiv (M.restrict U.ι)).trans
    (let e := M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
     { toFun := e.hom
       invFun := e.inv
       left_inv := fun t => Iso.hom_inv_id_apply e t
       right_inv := fun t => Iso.inv_hom_id_apply e t })

lemma section_value_natural {M : X.Modules} (s : O X ⟶ M) {U V : X.Opens} (i : U ⟶ V) :
    M.presheaf.map i.op (s.app V (1 : Γ(X, V))) = s.app U (1 : Γ(X, U)) := by
  have h := CategoryTheory.congr_fun (s.mapPresheaf.naturality i.op) (1 : Γ(X, V))
  change s.app U (X.presheaf.map i.op (1 : Γ(X, V))) =
    M.presheaf.map i.op (s.app V (1 : Γ(X, V))) at h
  simpa only [map_one] using h.symm

@[simp] lemma openSectionEquiv_restrict {M : X.Modules} (s : O X ⟶ M) (U : X.Opens) :
    openSectionEquiv M U (restrictSection U.ι s) = s.app U (1 : Γ(X, U)) := by
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (s.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme, ⊤)))) = _
  rw [map_one]
  exact section_value_natural s (eqToHom U.ι_image_top.symm)

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma moduleSectionEquiv_scalar {M : X.Modules} (f : Γ(X, ⊤)) (s : O X ⟶ M) :
    moduleSectionEquiv M (scalarEnd f ≫ s) = f • moduleSectionEquiv M s := by
  change s.app ⊤ (endValue (scalarEnd f)) = f • s.app ⊤ (1 : Γ(X, ⊤))
  rw [endValue_scalarEnd]
  have h := s.app_smul (r := f) (x := (1 : Γ(X, ⊤)))
  change s.app ⊤ (f * 1 : Γ(X, ⊤)) = f • s.app ⊤ (1 : Γ(X, ⊤)) at h
  simpa only [mul_one] using h

lemma openSectionEquiv_scalar (M : X.Modules) (U : X.Opens)
    (f : Γ(U.toScheme, ⊤)) (s : O U.toScheme ⟶ M.restrict U.ι) :
    openSectionEquiv M U (scalarEnd f ≫ s) = U.topIso.hom f • openSectionEquiv M U s := by
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (moduleSectionEquiv (M.restrict U.ι) (scalarEnd f ≫ s)) = _
  rw [moduleSectionEquiv_scalar]
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    ((U.ι.appIso ⊤).inv f • (show Γ(M, U.ι ''ᵁ ⊤) from moduleSectionEquiv (M.restrict U.ι) s)) = _
  rw [M.map_smul, U.ι_appIso]
  rfl

lemma openSectionEquiv_restrict_value (M : X.Modules) (U : X.Opens)
    (s : O U.toScheme ⟶ M.restrict U.ι) (W : U.toScheme.Opens) :
    M.presheaf.map (homOfLE (U.ι_image_le W)).op (openSectionEquiv M U s) =
      s.app W (1 : Γ(U.toScheme, W)) := by
  have h := section_value_natural s (homOfLE (show W ≤ ⊤ from le_top))
  change M.presheaf.map (U.ι.opensFunctor.map (homOfLE (show W ≤ ⊤ from le_top))).op
    (s.app ⊤ (1 : Γ(U.toScheme, ⊤))) = _ at h
  change M.presheaf.map (homOfLE (U.ι_image_le W)).op
    (M.presheaf.map (eqToHom U.ι_image_top.symm).op (s.app ⊤ (1 : Γ(U.toScheme, ⊤)))) = _
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact h

lemma image_section_extension (M : X.Modules) (U : X.Opens)
    (s t : O U.toScheme ⟶ M.restrict U.ι) (W : U.toScheme.Opens)
    (f : Γ(W.toScheme, ⊤))
    (h : restrictSection W.ι t = scalarEnd f ≫ restrictSection W.ι s) :
    M.presheaf.map (homOfLE (U.ι_image_le W)).op (openSectionEquiv M U t) =
      (U.ι.appIso W).inv (W.topIso.hom f) • M.presheaf.map (homOfLE (U.ι_image_le W)).op
        (openSectionEquiv M U s) := by
  have hh := congrArg (openSectionEquiv (M.restrict U.ι) W) h
  rw [openSectionEquiv_restrict, openSectionEquiv_scalar, openSectionEquiv_restrict] at hh
  rw [openSectionEquiv_restrict_value, openSectionEquiv_restrict_value]
  exact hh

end PiExponentSeshadri.Frames

end

end OAI
