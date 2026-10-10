import OAI.NumberTheory.PiExponent.Approximation.FrameSections
import OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing

namespace OAI

namespace PiExponent.SectionImageIdeal
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {M : X.Modules}

def imageIdeal (φ : M ⟶ structureSheaf X) (U : X.Opens) : Ideal Γ(X,U) :=
  (φ.val.app (op U)).hom.range

lemma map_imageIdeal_le (φ : M ⟶ structureSheaf X) {U V : X.Opens} (h : U ≤ V) :
    (imageIdeal φ V).map (X.presheaf.map (homOfLE h).op).hom ≤ imageIdeal φ U := by
  apply Ideal.map_le_iff_le_comap.mpr
  rintro x ⟨m,rfl⟩
  refine ⟨M.presheaf.map (homOfLE h).op m, ?_⟩
  exact congr($(φ.mapPresheaf.naturality (homOfLE h).op) m)

theorem affine_map_imageIdeal [IsAffine X] [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (r : Γ(X,⊤)) :
    (imageIdeal φ ⊤).map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      imageIdeal φ (X.basicOpen r) := by
  apply le_antisymm (map_imageIdeal_le φ _)
  rintro x ⟨m,rfl⟩
  change Γ(M, X.basicOpen r) at m
  obtain ⟨n,z,hz⟩ := GlobalSectionClearing.affine_basicOpen_denominators M r m
  let ρ : Γ(X,⊤) →+* Γ(X,X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  have he : ρ (φ.app ⊤ z) = ρ r ^ n * (show Γ(X,X.basicOpen r) from φ.app (X.basicOpen r) m) := by
    have hn := congr($(φ.mapPresheaf.naturality (homOfLE (X.basicOpen_le r)).op) z)
    change φ.app (X.basicOpen r)
      (GlobalSectionClearing.openRestriction M (X.basicOpen_le r) z) = ρ (φ.app ⊤ z) at hn
    rw [← hn, hz]
    change φ.app (X.basicOpen r) (ρ (r^n) • m) = _
    rw [map_pow, φ.app_smul]
    rfl
  have hm : ρ (φ.app ⊤ z) ∈ (imageIdeal φ ⊤).map ρ :=
    Ideal.mem_map_of_mem ρ ⟨z,rfl⟩
  rw [he] at hm
  exact (Ideal.unit_mul_mem_iff_mem _
    ((X.toRingedSpace.isUnit_res_basicOpen r).pow n)).mp hm

theorem imageIdeal_restrict {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (φ : M ⟶ structureSheaf X) (V : Y.Opens) :
    (imageIdeal ((Scheme.Modules.restrictFunctor f).map φ ≫
      (Scheme.Modules.restrictUnitIso f).hom) V).map (f.appIso V).inv.hom =
      imageIdeal φ (f ''ᵁ V) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    rintro y ⟨m,rfl⟩
    refine ⟨m,?_⟩
    change φ.app (f ''ᵁ V) m = (f.appIso V).inv ((f.appIso V).hom (φ.app (f ''ᵁ V) m))
    exact ((f.appIso V).hom_inv_id_apply _).symm
  · rintro y ⟨m,rfl⟩
    have h := Ideal.mem_map_of_mem (f.appIso V).inv.hom
      (show ((f.appIso V).hom (φ.app (f ''ᵁ V) m)) ∈
        imageIdeal ((Scheme.Modules.restrictFunctor f).map φ ≫
          (Scheme.Modules.restrictUnitIso f).hom) V from ⟨m,rfl⟩)
    change (show Γ(X,f ''ᵁ V) from φ.app (f ''ᵁ V) m) ∈
      (imageIdeal ((Scheme.Modules.restrictFunctor f).map φ ≫
        (Scheme.Modules.restrictUnitIso f).hom) V).map (f.appIso V).inv.hom
    erw [(f.appIso V).hom_inv_id_apply] at h
    exact h

theorem map_imageIdeal_affine_image {Y : Scheme.{0}} [IsAffine Y]
    [M.IsQuasicoherent] (f : Y ⟶ X) [IsOpenImmersion f]
    (φ : M ⟶ structureSheaf X) (r : Γ(Y,⊤)) :
    (imageIdeal φ (f ''ᵁ ⊤)).map
      (X.presheaf.map (f.opensFunctor.map (homOfLE (Y.basicOpen_le r))).op).hom =
      imageIdeal φ (f ''ᵁ Y.basicOpen r) := by
  let ψ : M.restrict f ⟶ structureSheaf Y :=
    (Scheme.Modules.restrictFunctor f).map φ ≫ (Scheme.Modules.restrictUnitIso f).hom
  rw [← imageIdeal_restrict f φ ⊤, Ideal.map_map]
  have hn := congrArg CommRingCat.Hom.hom
    (f.appIso_inv_naturality (homOfLE (Y.basicOpen_le r)).op)
  change (f.appIso (Y.basicOpen r)).inv.hom.comp
      (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom =
    (X.presheaf.map (f.opensFunctor.map (homOfLE (Y.basicOpen_le r))).op).hom.comp
      (f.appIso ⊤).inv.hom at hn
  rw [← hn, ← Ideal.map_map]
  rw [affine_map_imageIdeal ψ r, imageIdeal_restrict]

theorem map_imageIdeal_basicOpen [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (U : X.affineOpens) (r : Γ(X,U.1)) :
    (imageIdeal φ U.1).map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      imageIdeal φ (X.basicOpen r) := by
  let : IsAffine U.1.toScheme := U.2
  have h (V W : X.Opens) (hV : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) = V)
      (hW : U.1.ι ''ᵁ U.1.toScheme.basicOpen (U.1.topIso.inv r) = W) (hWV : W ≤ V) :
      (imageIdeal φ V).map (X.presheaf.map (homOfLE hWV).op).hom = imageIdeal φ W := by
    subst V
    subst W
    exact map_imageIdeal_affine_image U.1.ι φ (U.1.topIso.inv r)
  exact h U.1 (X.basicOpen r) U.1.ι_image_top (U.1.ι_image_basicOpen_topIso_inv r)
    (X.basicOpen_le r)

def imageIdealSheaf [M.IsQuasicoherent] (φ : M ⟶ structureSheaf X) : X.IdealSheafData where
  ideal U := imageIdeal φ U.1
  map_ideal_basicOpen U r := map_imageIdeal_basicOpen φ U r

@[simp] theorem imageIdealSheaf_ideal [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (U : X.affineOpens) :
    (imageIdealSheaf φ).ideal U = imageIdeal φ U.1 := rfl

theorem imageIdeal_top_of_frame (φ : M ⟶ structureSheaf X)
    (e : M ≅ structureSheaf X) :
    imageIdeal φ ⊤ = Ideal.span {PiExponentSeshadri.Frames.endValue (e.inv ≫ φ)} := by
  apply le_antisymm
  · rintro x ⟨m,rfl⟩
    change Γ(M,⊤) at m
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e.hom.app ⊤ m, ?_⟩
    have he : (e.inv ≫ φ).app ⊤ (e.hom.app ⊤ m) = φ.app ⊤ m := by
      change (e.hom ≫ e.inv ≫ φ).app ⊤ m = _
      rw [e.hom_inv_id_assoc]
    exact he.symm.trans ((PiExponentSeshadri.Frames.end_apply (e.inv ≫ φ) ⊤
      (e.hom.app ⊤ m)).trans (mul_comm (show Γ(X,⊤) from e.hom.app ⊤ m)
        (PiExponentSeshadri.Frames.endValue (e.inv ≫ φ))))
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    exact ⟨e.inv.app ⊤ (1 : Γ(X,⊤)), rfl⟩

lemma imageIdeal_map_eq (φ : M ⟶ structureSheaf X) {U V : X.Opens} (h : U = V) :
    (imageIdeal φ U).map (X.presheaf.map (eqToHom h.symm).op).hom = imageIdeal φ V := by
  subst V
  change (imageIdeal φ U).map (X.presheaf.map (𝟙 (op U))).hom = imageIdeal φ U
  rw [X.presheaf.map_id]
  exact Ideal.map_id _

theorem imageIdealSheaf_on_frame [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    (imageIdealSheaf φ).ideal U = Ideal.span
      {U.1.topIso.hom (PiExponentSeshadri.Frames.endValue
        (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  let ψ := (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫
    (Scheme.Modules.restrictUnitIso U.1.ι).hom
  have h : (imageIdeal ψ ⊤).map U.1.topIso.hom.hom = imageIdeal φ U.1 := by
    have hi := congrArg (fun J : Ideal Γ(X,U.1.ι ''ᵁ ⊤) =>
      J.map (X.presheaf.map (eqToHom U.1.ι_image_top.symm).op).hom)
      (imageIdeal_restrict U.1.ι φ ⊤)
    rw [imageIdeal_map_eq φ U.1.ι_image_top] at hi
    rw [Ideal.map_map] at hi
    convert hi using 1
    congr 1
    ext a
    simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appIso, Iso.refl_inv, RingHom.comp_apply]
    rfl
  rw [imageIdeal_top_of_frame ψ e, Ideal.map_span, Set.image_singleton] at h
  exact h.symm

end
end PiExponent.SectionImageIdeal

end OAI
