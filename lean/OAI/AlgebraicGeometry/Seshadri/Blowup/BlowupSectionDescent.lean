import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.SchemeHartogs
import OAI.AlgebraicGeometry.Seshadri.Blowup.PointBlowupExistence
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupHartogsCharts

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

lemma IsBlowup.dominant {X B : Scheme.{0}} [IsIntegral X]
    {I : X.IdealSheafData} {π : B ⟶ X} (hπ : IsBlowup I π) (hI : I.support ≠ ⊤) :
    IsDominant π := by
  have hd : Dense (centreComplement I : Set X) :=
    (centreComplement I).isOpen.dense (by
      obtain ⟨x⟩ := complement_nonempty hI
      exact ⟨x.val,x.property⟩)
  let : IsDominant (centreComplement I).ι := Opens.isDominant_ι hd
  let : IsDominant (hπ.complementLift ≫ π) := by rw [hπ.complementLift_comp]; infer_instance
  exact IsDominant.of_comp hπ.complementLift π

lemma Surface.blowup_chart_app_surjective (S : Surface) {r : ℕ} (p : Configuration S r)
    {B : Scheme.{0}} [IsIntegral B] {π : B ⟶ S.scheme}
    (hπ : IsBlowup (centreIdeal S r p) π)
    (U : S.scheme.affineOpens) [Nonempty U.1]
    (t : Fin 2 → Γ(S.scheme,U.1))
    (het : (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale)
    (ht : ∀ i, S.scheme.basicOpen (t i) ≤ centreComplement (centreIdeal S r p)) :
    Function.Surjective (π.app U.1) := by
  let X := U.1.toScheme
  let φ : MvPolynomial (Fin 2) ℂ →+* Γ(X,⊤) :=
    U.1.topIso.inv.hom.comp (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t)
  let : Algebra (MvPolynomial (Fin 2) ℂ) Γ(X,⊤) := φ.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(X,⊤) :=
    RingHom.Etale.respectsIso.1 _ U.1.topIso.symm.commRingCatIsoToRingEquiv het
  let : Module.Flat (MvPolynomial (Fin 2) ℂ) Γ(X,⊤) := inferInstance
  have hI := support_comap_ne_top_of_open (centreIdeal S r p)
    (S.centre_support_ne_top r p) U.1.ι
  let : Nonempty (π ⁻¹ᵁ U.1).toScheme := (hπ.morphismRestrict U.1).nonempty_of_support_ne_top hI
  have hb (i : Fin 2) : X.basicOpen (algebraMap (MvPolynomial (Fin 2) ℂ) Γ(X,⊤) (MvPolynomial.X i)) ≤
      centreComplement ((centreIdeal S r p).comap U.1.ι) := by
    intro y hy hyc
    have hy' : U.1.ι y ∈ S.scheme.basicOpen (t i) := by
      rw [← U.1.ι_image_basicOpen_topIso_inv]
      refine ⟨y,?_,rfl⟩
      change y ∈ U.1.toScheme.basicOpen (U.1.topIso.inv
        ((MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t) (MvPolynomial.X i))) at hy
      change y ∈ U.1.toScheme.basicOpen (U.1.topIso.inv (t i))
      simpa only [MvPolynomial.eval₂Hom_X'] using hy
    rw [Scheme.IdealSheafData.support_comap] at hyc
    exact ht i hy' hyc
  intro s
  obtain ⟨a,ha,-⟩ := MaximalSeshadri.Hartogs.blowup_descend ℂ
    (hπ.morphismRestrict U.1) hI (hb 0) (hb 1) ((π ⁻¹ᵁ U.1).topIso.inv s)
  refine ⟨U.1.topIso.hom a,?_⟩
  apply (ConcreteCategory.bijective_of_isIso (π ⁻¹ᵁ U.1).topIso.inv).injective
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top] at ha
  simpa only [Scheme.Hom.appLE_eq_app,CommRingCat.comp_apply] using ha

theorem Surface.blowup_structureMap_isIso (S : Surface) {r : ℕ} (p : Configuration S r)
    {B : Scheme.{0}} [IsIntegral B] {π : B ⟶ S.scheme} [QuasiCompact π]
    (hπ : IsBlowup (centreIdeal S r p) π) :
    IsIso (IdealModule.structureMap π) := by
  let : IsDominant π := hπ.dominant (S.centre_support_ne_top r p)
  let : IsSchemeTheoreticallyDominant π := .of_isDominant π
  have hm : Mono (IdealModule.structureMap π).val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    exact π.app_injective U.unop
  let : Mono (IdealModule.structureMap π) :=
    (SheafOfModules.forget S.scheme.ringCatSheaf).mono_of_mono_map hm
  let F := SheafOfModules.toSheaf S.scheme.ringCatSheaf
  have hl : TopCat.Presheaf.IsLocallySurjective (F.map (IdealModule.structureMap π)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U s x hx
    obtain ⟨V,hxV,hVU,t,het,ht⟩ := S.hartogs_chart p U x hx
    let : Nonempty V.1 := ⟨⟨x,hxV⟩⟩
    obtain ⟨a,ha⟩ := S.blowup_chart_app_surjective p hπ V t het ht
      (((F.obj ((Scheme.Modules.pushforward π).obj (IdealModule.unit B))).obj.map
        (homOfLE hVU).op) s)
    exact ⟨V.1,hVU,⟨a,ha⟩,hxV⟩
  let : Epi (F.map (IdealModule.structureMap π)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hl
  let : Epi (IdealModule.structureMap π) := F.epi_of_epi_map inferInstance
  exact isIso_of_mono_of_epi _

end
end MaximalSeshadri.Geometry

end


end OAI
