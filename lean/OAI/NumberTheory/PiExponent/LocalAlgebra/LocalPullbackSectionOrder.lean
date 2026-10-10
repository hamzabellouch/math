import OAI.NumberTheory.PiExponent.Geometry.CurveModelLocalOrder
import OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder
import OAI.NumberTheory.PiExponent.Polynomials.PullbackFrameCoefficient

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.LocalSectionOrder PiExponent.CurveSectionDegree

namespace PiExponent.LocalPullbackSectionOrder


theorem topIso_germ_stalkMap {X : Scheme.{0}} (U : X.Opens) (y : U.toScheme) :
    U.topIso.hom ≫ X.presheaf.germ U (U.ι y) y.2 ≫ U.ι.stalkMap y =
      U.toScheme.presheaf.germ ⊤ y trivial := by
  have hmap : U.topIso.hom ≫ U.ι.app U =
      U.toScheme.presheaf.map (homOfLE (show U.ι ⁻¹ᵁ U ≤ ⊤ from le_top)).op := by
    rw [Scheme.Opens.ι_app, Scheme.Opens.topIso_hom]
    erw [← Functor.map_comp]
    rfl
  have hstalk := congrArg (fun k => U.topIso.hom ≫ k) (U.ι.germ_stalkMap U y y.2)
  have hres := congrArg (fun k => k ≫ U.toScheme.presheaf.germ (U.ι ⁻¹ᵁ U) y y.2) hmap
  exact hstalk.trans ((Category.assoc U.topIso.hom (U.ι.app U)
    (U.toScheme.presheaf.germ (U.ι ⁻¹ᵁ U) y y.2)).symm.trans
      (hres.trans (U.toScheme.presheaf.germ_res (homOfLE le_top) y y.2)))

theorem factor_coefficient_image {X : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A]
    (U : X.Opens) (g : Spec (CommRingCat.of A) ⟶ U.toScheme)
    (c : Γ(U.toScheme, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom (g.appTop c) =
      (Scheme.stalkClosedPointTo (g ≫ U.ι))
        (X.presheaf.germ U ((g ≫ U.ι) (IsLocalRing.closedPoint A))
          (g (IsLocalRing.closedPoint A)).2 (U.topIso.hom c)) := by
  have h := topIso_germ_stalkMap U (g (IsLocalRing.closedPoint A))
  have hg := Scheme.germ_stalkClosedPointTo g ⊤ trivial
  simp only [Scheme.stalkClosedPointTo_comp]
  change ((g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) c) =
    ((U.topIso.hom ≫ X.presheaf.germ U _ _ ≫ U.ι.stalkMap _ ≫
      Scheme.stalkClosedPointTo g) c)
  erw [← Category.assoc U.topIso.hom
    (X.presheaf.germ U _ _ ≫ U.ι.stalkMap _) (Scheme.stalkClosedPointTo g), h]
  rw [hg]
  congr 1

theorem exists_frame_coefficient_germ {X : Scheme.{0}} {A : Type}
    [CommRing A] [IsLocalRing A] (f : Spec (CommRingCat.of A) ⟶ X)
    (L : LineBundle X) :
    ∃ e : (Scheme.Modules.pullback f).obj L.sheaf ≅ O (Spec (CommRingCat.of A)),
      ∀ s : GlobalSections X L.sheaf,
      localCoefficient e (pullbackSection f s) =
        (Scheme.stalkClosedPointTo f) (coefficientGermAt L s (f (IsLocalRing.closedPoint A))) := by
  let F := affineFrameAt L (f (IsLocalRing.closedPoint A))
  have hr : Set.range f ⊆ Set.range F.openSet.1.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open
      F.openSet.1.isOpen F.mem
  let g := IsOpenImmersion.lift F.openSet.1.ι f hr
  have hfac : g ≫ F.openSet.1.ι = f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e, he⟩ := PullbackFrameCoefficient.exists_frame_of_factors_through_open
    F.openSet.1 g F.frame
  have haux (f' : Spec (CommRingCat.of A) ⟶ X) (hf' : g ≫ F.openSet.1.ι = f') :
      ∃ e' : (Scheme.Modules.pullback f').obj L.sheaf ≅ O (Spec (CommRingCat.of A)),
      ∀ s : GlobalSections X L.sheaf,
        localCoefficient e' (pullbackSection f' s) =
          (Scheme.stalkClosedPointTo f')
            ((X.presheaf.germ F.openSet.1 (f' (IsLocalRing.closedPoint A))
              (by rw [← hf']; exact (g (IsLocalRing.closedPoint A)).2))
              (F.openSet.1.topIso.hom (coefficient F.frame (restrictSection F.openSet.1.ι s)))) := by
    subst f'
    refine ⟨e, fun s => ?_⟩
    unfold localCoefficient
    exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom (he s)).trans
      (factor_coefficient_image F.openSet.1 g _)
  exact haux f hfac

theorem sectionOrder_eq_germ_order {X : Scheme.{0}} {A : Type}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : Spec (CommRingCat.of A) ⟶ X)
    [IsDomain (X.presheaf.stalk (f (IsLocalRing.closedPoint A)))]
    [IsDiscreteValuationRing (X.presheaf.stalk (f (IsLocalRing.closedPoint A)))]
    [IsIso (Scheme.stalkClosedPointTo f)]
    (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (e : (Scheme.Modules.pullback f).obj L.sheaf ≅ O (Spec (CommRingCat.of A))) :
    sectionOrder e (pullbackSection f s) =
      IsDiscreteValuationRing.addVal (X.presheaf.stalk (f (IsLocalRing.closedPoint A)))
        (coefficientGermAt L s (f (IsLocalRing.closedPoint A))) := by
  obtain ⟨e', he'⟩ := exists_frame_coefficient_germ f L
  rw [sectionOrder_frame_independent e e', sectionOrder, he']
  exact CurveModelLocalOrder.addVal_ringEquiv
    (asIso (Scheme.stalkClosedPointTo f)).commRingCatIsoToRingEquiv _

end PiExponent.LocalPullbackSectionOrder

end

end OAI
