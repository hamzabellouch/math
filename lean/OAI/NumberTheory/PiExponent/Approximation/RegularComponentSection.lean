import OAI.NumberTheory.PiExponent.Approximation.FramedPullback
import OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections
import OAI.NumberTheory.PiExponent.Approximation.LinePullback
import OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity
import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct
import OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroStalk


variable {X Y : Scheme.{0}}

theorem exists_pullback_frame_sectionGerm (f : Y ⟶ X) [IsAffineHom f]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    ∃ eF : (L.pullback f).sheaf.restrict (f ⁻¹ᵁ U.1).ι ≅ O (f ⁻¹ᵁ U.1).toScheme,
      ∀ (y : Y) (hy : f y ∈ U.1),
        sectionGerm (L.pullback f) (pullbackSection f s)
          ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩ eF y hy =
        f.stalkMap y (sectionGerm L s U e (f y) hy) := by
  obtain ⟨eF, he⟩ := exists_restricted_pullback_frame f U.1 e s
  refine ⟨eF, ?_⟩
  intro y hy
  have hr (a : Γ(U.1.toScheme, ⊤)) :
      (f ⁻¹ᵁ U.1).topIso.hom ((f ∣_ U.1).appTop a) =
        f.app U.1 (U.1.topIso.hom a) := by
    change (f ⁻¹ᵁ U.1).topIso.hom ((f ∣_ U.1).app ⊤ a) = _
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_app_top]
    simp only [Scheme.Hom.appLE_eq_app]
    exact CategoryTheory.congr_fun (f ⁻¹ᵁ U.1).topIso.inv_hom_id _
  unfold sectionGerm
  erw [he, hr, Scheme.Hom.germ_stalkMap_apply]

private theorem sectionGerm_zero (L : LineBundle X) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) (x : X) (hx : x ∈ U.1) :
    sectionGerm L 0 U e x hx = 0 := by
  simp only [sectionGerm]
  erw [restrictSection_zero, coefficient, CategoryTheory.Limits.zero_comp]
  simp only [endValue]
  change X.presheaf.germ U.1 x hx (U.1.topIso.hom 0) = 0
  simp only [map_zero]

theorem regular_component_section_ne_zero (X : Scheme.{0}) (C : irreducibleComponents X)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    pullbackSection (reducedComponentι X C) s ≠ 0 := by
  let f := reducedComponentι X C
  let z : reducedComponent X C := genericPoint (reducedComponent X C)
  obtain ⟨U, hz, ⟨e⟩, _⟩ := common_affine_frames L L (f z)
  obtain ⟨eF, heF⟩ := exists_pullback_frame_sectionGerm f L s U e
  have hne := reducedComponentι_stalkMap_ne_zero X C z
    (sectionGerm L s U e (f z) hz) (sectionGerm_nonZeroDivisor L s U e (f z) hz)
  intro hs
  apply hne
  rw [← heF z hz, hs]
  exact sectionGerm_zero _ _ _ _ _

theorem regular_component_section_mono (X : Scheme.{0}) (C : irreducibleComponents X)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    Mono (pullbackSection (reducedComponentι X C) s) :=
  (L.pullback (reducedComponentι X C)).mono_section _
    (regular_component_section_ne_zero X C L s)

end
end PiExponent.CurveCycle

end OAI
