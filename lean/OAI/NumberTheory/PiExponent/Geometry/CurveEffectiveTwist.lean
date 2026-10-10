import OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration
import OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections
import OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws
import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent
import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct

namespace OAI

namespace PiExponent.CurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}} [IsIntegral X]

private theorem id_eq_zero_of_iso {C : Type*} [Category C] [Preadditive C]
    {A B : C} (e : A ≅ B) (h : 𝟙 A = 0) : 𝟙 B = 0 := by
  have he := congrArg (fun f : A ⟶ A => e.inv ≫ f ≫ e.hom) h
  simpa only [Category.id_comp, comp_zero, zero_comp, Iso.inv_hom_id] using he

private theorem generators_isZero {T : TopCat.{0}} (R : Sheaf (Opens.grothendieckTopology T) RingCat.{0})
    (M : SheafOfModules.{0} R) (G : M.GeneratingSections)
    (h : ∀ s : SheafOfModules.unit.{0} R ⟶ M, s = 0) : IsZero M := by
  have hπ : G.π = 0 := by
    apply M.freeHomEquiv.injective
    funext i
    apply M.unitHomEquiv.symm.injective
    rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
      SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simpa only [comp_zero] using h (SheafOfModules.ιFree i ≫ G.π)
  let : Epi G.π := G.epi
  exact IsZero.of_epi_eq_zero G.π hπ

theorem lineBundle_not_isZero (L : LineBundle X) : ¬ IsZero L.sheaf := by
  intro h
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hL : (𝟙 L.sheaf) = 0 := h.eq_of_src _ _
  have hr := congrArg (Scheme.Modules.restrictFunctor U.ι).map hL
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at hr
  have hid : (𝟙 (O U.toScheme)) = 0 := by
    simpa only [O] using! id_eq_zero_of_iso e hr
  have hh := congrArg (endValue (X := U.toScheme)) hid
  simp only [endValue] at hh
  exact one_ne_zero (show (1 : Γ(U.toScheme, ⊤)) = 0 from hh)

omit [IsIntegral X] in

theorem section_ne_zero_of_mem_isoOpen (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (x : X) (hx : x ∈ isoOpen s) : s ≠ 0 := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  have hm : (⟨x, hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ isoOpen s := hx
  rw [preimage_isoOpen s U.ι e] at hm
  intro hz
  subst s
  have hrestrict : restrictSection U.ι (0 : O X ⟶ L.sheaf) = 0 := by
    simpa only [restrictSection] using restrictSection_zero (M := L.sheaf) U.ι
  have hz := (congrArg (coefficient e) hrestrict).trans (coefficient_zero e)
  erw [hz, Scheme.basicOpen_zero] at hm
  exact hm

theorem nonzero_section_of_generators (L : LineBundle X) (G : L.sheaf.GeneratingSections) :
    ∃ s : GlobalSections X L.sheaf, s ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact lineBundle_not_isZero L (generators_isZero X.ringCatSheaf L.sheaf G h)

def twistLineIso (H L : LineBundle X) (n : ℕ) :
    (moduleTwistFunctor H n).obj L.sheaf ≅ ((H.pow n).tensor L).sheaf :=
  moduleTwistPowerIso H L.sheaf n ≪≫
    moduleTensorComm L.sheaf (modulePow X H.sheaf n)

theorem exists_effective_twist [NoetherianSpace X]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) :
    ∃ A : LineBundle X,
      (∃ t : GlobalSections X A.sheaf, t ≠ 0) ∧
      (∃ u : GlobalSections X (A.tensor L).sheaf, u ≠ 0) := by
  obtain ⟨d, hd, k, s, hcover, haffine, hcoverData⟩ := H.ample_common_degree_cover hH
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  obtain ⟨N, hN⟩ := AmpleGlobalGeneration.eventual_global_generators_of_section_cover
    (H.pow d) L.sheaf s hcover haffine
  obtain ⟨G, hG⟩ := hN N le_rfl
  let A := (H.pow d).pow N
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, sectionOpen X (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let t := powerSection (s i) N
  have ht : t ≠ 0 := section_ne_zero_of_mem_isoOpen A t x
    (sectionOpen_le_powerSection (s i) N hi)
  have hu := nonzero_section_of_generators (A.tensor L)
    (SheafOfModules.GeneratingSections.equivOfIso (twistLineIso (H.pow d) L N) G)
  exact ⟨A, ⟨t, ht⟩, hu⟩

end
end PiExponent.CurveDegree

end OAI
