import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting
import OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens
import OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem power_nonvanishing_sections_of_divisor_lifts
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ)
    (hlift : Function.Surjective
      (fun t : GlobalSections X (L.pow n).sheaf =>
        pullbackSection (zeroIdeal L s).subschemeι t))
    (hgenerate : ∀ y : (zeroIdeal L s).subscheme, ∃ σ :
      GlobalSections (zeroIdeal L s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow n).sheaf),
      y ∈ sectionOpen (zeroIdeal L s).subscheme σ) :
    ∀ x : X, ∃ t : GlobalSections X (L.pow n).sheaf, x ∈ sectionOpen X t := by
  intro x
  by_cases hx : x ∈ sectionOpen X s
  · exact ⟨powerSection s n, sectionOpen_le_powerSection s n hx⟩
  · have hxI : x ∈ (zeroIdeal L s).support := by
      change x ∈ ((zeroIdeal L s).support : Set X)
      rw [zeroIdeal_support]
      exact hx
    have hr : x ∈ Set.range (zeroIdeal L s).subschemeι := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    obtain ⟨y,rfl⟩ := hr
    obtain ⟨σ,hσ⟩ := hgenerate y
    obtain ⟨t,ht⟩ := hlift σ
    change pullbackSection (zeroIdeal L s).subschemeι t = σ at ht
    refine ⟨t,?_⟩
    have he := pullback_isoOpen_eq (L.pow n) t (zeroIdeal L s).subschemeι
    rw [ht] at he
    change y ∈ (zeroIdeal L s).subschemeι ⁻¹ᵁ PiExponentSeshadri.SectionOpens.isoOpen t
    exact he.le hσ

theorem finite_section_cover_of_pointwise [CompactSpace X] (L : LineBundle X)
    (h : ∀ x : X, ∃ t : GlobalSections X L.sheaf, x ∈ sectionOpen X t) :
    ∃ l : ℕ, ∃ t : Fin l → GlobalSections X L.sheaf,
      (⨆ j, sectionOpen X (t j)) = ⊤ := by
  classical
  choose t ht using h
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (t x) : Set X)) (fun x => (sectionOpen X (t x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,ht x⟩)
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,fun j => t (e j).val,?_⟩
  apply top_unique
  intro x _
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
  obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
  apply Opens.mem_iSup.mpr
  refine ⟨e.symm ⟨i,hi⟩,?_⟩
  change x ∈ sectionOpen X (t (e (e.symm ⟨i,hi⟩)).val)
  rw [Equiv.apply_symm_apply]
  exact hx

theorem eventual_power_section_cover_of_divisor [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s]
    (hfinite : ∀ n, letI := Module.compHom (cohomology (L.pow n).sheaf 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).sheaf 1))
    (hzero : ∃ N, ∀ n, N ≤ n → ∀ z :
      cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) 1,
      z = 0)
    (hgenerate : ∃ N, ∀ n, N ≤ n → ∀ y : (zeroIdeal L s).subscheme, ∃ σ :
      GlobalSections (zeroIdeal L s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf),
      y ∈ sectionOpen (zeroIdeal L s).subscheme σ) :
    ∃ N, ∀ n, N ≤ n → ∃ l : ℕ, ∃ t : Fin l → GlobalSections X (L.pow (n+1)).sheaf,
      (⨆ j, sectionOpen X (t j)) = ⊤ := by
  obtain ⟨N,hN⟩ := eventual_cartier_restriction_section_lifting p L s hfinite hzero
  obtain ⟨K,hK⟩ := hgenerate
  refine ⟨max N K,fun n hn => ?_⟩
  apply finite_section_cover_of_pointwise (L.pow (n+1))
  exact power_nonvanishing_sections_of_divisor_lifts L s (n+1)
    (hN n ((le_max_left N K).trans hn)) (hK n ((le_max_right N K).trans hn))

end
end PiExponent.NumericalAmpleness

end OAI
