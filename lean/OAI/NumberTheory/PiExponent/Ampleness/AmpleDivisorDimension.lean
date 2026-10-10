import OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase
import OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrincipalQuotientDimension

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
open PiExponent.SectionZeroIdeal

variable {X Y : Scheme.{0}}

theorem sectionZero_pullback_dimension_le (H : LineBundle X)
    (s : GlobalSections X H.sheaf) (i : Y ⟶ X) [IsClosedImmersion i] :
    topologicalKrullDim (zeroIdeal (H.pullback i) (pullbackSection i s)).subscheme ≤
      topologicalKrullDim (zeroIdeal H s).subscheme := by
  let I := zeroIdeal H s
  let J := zeroIdeal (H.pullback i) (pullbackSection i s)
  have hmap (z : J.subscheme) : i (J.subschemeι z) ∈ (I.support : Set X) := by
    have hz := z.property
    change J.subschemeι z ∈ (J.support : Set Y) at hz
    erw [zeroIdeal_support] at hz ⊢
    change J.subschemeι z ∉ isoOpen (pullbackSection i s) at hz
    rw [pullback_isoOpen_eq H s i] at hz
    exact hz
  have he := (i.isEmbedding.comp J.subschemeι.isEmbedding).codRestrict
    (I.support : Set X) hmap
  exact he.isInducing.topologicalKrullDim_le

theorem sectionZero_dimension_succ_ge_of_zero [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType p]
    (H : LineBundle X) (s : GlobalSections X H.sheaf)
    (y : X) (hy : y ∉ sectionOpen X s) :
    topologicalKrullDim X ≤ topologicalKrullDim (zeroIdeal H s).subscheme + 1 := by
  obtain ⟨V, hyV, ⟨eV⟩⟩ := H.locallyRankOne y
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset hyV
  let U : X.affineOpens := ⟨W, hW⟩
  let e := restrictOpenFrame hWV eV
  let : Nonempty U.1 := ⟨⟨y, hyW⟩⟩
  let a : Γ(X,U) := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
  have ha : ¬ IsUnit a := by
    intro ha
    have hc : IsUnit (coefficient e (restrictSection U.1.ι s)) := by
      have hh := ha.map U.1.topIso.inv.hom
      simpa only [a, ← CommRingCat.comp_apply, Iso.hom_inv_id,
        CommRingCat.id_apply] using hh
    have hopen := preimage_isoOpen s U.1.ι e
    rw [U.1.toScheme.basicOpen_of_isUnit hc] at hopen
    have hm : (⟨y,hyW⟩ : U.1.toScheme) ∈ U.1.ι ⁻¹ᵁ isoOpen s :=
      hopen.ge trivial
    exact hy hm
  let := IntegralAffineOpenDimension.chartAlgebra p U
  let := IntegralAffineOpenDimension.chart_finiteType p U
  have hdrop := GeometrySupport.PrincipalQuotientDimension.le_quotient_succ
    ℂ Γ(X,U) a ha
  rw [← zeroIdeal_on_frame H s U e] at hdrop
  rw [IntegralAffineOpenDimension.affine_ring_dimension_eq p U] at hdrop
  let I := zeroIdeal H s
  have hquot : ringKrullDim (Γ(X,U) ⧸ I.ideal U) ≤
      topologicalKrullDim I.subscheme := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    let : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
    exact (I.subschemeCover.f U).isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  exact hdrop.trans (add_le_add hquot le_rfl)

theorem regular_ample_sectionZero_dimension
    [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (s : GlobalSections X H.sheaf) [Mono s] (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1 : ℕ) : WithBot ℕ∞)) :
    Nonempty (zeroIdeal H s).subscheme ∧
      topologicalKrullDim (zeroIdeal H s).subscheme = d := by
  refine ⟨ample_section_zero_nonempty p H hH s (d+1) hdim (Nat.succ_pos d), ?_⟩
  apply le_antisymm
  · apply regular_sectionZero_dimension_le H s d
    simpa only [Nat.cast_add, Nat.cast_one] using hdim.le
  · obtain ⟨Y, i, hi, hY, hdimY⟩ := exists_integral_closed_full_dimension X (d+1) hdim
    let := hi
    let := hY
    have hample := LineBundle.IsAmple.pullback_closedImmersion H hH i
    obtain ⟨y, hy⟩ := ample_section_has_zero (i ≫ p) (H.pullback i) hample
      (pullbackSection i s) (d+1) hdimY (Nat.succ_pos d)
    have hlow := sectionZero_dimension_succ_ge_of_zero (i ≫ p)
      (H.pullback i) (pullbackSection i s) y hy
    rw [hdimY] at hlow
    have hbound := hlow.trans (add_le_add (sectionZero_pullback_dimension_le H s i) le_rfl)
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    simpa only [Nat.cast_add, Nat.cast_one] using hbound

end
end PiExponent.NumericalAmpleness

end OAI
