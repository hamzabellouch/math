import OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension
import OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionMinimalSum

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentJets.W28.LocalIntersection
open scoped nonZeroDivisors

theorem stalk_krullDimLE_one (X : Scheme.{0})
    (hd : topologicalKrullDim X ≤ 1) (x : X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk x) := by
  apply Ring.krullDimLE_iff.mpr
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (X.fromSpecStalk x).isEmbedding.isInducing.topologicalKrullDim_le.trans hd

theorem sectionGerm_nonZeroDivisor {X : Scheme.{0}}
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (x : X) (hx : x ∈ U.1) :
    SectionZeroStalk.sectionGerm L s U e x hx ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  let := X.presheaf.algebra_section_stalk (⟨x,hx⟩ : U.1)
  let := U.2.isLocalization_stalk (⟨x,hx⟩ : U.1)
  exact IsLocalization.nonZeroDivisors_le_comap
    ((U.2.primeIdealOf ⟨x,hx⟩).asIdeal.primeCompl) (X.presheaf.stalk x)
    (NumericalAmpleness.section_affine_coefficient_nonZeroDivisor L s U e)

theorem zero_stalk_length_eq_minimalPrimeCutSum {X : Scheme.{0}}
    [IsLocallyNoetherian X] (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1) :
    Module.length ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y)
      ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y) =
    minimalPrimeCutSum (⊥ : Ideal
      (X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y)))
      (SectionZeroStalk.sectionGerm L s U e _ hy) := by
  let x := (SectionZeroIdeal.zeroIdeal L s).subschemeι y
  let A := X.presheaf.stalk x
  let c : A := SectionZeroStalk.sectionGerm L s U e x hy
  let := stalk_krullDimLE_one X hd x
  have hlen := SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (SectionZeroStalk.zeroStalkQuotientEquiv L s U e y hy)
  have hsc : Module.length A (A ⧸ Ideal.span {c}) =
      Module.length (A ⧸ Ideal.span {c}) (A ⧸ Ideal.span {c}) :=
    Module.length_eq_of_surjective (M := A ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective
  exact hlen.symm.trans (hsc.symm.trans
    (regular_ring_onecut_length c (sectionGerm_nonZeroDivisor L s U e x hy)))

theorem zero_stalk_length_ne_top {X : Scheme.{0}} [IsLocallyNoetherian X]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme) :
    Module.length ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y)
      ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y) ≠ ⊤ := by
  let x := (SectionZeroIdeal.zeroIdeal L s).subschemeι y
  obtain ⟨V,hxV,⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨W,hW,hxW,hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let U : X.affineOpens := ⟨W,hW⟩
  let e := restrictOpenFrame hWV eV
  let A := X.presheaf.stalk x
  let c : A := SectionZeroStalk.sectionGerm L s U e x hxW
  let := stalk_krullDimLE_one X hd x
  have hfinite : IsFiniteLength A (A ⧸ Ideal.span {c}) :=
    isFiniteLength_quotient_span_singleton A (sectionGerm_nonZeroDivisor L s U e x hxW)
  have hsc : Module.length A (A ⧸ Ideal.span {c}) =
      Module.length (A ⧸ Ideal.span {c}) (A ⧸ Ideal.span {c}) :=
    Module.length_eq_of_surjective (M := A ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective
  have hlen := SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (SectionZeroStalk.zeroStalkQuotientEquiv L s U e y hxW)
  rw [← hlen,← hsc]
  exact Module.length_ne_top_iff.mpr hfinite

end
end PiExponent.CurveCycle

end OAI
