import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtaleDimension
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.LocalDimension
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PullbackSectionOpenExact
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtaleLowerDimension
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionCoefficientOrder
import OAI.AlgebraicGeometry.Seshadri.Sheaves.EtaleLineFrame
import OAI.AlgebraicGeometry.Seshadri.Geometry.IntegralImage

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma pullback_zero_of_range (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (f : Y ⟶ X) [IsIntegral Y] (h : ∀ y, f y ∉ isoOpen s) :
    pullbackSection f s = 0 := by
  let pulledSection : O Y ⟶ (L.pullback f).sheaf := pullbackSection f s
  have htopen : isoOpen pulledSection = f ⁻¹ᵁ isoOpen s := pullback_isoOpen_eq L s f
  change pulledSection = 0
  by_contra hn
  apply (L.pullback f).isoOpen_ne_bot pulledSection hn
  rw [htopen]
  apply bot_unique
  intro y hy
  exact (h y hy).elim

lemma affineCoefficient_basicOpen (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    X.basicOpen (affineCoefficient U e s) = U.1 ⊓ isoOpen s := by
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv]
  have he : U.1.topIso.inv (affineCoefficient U e s) =
      coefficient e (restrictSection U.1.ι s) := by
    exact ConcreteCategory.congr_hom U.1.topIso.hom_inv_id _
  rw [he,← preimage_isoOpen s U.1.ι e]
  ext x
  change (∃ q : U.1.toScheme, q.1 ∈ isoOpen s ∧ q.1 = x) ↔ _
  constructor
  · rintro ⟨q,hq,rfl⟩; exact ⟨q.property,hq⟩
  · rintro ⟨hx,hq⟩; exact ⟨⟨x,hx⟩,hq,rfl⟩

lemma Surface.annihilated_subscheme_dimension (S : Surface)
    (L : LineBundle S.scheme) (s : O S.scheme ⟶ L.sheaf) (hs : s ≠ 0)
    (I : S.scheme.IdealSheafData) (hi : pullbackSection I.subschemeι s = 0) :
    topologicalKrullDim I.subscheme ≤ 1 := by
  apply subscheme_dimension_le_of_affine_neighborhoods
  intro x
  obtain ⟨U,hx,-,e,t,het⟩ := S.etale_line_frame_inside L ⊤ (I.subschemeι x) (by trivial)
  let : Nonempty U.1 := ⟨⟨_,hx⟩⟩
  let φ := MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t
  let : Algebra (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := φ.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := het
  have hd := MaximalSeshadri.EtaleDimension.etale_surface_dimension_le ℂ Γ(S.scheme,U.1)
  let a := affineCoefficient U e s
  have ha : a ≠ 0 := (isRegular_iff_ne_zero).mp (L.section_coefficient_regular s hs U e)
  have ham : a ∈ I.ideal U := pullback_zero_coefficient_mem S.structureMap I L s hi U e
  refine ⟨U,hx,ENat.WithBot.add_le_add_one_right_iff.mp ?_⟩
  exact (ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (I.ideal U))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
      (Ideal.Quotient.eq_zero_iff_mem.mpr ham)).trans hd

lemma residue_image_one_le (X : Scheme.{0}) (x y : X) (hxy : x ⤳ y) (hne : x ≠ y) :
    1 ≤ topologicalKrullDim (X.fromSpecResidueField x).image := by
  let f := (X.fromSpecResidueField x).imageι
  have hx : x ∈ Set.range f := (residue_image_range X x).symm ▸ subset_closure (Set.mem_singleton x)
  have hy : y ∈ Set.range f := (residue_image_range X x).symm ▸ hxy.mem_closure
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  rw [scheme_dimension_eq_point_dimension,Order.one_le_krullDim_iff]
  refine ⟨b,a,lt_iff_le_not_ge.mpr ⟨?_,?_⟩⟩
  · apply Scheme.le_iff_specializes.mpr
    apply f.isEmbedding.isInducing.specializes_iff.mp
    rwa [ha,hb]
  · intro he
    apply hne
    have hba : y ⤳ x := by
      have H := (Scheme.le_iff_specializes.mp he).map f.continuous
      rwa [ha,hb] at H
    exact (hxy.antisymm hba).eq

theorem Surface.section_contains_curve (S : Surface) (L : LineBundle S.scheme)
    (s : O S.scheme ⟶ L.sheaf) (hs : s ≠ 0)
    (U : S.scheme.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (t : Fin 2 → Γ(S.scheme,U.1))
    (het : (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra; Γ(S.scheme,U.1) →ₐ[ℂ] ℂ)
    (hρ : ρ (affineCoefficient U e s) = 0) :
    ∃ C : IntegralCurve S, pullbackSection C.embedding s = 0 := by
  classical
  let := (openScalars S.structureMap U.1).toAlgebra
  let φ := MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t
  let : Algebra (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := φ.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change openScalars S.structureMap U.1 z = φ (MvPolynomial.C z)
      simp [φ])
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := het
  let a := affineCoefficient U e s
  let J := Ideal.span {a}
  have hd := MaximalSeshadri.EtaleDimension.etale_principal_dimension_lower ℂ Γ(S.scheme,U.1)
    (Fin 2) ρ a hρ
  have hd' : 1 ≤ ringKrullDim (Γ(S.scheme,U.1) ⧸ J) := by
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    convert hd using 1
    norm_num [J]
  rw [ringKrullDim_quotient,Order.one_le_krullDim_iff] at hd'
  obtain ⟨x,y,hxy⟩ := hd'
  let z := U.2.fromSpec x.val
  let w := U.2.fromSpec y.val
  have hzw : z ⤳ w :=
    ((PrimeSpectrum.le_iff_specializes x.val y.val).mp hxy.le).map U.2.fromSpec.continuous
  have hne : z ≠ w := by
    let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    have hinj : Function.Injective U.2.fromSpec := U.2.fromSpec.isOpenEmbedding.injective
    intro h
    exact hxy.ne (Subtype.ext (hinj h))
  have hz : z ∉ isoOpen s := by
    intro h
    have hxU : z ∈ U.1 := by
      have H := Set.mem_range_self (f := U.2.fromSpec) x.val
      rwa [U.2.range_fromSpec] at H
    have H : z ∈ S.scheme.basicOpen a := by
      rw [affineCoefficient_basicOpen L s U e]; exact ⟨hxU,h⟩
    have H' : x.val ∈ PrimeSpectrum.basicOpen a := by
      rw [← U.2.fromSpec_preimage_basicOpen]
      exact H
    exact H' (x.property (Ideal.subset_span (Set.mem_singleton a)))
  let g := S.scheme.fromSpecResidueField z
  let := residue_image_integral S.scheme z
  have hzero : pullbackSection g.imageι s = 0 := by
    apply pullback_zero_of_range L s
    intro q
    have hq : g.imageι q ∈ closure {z} :=
      (residue_image_range S.scheme z) ▸ Set.mem_range_self q
    exact closure_minimal (Set.singleton_subset_iff.mpr hz) (isoOpen s).isOpen.isClosed_compl hq
  have hdim : topologicalKrullDim g.image = 1 := le_antisymm
    (S.annihilated_subscheme_dimension L s hs g.ker hzero)
    (residue_image_one_le S.scheme z w hzw hne)
  exact ⟨⟨g.image,g.imageι,inferInstance,inferInstance,hdim⟩,hzero⟩
end
end MaximalSeshadri.Geometry

end

end OAI
