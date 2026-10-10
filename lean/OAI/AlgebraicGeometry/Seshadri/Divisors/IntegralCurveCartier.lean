import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.CartierModule
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.SmoothCurvePrincipal
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.IntegralCurveIdeal

namespace OAI


                                              
section

namespace MaximalSeshadri.LocalCurve
noncomputable section

lemma rational_of_maximal {K R : Type} [Field K] [IsAlgClosed K]
    [CommRing R] [Algebra K R] [Algebra.FiniteType K R]
    (q : Ideal R) [q.IsMaximal] : ∃ ρ : R →ₐ[K] K, RingHom.ker ρ = q := by
  let : Field (R ⧸ q) := Ideal.Quotient.field q
  let : Module.Finite K (R ⧸ q) := finite_of_finite_type_of_isJacobsonRing K _
  let φ : (R ⧸ q) →ₐ[K] K := IsAlgClosed.lift
  let ρ := φ.comp (Ideal.Quotient.mkₐ K q)
  refine ⟨ρ, ?_⟩
  ext x
  change φ (Ideal.Quotient.mk q x) = 0 ↔ x ∈ q
  change φ.toRingHom (Ideal.Quotient.mk q x) = 0 ↔ x ∈ q
  rw [← map_zero φ.toRingHom, φ.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

end
end MaximalSeshadri.LocalCurve

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma IntegralCurve.equation_at_support (S : Surface) (C : IntegralCurve S)
    (x : C.scheme) : ∃ U : S.scheme.affineOpens, C.embedding x ∈ U.1 ∧
      ∃ c : Γ(S.scheme,U.1), IsRegular c ∧ C.embedding.ker.ideal U = Ideal.span {c} := by
  obtain ⟨U,hxU,-,hstd⟩ := exists_standard_smooth_affine_inside S.structureMap 2
    ⊤ (C.embedding x) (by trivial)
  let := (openScalars S.structureMap U.1).toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ Γ(S.scheme,U.1) := hstd
  let : Algebra.IsStandardSmooth ℂ Γ(S.scheme,U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2
  let : Nonempty (C.embedding ⁻¹ᵁ U.1) := ⟨⟨x,hxU⟩⟩
  let : Nonempty U.1 := ⟨⟨_,hxU⟩⟩
  let I := C.embedding.ker.ideal U
  let : I.IsPrime := C.affine_ideal_prime S U inferInstance
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hxrange : C.embedding x ∈ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]; exact hxU
  obtain ⟨p,hp⟩ := hxrange
  have hIp : I ≤ p.asIdeal := by
    have hz : p ∈ PrimeSpectrum.zeroLocus I := by
      have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
        rw [Scheme.Hom.support_ker]
        exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
      have hh : C.embedding x ∈ (C.embedding.ker.support : Set S.scheme) ∩ U.1 :=
        ⟨hr ▸ Set.mem_range_self x,hxU⟩
      rw [C.embedding.ker.coe_support_inter U,← U.2.fromSpec_image_zeroLocus] at hh
      obtain ⟨p',hp',he⟩ := hh
      have ep : p' = p := U.2.fromSpec.isOpenEmbedding.injective (he.trans hp.symm)
      subst p'
      exact hp'
    exact hz
  obtain ⟨q,hq,hpq⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let := hq
  obtain ⟨ρ,hρ⟩ := LocalCurve.rational_of_maximal (K := ℂ) q
  have hIq : I ≠ RingHom.ker ρ := by
    rw [hρ]
    intro he
    exact C.affine_ideal_not_maximal S U inferInstance (by change I.IsMaximal; rw [he]; exact hq)
  obtain ⟨c,hc,s,hs,he⟩ := LocalCurve.standard_smooth_prime_principal_neighborhood
    ρ I (hρ.symm ▸ hIp.trans hpq) hIq
  let V : S.scheme.affineOpens := ⟨S.scheme.basicOpen s,U.2.basicOpen s⟩
  have hxV : C.embedding x ∈ V.1 := by
    have hz : p ∈ PrimeSpectrum.basicOpen s := fun hh =>
      hs (show s ∈ RingHom.ker ρ from hρ.symm ▸ hpq hh)
    rw [← U.2.fromSpec_preimage_basicOpen] at hz
    change U.2.fromSpec p ∈ S.scheme.basicOpen s at hz
    rwa [hp] at hz
  let : Nonempty (C.embedding ⁻¹ᵁ V.1) := ⟨⟨x,hxV⟩⟩
  let : Nonempty V.1 := ⟨⟨_,hxV⟩⟩
  let : IsLocalization.Away s Γ(S.scheme,V.1) := U.2.isLocalization_basicOpen s
  let e := IsLocalization.algEquiv (Submonoid.powers s)
    (Localization.Away s) Γ(S.scheme,V.1)
  let c' : Γ(S.scheme,V.1) := algebraMap Γ(S.scheme,U.1) Γ(S.scheme,V.1) c
  have he' : C.embedding.ker.ideal V = Ideal.span {c'} := by
    have H := congrArg (Ideal.map e.toRingHom) he
    rw [Ideal.map_map,Ideal.map_span,Set.image_singleton] at H
    have comp : e.toRingHom.comp (algebraMap Γ(S.scheme,U.1) (Localization.Away s)) =
        algebraMap Γ(S.scheme,U.1) Γ(S.scheme,V.1) := by
      ext z; exact e.commutes z
    change I.map (e.toRingHom.comp (algebraMap Γ(S.scheme,U.1) (Localization.Away s))) =
      Ideal.span {e (algebraMap Γ(S.scheme,U.1) (Localization.Away s) c)} at H
    rw [comp,e.commutes] at H
    exact (C.embedding.ker.map_ideal_basicOpen U s).symm.trans H
  have hc' : c' ≠ 0 := by
    intro hz
    have H := C.affine_ideal_ne_bot S V inferInstance
    rw [he',hz,Ideal.span_singleton_zero] at H
    exact H rfl
  exact ⟨V,hxV,c',isRegular_iff_ne_zero.mpr hc',he'⟩

theorem IntegralCurve.invertible_ideal (S : Surface) (C : IntegralCurve S) :
    InvertiblePullbackIdeal C.embedding.ker (𝟙 S.scheme) := by
  apply InvertibleLocal.invertible_of_affine_equations
  intro x
  by_cases hx : x ∈ Set.range C.embedding
  · obtain ⟨z,rfl⟩ := hx
    exact C.equation_at_support S z
  · let W : S.scheme.Opens := ⟨(Set.range C.embedding)ᶜ,
      C.embedding.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨U,hU,hxU,hUW⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ W from hx)
    have htop : C.embedding.ker.ideal ⟨U,hU⟩ = ⊤ := by
      apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
      rw [Set.eq_empty_iff_forall_notMem]
      intro p hp
      have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
        rw [Scheme.Hom.support_ker]
        exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
      have hz : hU.fromSpec p ∈ (C.embedding.ker.support : Set S.scheme) ∩ U := by
        rw [C.embedding.ker.coe_support_inter ⟨U,hU⟩,← hU.fromSpec_image_zeroLocus]
        exact ⟨p,hp,rfl⟩
      exact hUW hz.2 (hr ▸ hz.1)
    exact ⟨⟨U,hU⟩,hxU,1,isRegular_one,by rw [htop,Ideal.span_singleton_one]⟩

end
end MaximalSeshadri.Geometry

end


end OAI
