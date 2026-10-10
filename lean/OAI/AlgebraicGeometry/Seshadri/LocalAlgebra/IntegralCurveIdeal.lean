import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.SmoothSurfaceDimension

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma IntegralCurve.affine_ideal_prime (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens) (hne : Nonempty (C.embedding ⁻¹ᵁ U.1)) :
    (C.embedding.ker.ideal U).IsPrime := by
  have := hne
  rw [Scheme.Hom.ker_apply]
  exact RingHom.ker_isPrime _

lemma IntegralCurve.affine_ideal_not_maximal (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens) (hne : Nonempty (C.embedding ⁻¹ᵁ U.1)) :
    ¬ (C.embedding.ker.ideal U).IsMaximal := by
  intro hmax
  have := hmax
  have : Smooth S.structureMap := SmoothOfRelativeDimension.smooth 2 S.structureMap
  have : JacobsonSpace C.scheme := LocallyOfFiniteType.jacobsonSpace
    (C.embedding ≫ S.structureMap)
  let I := C.embedding.ker.ideal U
  have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
    rw [Scheme.Hom.support_ker]
    exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
  have he : (Set.range C.embedding) ∩ (U.1 : Set S.scheme) =
      {U.2.fromSpec ⟨I,inferInstance⟩} := by
    rw [← hr,C.embedding.ker.coe_support_inter U,← U.2.fromSpec_image_zeroLocus,
      PrimeSpectrum.zeroLocus_eq_singleton]
    exact Set.image_singleton
  obtain ⟨x,hx⟩ := hne
  have hxq : C.embedding x = U.2.fromSpec ⟨I,inferInstance⟩ :=
    Set.mem_singleton_iff.mp (he ▸ ⟨Set.mem_range_self x,hx⟩)
  have hs : (C.embedding ⁻¹ᵁ U.1 : Set C.scheme) = {x} := by
    ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      apply C.embedding.isEmbedding.injective
      exact (Set.mem_singleton_iff.mp (he ▸ ⟨Set.mem_range_self y,hy⟩)).trans hxq.symm
    · rintro rfl
      exact hx
  have ho : IsOpen ({x} : Set C.scheme) := hs ▸ (C.embedding ⁻¹ᵁ U.1).isOpen
  have hc : IsClosed ({x} : Set C.scheme) :=
    isClosed_singleton_of_isLocallyClosed_singleton ho.isLocallyClosed
  have hu : ({x} : Set C.scheme) = Set.univ := by
    rw [← hc.closure_eq]
    exact (ho.dense (Set.singleton_nonempty x)).closure_eq
  have : Subsingleton C.scheme := ⟨fun y z => by
    have hy : y = x := Set.mem_singleton_iff.mp (hu ▸ Set.mem_univ y)
    have hz : z = x := Set.mem_singleton_iff.mp (hu ▸ Set.mem_univ z)
    exact hy.trans hz.symm⟩
  have hd := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dimension] at hd
  norm_num at hd

lemma IntegralCurve.affine_ideal_ne_bot (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens) (hne : Nonempty (C.embedding ⁻¹ᵁ U.1)) :
    C.embedding.ker.ideal U ≠ ⊥ := by
  intro hzero
  have affineOpen : IsAffineOpen U.1 := U.2
  have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
    rw [Scheme.Hom.support_ker]
    exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
  have he := C.embedding.ker.coe_support_inter U
  rw [hr,← affineOpen.fromSpec_image_zeroLocus,hzero,PrimeSpectrum.zeroLocus_bot] at he
  change Set.range C.embedding ∩ (U.1 : Set S.scheme) =
    affineOpen.fromSpec '' (Set.univ : Set (Spec Γ(S.scheme, U.1))) at he
  rw [Set.image_univ,affineOpen.range_fromSpec] at he
  have hsub : (U.1 : Set S.scheme) ⊆ Set.range C.embedding := fun x hx =>
    (he.symm ▸ hx).1
  obtain ⟨x,hx⟩ := hne
  have hd := U.1.isOpen.dense ⟨C.embedding x,hx⟩
  have hall : Set.range C.embedding = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hd.closure_eq]
    exact closure_minimal hsub C.embedding.isClosedEmbedding.isClosed_range
  have hh : IsHomeomorph C.embedding := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨C.embedding.isEmbedding,Set.range_eq_univ.mp hall⟩
  have heq := hh.topologicalKrullDim_eq C.embedding
  have hdS := S.two_le_dimension
  rw [← heq,C.dimension] at hdS
  norm_num at hdS

end
end MaximalSeshadri.Geometry

end

end OAI
