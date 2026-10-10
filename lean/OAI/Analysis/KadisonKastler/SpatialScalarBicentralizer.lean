import OAI.Analysis.KadisonKastler.ModularCoisometryBicentralizer
import OAI.Analysis.KadisonKastler.CanonicalPositiveCone
import OAI.Analysis.KadisonKastler.HilbertConjugation

namespace OAI

/-! # The scalar bicentralizer of the two-ratio product state -/

namespace KadisonKastler

open Generator.Tracial UnitalTomsWinter

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Nontrivial (SpatialHilbert H K)] [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {Ω : H} {ξ : K}

local instance spatialScalarRealInner : InnerProductSpace ℝ (SpatialHilbert H K) :=
  InnerProductSpace.complexToReal

theorem PointedMatrixSites.spatial_state_bicentralizer_scalar
    (P : PointedMatrixSites N ξ twoRatioSiteParameter)
    (hunit : ‖Ω‖=1) (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (hIII : TypeIIIFactor (spatialProductAlgebra M N))
    (a : Algebra (spatialProductAlgebra M N))
    (ha : stateBicentralizerMember (tensorVector ξ Ω) a) :
    ∃ z : ℂ, a=z • 1 := by
  let S := spatialProductAlgebra M N
  let ψ := tensorVector ξ Ω
  have hs : Function.Injective (algebraVectorMap S ψ) :=
    separating_spatialProduct_vector_of_separating M N Ω ξ hsep P.separating
  have hc : DenseRange (algebraVectorMap S ψ) :=
    denseRange_spatialProduct_vector M N Ω ξ hcyc P.cyclic
  obtain ⟨J,_⟩ := exists_hilbert_conjugation (H := SpatialHilbert H K)
  let L := tomitaPolarConjugation J ψ hs hc
  have hL : Function.Involutive L := tomitaPolarConjugation_involutive J ψ hs hc
  have hright : ∀ b : Algebra S, conjugationOperator L b.val∈S.commutant :=
    tomitaPolarConjugation_right_mem J ψ hs hc
  have hleft : ∀ b : Algebra S.commutant, conjugationOperator L b.val∈S := by
    intro b
    let T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K := b.val
    have hb : T∈(S.commutant : Set (SpatialHilbert H K →L[ℂ] SpatialHilbert H K)) := b.property
    rw [← tomitaPolarConjugation_commutant_eq J ψ hs hc,conjugateRightAlgebra_coe] at hb
    obtain ⟨c,hcS,he⟩ := hb
    change conjugationOperator L c=T at he
    change conjugationOperator L T∈S
    rw [← he,conjugationOperator_twice _ hL]
    exact hcS
  apply state_bicentralizer_scalar_of_modular_coisometries L hL hright hleft ψ
    (tomitaPolarConjugation_fixes_vector J ψ hs hc) ?_ hs ?_ hIII
    (P.spatial_universal_modular_coisometries hsep hcyc J) a ha
  · change ‖tensorVector ξ Ω‖=1
    rw [norm_tensorVector_apply,hunit,P.unit_vector,mul_one]
  · intro b
    exact (tomitaPolarConjugation_quadratic_nonneg J ψ hs hc b).1

end

end KadisonKastler

end OAI
