import OAI.Analysis.KadisonKastler.ExpectedFromBicentralizer
import OAI.Analysis.KadisonKastler.CanonicalPositiveCone
import OAI.Analysis.KadisonKastler.ConstructedModularData
import OAI.Analysis.KadisonKastler.HilbertConjugation

namespace OAI

/-! # State-theoretic hypotheses for the expected subfactor

Connes–Størmer, *Homogeneity of the state space of factors of type III₁*,
J. Functional Analysis 28 (1978), 187–196, main state-orbit transitivity
theorem, gives the faithful vector-state specialization below.

Marrakchi, *Full factors, bicentralizer flow and approximately inner
automorphisms*, arXiv:1811.10253v2, Theorem D(ii), gives the second input.
It is stated only for the fixed Powers product used by the application.

Together, these hypotheses imply the existence of the full expected
matrix subfactor, without an additional relative-algebra hypothesis.
-/

namespace KadisonKastler

open Generator

noncomputable section

universe u

def PublishedTypeIII1StateHomogeneity : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H), TypeIII1Factor M → FaithfulVectorStateHomogeneity M

def PublishedPowersAbsorptionBicentralizer : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H), TypeIII1Factor M →
    ∀ R : PointedMatrixProduct.{u} (fun _ : ℕ => fixedProductLambda),
      Nonempty (Algebra (spatialProductAlgebra M R.algebra) ≃⋆ₐ[ℂ] Algebra M) →
      FaithfulVectorBicentralizersScalar M

theorem publishedExpectedMatrixSubfactor_of_state_inputs
    (hhom : PublishedTypeIII1StateHomogeneity.{u})
    (hbic : PublishedPowersAbsorptionBicentralizer.{u}) :
    PublishedExpectedMatrixSubfactor.{u} := by
  intro H _ _ _ _ _ M hM R hR
  obtain ⟨ξ,hunit,hcyc,hsep⟩ := hM.toTypeIIIFactor.exists_cyclic_separating_unit_vector
  obtain ⟨J,_⟩ := exists_hilbert_conjugation (H := H)
  let d := constructedModularConjugationData J ξ hsep hcyc
    (tomitaPolarConjugation_commutant_eq J ξ hsep hcyc)
  apply expectedMatrixSubfactorModel_of_bicentralizer hM.toTypeIIIFactor ξ hunit hsep hcyc d
  · let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
    intro a
    exact (tomitaPolarConjugation_quadratic_nonneg J ξ hsep hcyc a).1
  · exact hhom H M hM
  · exact hbic H M hM R hR

end

end KadisonKastler

end OAI
