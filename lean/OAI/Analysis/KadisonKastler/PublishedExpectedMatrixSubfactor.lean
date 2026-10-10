import OAI.Analysis.KadisonKastler.FixedProductAbsorption
import OAI.Analysis.KadisonKastler.ExpectedCentralizer
import OAI.Analysis.KadisonKastler.IncreasingMatrixPreparation
import OAI.Analysis.KadisonKastler.PublishedModularCoreType

namespace OAI

/-! # The expected hyperfinite subfactor consequence used for preparation

Marrakchi, *Full factors, bicentralizer flow and approximately inner
automorphisms*, arXiv:1811.10253v2, Theorem D(ii), gives trivial bicentralizer
for a type III₁ factor absorbing R_lambda. Haagerup, *Connes' bicentralizer
problem and uniqueness of the injective factor of type III₁*, Acta Math.
158 (1987), Lemma 3.8 and the proof of Theorem 3.1, (2) => (3), pp.142--145,
then gives an irreducible hyperfinite II₁ subfactor with faithful normal
expectation. Its increasing full-matrix model is retained here.

The composed trace-state has a cyclic separating vector in the given
separable type III representation: Haagerup, *The standard form of von
Neumann algebras*, Math. Scand. 37 (1975), Lemma 2.10(1), p.278, and
Blackadar III.1.7.9 give the representation transfer. This input concerns
a single algebra and contains no proximity or perturbation conclusion.
-/

namespace KadisonKastler

open Generator
open UnitalTomsWinter

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Only the expected matrix subfactor data needed by preparation. The
right action, neighboring inclusion and all estimates are constructed
by the application. -/
structure ExpectedMatrixSubfactorModel (M : VonNeumannAlgebra H) where
  stage : ℕ → FiniteMatrixStage M
  increasing : Monotone (fun n => (stage n).units.concreteAlgebra)
  trace : FaithfulTracialState (Algebra (FiniteMatrixStage.generatedVonNeumann stage))
  expectation : Algebra M →L[ℂ] Algebra (FiniteMatrixStage.generatedVonNeumann stage)
  unital : expectation 1 = 1
  left_module : ∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann stage)) (x : Algebra M),
    expectation (StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le stage) r * x) =
      r * expectation x
  right_module : ∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann stage)) (x : Algebra M),
    expectation (x * StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le stage) r) =
      expectation x * r
  vector : H
  vector_state : ∀ x : Algebra M,
    expectedTrace trace expectation x = inner ℂ vector (x.val vector)
  cyclic : DenseRange (algebraVectorMap M vector)
  separating : Function.Injective (algebraVectorMap M vector)
  irreducible : ∀ T ∈ M,
    (∀ r ∈ FiniteMatrixStage.generatedVonNeumann stage, r * T = T * r) →
    ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)

def PublishedExpectedMatrixSubfactor : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H), TypeIII1Factor M →
    ∀ R : PointedMatrixProduct.{u} (fun _ : ℕ => fixedProductLambda),
      Nonempty (Algebra (spatialProductAlgebra M R.algebra) ≃⋆ₐ[ℂ] Algebra M) →
      Nonempty (ExpectedMatrixSubfactorModel M)

theorem ExpectedMatrixSubfactorModel.unit_vector {M : VonNeumannAlgebra H}
    (E : ExpectedMatrixSubfactorModel M) : ‖E.vector‖ = 1 :=
  norm_vector_of_expectedTrace M _ E.trace E.expectation E.unital E.vector E.vector_state

end

end KadisonKastler

end OAI
