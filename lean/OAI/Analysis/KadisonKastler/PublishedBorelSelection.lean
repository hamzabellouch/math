import OAI.Analysis.KadisonKastler.PolishConjugacyRelation
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

namespace OAI

/-! # The published Borel selection input

Alexander S. Kechris, *Classical Descriptive Set Theory*, GTM 156,
Springer (1995), Theorem 18.1, pp.120–121, and Theorem 21.10, pp.155–156.
DOI: 10.1007/978-1-4612-4190-4.

We retain only selection for Borel relations whose second coordinate is
the proved Polish unitary coordinate space, for one finite Borel measure.
The published universally measurable selector is measurable for the
completed measure, hence has the `AEMeasurable` formulation used here.
No algebra-conjugacy or perturbation conclusion is part of this input.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

universe u v

def PublishedUnitaryBorelSelection : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] [StandardBorelSpace X]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (ξ : ℕ → H), DenseRange ξ →
    ∀ (μ : Measure X) [IsFiniteMeasure μ] (R : Set (X × StrongUnitarySpace ξ)),
      MeasurableSet R → (∀ᵐ x ∂μ, ∃ p, (x, p) ∈ R) →
      ∃ f : X → StrongUnitarySpace ξ,
        AEMeasurable f μ ∧ ∀ᵐ x ∂μ, (x, f x) ∈ R

end KadisonKastler

end OAI
