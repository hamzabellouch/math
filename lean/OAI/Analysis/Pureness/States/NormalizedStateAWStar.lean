import OAI.Analysis.Pureness.States.QuotientAWStar
import OAI.Analysis.Pureness.States.NormalizedStateQuotientQuasitrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped Topology NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

theorem regularizedStateQuotient_right_annihilator
    (S : Set (RegularizedStateCauchyQuotient hsimple y hy f 0)) :
    ∃ p : RegularizedStateCauchyQuotient hsimple y hy f 0, IsStarProjection p ∧
      ∀ z, (∀ a ∈ S, a*z=0) ↔ p*z=z :=
  PositiveQuasitrace.quotient_right_annihilator_projection _ _
    (finiteSpectralPositiveQuasitrace_sqrt_add _ _ _ _ 1) S

theorem regularizedStateQuotient_faithful_normalized_awstar :
    ∃ Q : ComplexQuasitrace (RegularizedStateCauchyQuotient hsimple y hy f 0),
      (∀ x, Q x=normalizedStateCauchyValue hsimple y hy f x) ∧ Q 1=1 ∧
      (∀ x, Q (star x*x)=0 ↔ x=0) ∧
      (∀ S : Set (RegularizedStateCauchyQuotient hsimple y hy f 0),
        ∃ p : RegularizedStateCauchyQuotient hsimple y hy f 0, IsStarProjection p ∧
          ∀ z, (∀ a ∈ S, a*z=0) ↔ p*z=z) :=
  ⟨normalizedStateQuotientQuasitrace hsimple y hy f,
    normalizedStateQuotientQuasitrace_eq hsimple y hy f,
    normalizedStateQuotientQuasitrace_unit hsimple y hy f,
    normalizedStateQuotientQuasitrace_faithful hsimple y hy f,
    regularizedStateQuotient_right_annihilator hsimple y hy f⟩
end CuntzPureness

end

end OAI
