import OAI.Analysis.Pureness.GroupAlgebra.FiniteQuotientMatrixExtension
import OAI.Analysis.Pureness.States.NormalizedStateAWStar

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped Topology NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

def normalizedStateQuotientTwoQuasitrace : TwoQuasitrace (RegularizedStateCauchyQuotient hsimple y hy f 0) :=
  (finiteQuotientTwoQuasitrace (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f)).scale
    ⟨(regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹,
      inv_nonneg.mpr ENNReal.toReal_nonneg⟩

lemma normalizedStateQuotientTwoQuasitrace_eq (x : RegularizedStateCauchyQuotient hsimple y hy f 0) :
    (normalizedStateQuotientTwoQuasitrace hsimple y hy f).base x=
      normalizedStateCauchyValue hsimple y hy f x := by
  unfold normalizedStateQuotientTwoQuasitrace TwoQuasitrace.scale ComplexQuasitrace.scale normalizedStateCauchyValue
  dsimp only
  rw [finiteQuotientTwoQuasitrace_base]
  exact congrArg₂ (·*·) (Complex.ofReal_inv _) rfl

lemma normalizedStateQuotientTwoQuasitrace_unit :
    (normalizedStateQuotientTwoQuasitrace hsimple y hy f).base 1=1 := by
  rw [normalizedStateQuotientTwoQuasitrace_eq,normalizedStateCauchyValue_unit]

lemma normalizedStateQuotientTwoQuasitrace_faithful (x : RegularizedStateCauchyQuotient hsimple y hy f 0) :
    (normalizedStateQuotientTwoQuasitrace hsimple y hy f).base (star x*x)=0 ↔ x=0 := by
  rw [normalizedStateQuotientTwoQuasitrace_eq]
  exact normalizedStateCauchyValue_square_eq_zero_iff hsimple y hy f x

theorem regularizedStateQuotient_twoQuasitrace_awstar :
    ∃ Q : TwoQuasitrace (RegularizedStateCauchyQuotient hsimple y hy f 0),
      (∀ x, Q.base x=normalizedStateCauchyValue hsimple y hy f x) ∧ Q.base 1=1 ∧
      (∀ x, Q.base (star x*x)=0 ↔ x=0) ∧
      (∀ S : Set (RegularizedStateCauchyQuotient hsimple y hy f 0),
        ∃ p : RegularizedStateCauchyQuotient hsimple y hy f 0, IsStarProjection p ∧
          ∀ z, (∀ a ∈ S, a*z=0) ↔ p*z=z) :=
  ⟨normalizedStateQuotientTwoQuasitrace hsimple y hy f,
    normalizedStateQuotientTwoQuasitrace_eq hsimple y hy f,
    normalizedStateQuotientTwoQuasitrace_unit hsimple y hy f,
    normalizedStateQuotientTwoQuasitrace_faithful hsimple y hy f,
    regularizedStateQuotient_right_annihilator hsimple y hy f⟩
end CuntzPureness

end

end OAI
