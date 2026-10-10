import OAI.Analysis.Pureness.States.QuotientGenuineQuasitrace
import OAI.Analysis.Pureness.States.RegularizedStateCStarValue

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped Topology NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

def normalizedStateQuotientQuasitrace :
    ComplexQuasitrace (RegularizedStateCauchyQuotient hsimple y hy f 0) :=
  ((finiteSpectralPositiveQuasitrace
    (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f) 1).quotientComplexQuasitrace
        (finiteSpectralPositiveQuasitrace_metricSize_add _ _ _ _ 1)
        (finiteSpectralPositiveQuasitrace_sqrt_add _ _ _ _ 1)).scale
    ⟨(regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹,
      inv_nonneg.mpr ENNReal.toReal_nonneg⟩

lemma normalizedStateQuotientQuasitrace_eq (x : RegularizedStateCauchyQuotient hsimple y hy f 0) :
    normalizedStateQuotientQuasitrace hsimple y hy f x =
      normalizedStateCauchyValue hsimple y hy f x := by
  unfold normalizedStateQuotientQuasitrace ComplexQuasitrace.scale normalizedStateCauchyValue
  dsimp only
  rw [PositiveQuasitrace.quotientComplexQuasitrace_eq]
  exact congrArg₂ (·*·) (Complex.ofReal_inv _) rfl

lemma normalizedStateQuotientQuasitrace_unit :
    normalizedStateQuotientQuasitrace hsimple y hy f 1 = 1 := by
  rw [normalizedStateQuotientQuasitrace_eq, normalizedStateCauchyValue_unit]

lemma normalizedStateQuotientQuasitrace_faithful (x : RegularizedStateCauchyQuotient hsimple y hy f 0) :
    normalizedStateQuotientQuasitrace hsimple y hy f (star x*x) = 0 ↔ x = 0 := by
  rw [normalizedStateQuotientQuasitrace_eq]
  exact normalizedStateCauchyValue_square_eq_zero_iff hsimple y hy f x

lemma normalizedStateQuotientQuasitrace_original (x : A) :
    normalizedStateQuotientQuasitrace hsimple y hy f
      (regularizedStateCauchyEmbedding hsimple y hy f 0 (scalarMatrixHom (ι := Fin 1) x)) =
      (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base x := by
  rw [normalizedStateQuotientQuasitrace_eq, normalizedStateCauchyValue_original]
end CuntzPureness

end

end OAI
