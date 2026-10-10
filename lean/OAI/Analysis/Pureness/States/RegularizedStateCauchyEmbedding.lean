import OAI.Analysis.Pureness.States.FiniteQuasitraceCauchyValue
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientRealImag

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped Topology NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

abbrev RegularizedStateCauchyQuotient (n : ℕ) :=
  FiniteQuasitraceCauchyQuotient (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f) n

def regularizedStateCauchyEmbedding (n : ℕ) : FinMatrix A (n+1) →⋆ₐ[ℂ]
    RegularizedStateCauchyQuotient hsimple y hy f n := finiteQuasitraceCauchyEmbedding _ _ _ _ n

lemma regularizedStateCauchyEmbedding_injective (n : ℕ) :
    Function.Injective (regularizedStateCauchyEmbedding hsimple y hy f n) :=
  PositiveQuasitrace.quotientEmbedding_injective _ _
    (regularizedState_positiveQuasitrace_faithful hsimple y hy f (n+1))

def normalizedStateCauchyValue : RegularizedStateCauchyQuotient hsimple y hy f 0 → ℂ :=
  fun x => ((regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹ : ℂ)*
    finiteQuasitraceCauchyValue _ _ _ _ 0 x

lemma normalizedStateCauchyValue_original (x : A) :
    normalizedStateCauchyValue hsimple y hy f
      (regularizedStateCauchyEmbedding hsimple y hy f 0 (scalarMatrixHom (ι := Fin 1) x)) =
      (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base x := by
  unfold normalizedStateCauchyValue regularizedStateCauchyEmbedding
  rw [finiteQuasitraceCauchyValue_embedding]
  dsimp [normalizedRegularizedStateTwoQuasitrace,TwoQuasitrace.scale,
    ComplexQuasitrace.scale,regularizedStateTwoQuasitrace,finiteSpectralTwoQuasitrace,
    PositiveQuasitrace.toComplex]
  rw [PositiveQuasitrace.comap_complexValue]
  exact congrArg₂ (·*·) (Complex.ofReal_inv _).symm rfl

lemma normalizedStateCauchyValue_unit :
    normalizedStateCauchyValue hsimple y hy f 1 = 1 := by
  have h := normalizedStateCauchyValue_original hsimple y hy f (1 : A)
  simpa only [map_one,normalizedRegularizedStateTwoQuasitrace_unit] using h
end CuntzPureness

end

end OAI
