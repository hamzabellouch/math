import OAI.Analysis.ModularTheory.FiniteWeightDensity
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! The genuine tracial conjugation on the actual modular Hilbert space.
It is extended from star on the dense finite-weight domain. -/
noncomputable section
open MeasureTheory
open scoped Topology

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularFiniteWeightStar (S : StandardModularData H) :
    modularFiniteWeightSpace S →ₛₗ[starRingEnd ℂ] modularFiniteWeightSpace S where
  toFun T := ⟨star T.val, star_mem T.property.1,
    modularCoreSquareWeight_star_finite S T.val T.property.1 T.property.2⟩
  map_add' T R := by
    apply Subtype.ext
    exact star_add T.val R.val
  map_smul' c T := by
    apply Subtype.ext
    exact star_smul c T.val

lemma modularFiniteWeightStar_involutive (S : StandardModularData H) :
    Function.Involutive (modularFiniteWeightStar S) := by
  intro T
  apply Subtype.ext
  exact star_star T.val

def modularFiniteWeightAdjoint (S : StandardModularData H) :
    modularFiniteWeightSpace S →ₛₗ[starRingEnd ℂ] Lp H 2 (volume : Measure ℝ) :=
  (modularFiniteWeightMap S).comp (modularFiniteWeightStar S)

lemma modularFiniteWeightAdjoint_norm (S : StandardModularData H)
    (T : modularFiniteWeightSpace S) :
    ‖modularFiniteWeightAdjoint S T‖ = ‖modularFiniteWeightMap S T‖ :=
  modularWeightVector_star_norm S T.val T.property.1 T.property.2

def modularTraceConjugation (S : StandardModularData H) :
    Lp H 2 (volume : Measure ℝ) →ₛₗᵢ[starRingEnd ℂ] Lp H 2 (volume : Measure ℝ) :=
  LinearMap.extendOfIsometry (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := modularFiniteWeightSpace S) (Eₗ := Lp H 2 (volume : Measure ℝ))
    (F := Lp H 2 (volume : Measure ℝ)) (σ₁₂ := starRingEnd ℂ)
    (modularFiniteWeightAdjoint S) (e := modularFiniteWeightMap S)
    (modularFiniteWeightMap_dense S) (modularFiniteWeightAdjoint_norm S)

lemma modularTraceConjugation_vector (S : StandardModularData H)
    (T : modularFiniteWeightSpace S) :
    modularTraceConjugation S (modularFiniteWeightMap S T) =
      modularFiniteWeightMap S (modularFiniteWeightStar S T) :=
  LinearMap.extendOfIsometry_eq _ _ _ _

lemma modularTraceConjugation_involutive (S : StandardModularData H) :
    Function.Involutive (modularTraceConjugation S) := by
  intro f
  refine (modularFiniteWeightMap_dense S).induction_on
    (p := fun x => modularTraceConjugation S (modularTraceConjugation S x) = x) f ?_ ?_
  · exact isClosed_eq ((modularTraceConjugation S).continuous.comp
      (modularTraceConjugation S).continuous) continuous_id
  · intro T
    rw [modularTraceConjugation_vector, modularTraceConjugation_vector,
      modularFiniteWeightStar_involutive S T]

end WeakPureInfiniteness

end

end OAI
