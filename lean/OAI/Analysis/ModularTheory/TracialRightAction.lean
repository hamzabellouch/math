import OAI.Analysis.ModularTheory.TraceConjugation
import OAI.Analysis.OperatorAlgebra.AntiunitaryCPConjugation

namespace OAI

/-! The actual tracial right action on the modular Hilbert space. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularCoreSquareWeight_right_mul_finite (S : StandardModularData H)
    (T a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct volume S)
    (hf : modularCoreSquareWeight S T < ⊤)
    (ha : a ∈ modularCrossedProduct volume S) :
    modularCoreSquareWeight S (T * a) < ⊤ := by
  have h := modularCoreSquareWeight_mul_finite S (star T)
    (modularCoreSquareWeight_star_finite S T hT hf) (star a)
  rw [← star_mul, modularCoreSquareWeight_adjoint S (T * a) (mul_mem hT ha)] at h
  exact h

def modularFiniteWeightRight (S : StandardModularData H)
    (T : modularFiniteWeightSpace S)
    (a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (ha : a ∈ modularCrossedProduct volume S) : modularFiniteWeightSpace S :=
  ⟨T.val * a, mul_mem T.property.1 ha,
    modularCoreSquareWeight_right_mul_finite S T.val a T.property.1 T.property.2 ha⟩

def modularFiniteWeightLeft (S : StandardModularData H)
    (a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (ha : a ∈ modularCrossedProduct volume S) (T : modularFiniteWeightSpace S) :
    modularFiniteWeightSpace S :=
  ⟨a * T.val, mul_mem ha T.property.1,
    modularCoreSquareWeight_mul_finite S T.val T.property.2 a⟩

lemma modularFiniteWeightMap_left (S : StandardModularData H)
    (a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (ha : a ∈ modularCrossedProduct volume S) (T : modularFiniteWeightSpace S) :
    modularFiniteWeightMap S (modularFiniteWeightLeft S a ha T) =
      a (modularFiniteWeightMap S T) :=
  modularWeightVector_mul S T.val T.property.1 T.property.2 a ha

def modularTraceAntiunitary (S : StandardModularData H) :
    Lp H 2 (volume : Measure ℝ) ≃ₗᵢ⋆[ℂ] Lp H 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective (modularTraceConjugation S)
    (modularTraceConjugation_involutive S).surjective

lemma modularTraceAntiunitary_involutive (S : StandardModularData H) :
    Function.Involutive (modularTraceAntiunitary S) :=
  modularTraceConjugation_involutive S

def modularTracialRightAction (S : StandardModularData H)
    (a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  antiunitaryConjugate (modularTraceAntiunitary S) (star a)

lemma modularTracialRightAction_norm_le (S : StandardModularData H)
    (a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    ‖modularTracialRightAction S a‖ ≤ ‖a‖ := by
  change ‖antiunitaryConjugate (modularTraceAntiunitary S) (star a)‖ ≤ ‖a‖
  simpa only [norm_star] using antiunitaryConjugate_norm_le (modularTraceAntiunitary S) (star a)

lemma modularTracialRightAction_vector (S : StandardModularData H)
    (T : modularFiniteWeightSpace S)
    (a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (ha : a ∈ modularCrossedProduct volume S) :
    modularTracialRightAction S a (modularFiniteWeightMap S T) =
      modularFiniteWeightMap S (modularFiniteWeightRight S T a ha) := by
  change modularTraceConjugation S
    (star a (modularTraceConjugation S (modularFiniteWeightMap S T))) = _
  rw [modularTraceConjugation_vector]
  have hp : modularFiniteWeightStar S (modularFiniteWeightRight S T a ha) =
      modularFiniteWeightLeft S (star a) (star_mem ha) (modularFiniteWeightStar S T) := by
    apply Subtype.ext
    exact star_mul T.val a
  have hm : star a (modularFiniteWeightMap S (modularFiniteWeightStar S T)) =
      modularFiniteWeightMap S (modularFiniteWeightStar S
        (modularFiniteWeightRight S T a ha)) := by
    rw [hp, modularFiniteWeightMap_left]
  rw [hm, modularTraceConjugation_vector, modularFiniteWeightStar_involutive]

lemma modularTracialRightAction_commutes (S : StandardModularData H)
    (a b : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (ha : a ∈ modularCrossedProduct volume S)
    (hb : b ∈ modularCrossedProduct volume S) :
    a * modularTracialRightAction S b = modularTracialRightAction S b * a := by
  apply ContinuousLinearMap.ext
  intro x
  change a (modularTracialRightAction S b x) = modularTracialRightAction S b (a x)
  refine (modularFiniteWeightMap_dense S).induction_on x
    (isClosed_eq (a.continuous.comp (modularTracialRightAction S b).continuous)
      ((modularTracialRightAction S b).continuous.comp a.continuous)) ?_
  intro T
  rw [modularTracialRightAction_vector S T b hb,
    ← modularFiniteWeightMap_left S a ha,
    ← modularFiniteWeightMap_left S a ha,
    modularTracialRightAction_vector S _ b hb]
  congr 1

lemma modularTracialRightProjection_strong (S : StandardModularData H)
    (x : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => modularTracialRightAction S (modularFiniteProjection n) x)
      atTop (𝓝 x) := by
  have hstar (n : ℕ) : star (modularFiniteProjection (H := H) n) =
      modularFiniteProjection (H := H) n :=
    (modularFiniteProjection_isStarProjection (H := H) n).isSelfAdjoint.star_eq
  change Tendsto (fun n => modularTraceConjugation S
    (star (modularFiniteProjection n) (modularTraceConjugation S x))) atTop (𝓝 x)
  simp only [hstar]
  simpa only [Function.comp_def, modularTraceConjugation_involutive S x] using
    (modularTraceConjugation S).continuous.continuousAt.tendsto.comp
      (modularFiniteProjection_strong (modularTraceConjugation S x))

end WeakPureInfiniteness

end

end OAI
