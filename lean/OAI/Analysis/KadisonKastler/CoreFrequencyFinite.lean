import OAI.Analysis.KadisonKastler.CoreFrequencyFaithfulness
import OAI.Analysis.KadisonKastler.FiniteProjectionVectorCriterion

namespace OAI

/-! # The finite-window reduction for the modular core

The frequency window is nonzero, and the weighted packet gives a
faithful vector on its corner. Equality of the vector norms for an
operator and its adjoint makes this corner finite.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)

def unitCoreFrequencyProjection : AlgebraProjection (regularCoreAlgebra U hU M) :=
  ⟨⟨regularFrequencyWindow 0 1, regularFrequencyWindow_mem_core U hU M 0 1⟩, by
    constructor
    · apply Subtype.ext
      exact (regularFrequencyWindow_isStarProjection (H := H) 0 1).isIdempotentElem.eq
    · apply Subtype.ext
      exact (regularFrequencyWindow_isStarProjection (H := H) 0 1).isSelfAdjoint.star_eq⟩

theorem unitCoreFrequencyProjection_ne_zero [Nontrivial H] :
    (unitCoreFrequencyProjection U hU M).val ≠ 0 := by
  intro he
  exact regularFrequencyWindow_unit_ne_zero (congrArg Subtype.val he)

theorem unitCoreFrequencyProjection_finite_of_norm
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (Ω : H) (hΩ : ∀ t, (U t : H →L[ℂ] H) Ω = Ω)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (htrace : ∀ a : Algebra (regularCoreAlgebra U hU M),
      (unitCoreFrequencyProjection U hU M).val * a = a →
      a * (unitCoreFrequencyProjection U hU M).val = a →
      ‖a.val (coreTraceFrequencyVector Ω)‖ = ‖(star a).val (coreTraceFrequencyVector Ω)‖) :
    FiniteProjectionIn (regularCoreAlgebra U hU M) (unitCoreFrequencyProjection U hU M).val := by
  apply finiteProjectionIn_of_faithful_vector_norm (unitCoreFrequencyProjection U hU M)
    (coreTraceFrequencyVector Ω) (coreTraceFrequencyVector_fixed Ω) ?_ htrace
  intro a ha
  apply Subtype.ext
  exact core_kills_window_of_kills_trace_packet U hU M hM Ω hΩ hsep a.val a.property ha

theorem core_projectionSemifinite_of_window_norm [Nontrivial H]
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (hfactor : ScalarCenter (regularCoreAlgebra U hU M))
    (Ω : H) (hΩ : ∀ t, (U t : H →L[ℂ] H) Ω = Ω)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (htrace : ∀ a : Algebra (regularCoreAlgebra U hU M),
      (unitCoreFrequencyProjection U hU M).val * a = a →
      a * (unitCoreFrequencyProjection U hU M).val = a →
      ‖a.val (coreTraceFrequencyVector Ω)‖ = ‖(star a).val (coreTraceFrequencyVector Ω)‖) :
    ∀ p : AlgebraProjection (regularCoreAlgebra U hU M), p.val ≠ 0 →
      ∃ q : AlgebraProjection (regularCoreAlgebra U hU M),
        q ≤ p ∧ q.val ≠ 0 ∧ FiniteProjectionIn (regularCoreAlgebra U hU M) q.val :=
  projectionSemifinite_of_finite_projection hfactor (unitCoreFrequencyProjection U hU M)
    (unitCoreFrequencyProjection_ne_zero U hU M)
    (unitCoreFrequencyProjection_finite_of_norm U hU M hM Ω hΩ hsep htrace)

end

end KadisonKastler

end OAI
