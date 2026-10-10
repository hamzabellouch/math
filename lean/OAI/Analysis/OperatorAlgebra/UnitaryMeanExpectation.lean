import OAI.Analysis.OperatorAlgebra.UnitaryMeanRange
import OAI.Analysis.Nuclearity.NuclearCommutantExpectation

namespace OAI

/-! Real-action averaging of a cpc projection onto an invariant von Neumann
algebra gives a cpc projection onto its fixed-point algebra. This follows
Anantharaman-Delaroche, Pacific J. Math. 171 (1995), Proposition 3.6, p. 329. -/

noncomputable section
open Filter
open scoped InnerProductSpace ComplexOrder CStarAlgebra

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem realAction_fixedPoint_expectation
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (U : ℝ → H ≃ₗᵢ[ℂ] H) (hU : ∀ x, Continuous (fun t => U t x))
    (hadd : ∀ t s x, U (t + s) x = U t (U s x))
    (M : VonNeumannAlgebra H)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEn : ‖E‖ ≤ 1)
    (hEr : ∀ T, E T ∈ M) (hEf : ∀ T, T ∈ M → E T = T)
    (hconj : ∀ t T, T ∈ M → orbitConjugate (U t) T ∈ M) :
    ∃ Q : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H),
      CompletelyPositive Q ∧ ‖Q‖ ≤ 1 ∧
      (∀ T, Q T ∈ M) ∧
      (∀ T s x, Q T (U s x) = U s (Q T x)) ∧
      (∀ T, T ∈ M → (∀ s x, T (U s x) = U s (T x)) → Q T = T) := by
  let Q := (unitaryOrbitMeanCLM ω U hU).comp E
  refine ⟨Q, completelyPositive_comp _ _ hE (unitaryOrbitMeanCLM_cp ω hω U hU),
    ?_, ?_, ?_, ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (unitaryOrbitMeanCLM_norm_le ω hω U hU) hEn
        (norm_nonneg E) zero_le_one).trans_eq (one_mul 1))
  · intro T
    exact unitaryOrbitMean_mem ω U hU M (E T) (fun t => hconj t _ (hEr T))
  · intro T s x
    exact (unitaryOrbitMean_commutes ω hω U hU hadd (E T) s x).symm
  · intro T hT hc
    change unitaryOrbitMean ω U hU (E T) = T
    rw [hEf T hT]
    exact unitaryOrbitMean_fix ω hω U hU T hc

end WeakPureInfiniteness

end

end OAI
