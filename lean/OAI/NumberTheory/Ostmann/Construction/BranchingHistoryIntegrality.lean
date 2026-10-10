import OAI.NumberTheory.Ostmann.Construction.BranchingHistoryReplay
import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructionIntegrality

namespace OAI

/-! # Every branching reconstruction gate is its constructed polynomial divisibility test -/

namespace Ostmann.BranchingWordHistory

open scoped Classical

variable {σ : Type*}

theorem updatedFormula_integral_iff (step : HistoryPivotStep σ) (env : σ → HistoryFormula σ)
    (a x : σ → ℤ) (he : ∀ i, (env i).value (fun j => (a j : ℚ)) = x i) :
    (step.formula.bind env).IntegralAt a ↔ step.Valid x := by
  have hv : (step.formula.bind env).value (fun j => (a j : ℚ)) =
      step.formula.value (fun j => (x j : ℚ)) := by
    rw [HistoryFormula.value_bind]
    congr 1
    funext i
    exact he i
  rw [step.valid_iff_integral]
  simp only [HistoryFormula.IntegralAt, hv]

/-- The full branching support has precisely one constructed integrality
test for each internal node. Child branches are evaluated independently. -/
theorem pivotFormulas_integral_iff (history : BranchingWordHistory σ)
    (env : σ → HistoryFormula σ) (a x : σ → ℤ)
    (he : ∀ i, (env i).value (fun j => (a j : ℚ)) = x i) :
    (∀ F ∈ history.pivotFormulas env, F.IntegralAt a) ↔ history.Valid x := by
  induction history generalizing env x with
  | leaf word => simp [pivotFormulas, Valid]
  | node step left right hl hr =>
    have hh := updatedFormula_integral_iff step env a x he
    simp only [pivotFormulas, List.mem_cons, List.mem_append, or_imp, forall_and, forall_eq, Valid]
    rw [hh]
    constructor
    · rintro ⟨hs, hleft, hright⟩
      have hu := updatedFormulas_value step env (fun j => (a j : ℚ)) x he hs
      exact ⟨hs, (hl _ _ hu).mp hleft, (hr _ _ hu).mp hright⟩
    · rintro ⟨hs, hleft, hright⟩
      have hu := updatedFormulas_value step env (fun j => (a j : ℚ)) x he hs
      exact ⟨hs, (hl _ _ hu).mpr hleft, (hr _ _ hu).mpr hright⟩

/-- In the initial prime environment the gate is an explicit divisibility
of integer polynomial values by the constructed nonzero denominators. -/
theorem branching_integer_polynomial_tests (history : BranchingWordHistory σ) (x : σ → ℤ) :
    history.Valid x ↔ ∀ F ∈ history.pivotFormulas .prime,
      F.cleared.denominator ∣ MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator := by
  rw [← pivotFormulas_integral_iff history .prime x x (by intro i; simp)]
  simp only [HistoryFormula.integralAt_iff]

end Ostmann.BranchingWordHistory

end OAI
