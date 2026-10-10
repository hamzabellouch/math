import OAI.NumberTheory.Ostmann.Arithmetic.CommonHistoryPeriod
import OAI.NumberTheory.Ostmann.Construction.HistoryResidueGate

namespace OAI

/-! # Indexed original pivots and their exact cleared residue tests -/

namespace Ostmann

open scoped Classical

noncomputable def reconstructionFormulaAt {σ : Type*} :
    (steps : List (HistoryPivotStep σ)) → (σ → HistoryFormula σ) →
      Fin steps.length → HistoryFormula σ
  | [], _, i => Fin.elim0 i
  | step :: rest, env, i => Fin.cases (step.formula.bind env)
      (reconstructionFormulaAt rest (Function.update env step.target (step.formula.bind env))) i

noncomputable def reconstructedPivotAt {σ : Type*} :
    (steps : List (HistoryPivotStep σ)) → (σ → ℤ) → Fin steps.length → ℤ
  | [], _, i => Fin.elim0 i
  | step :: rest, x, i => Fin.cases (step.numerator x / step.s)
      (reconstructedPivotAt rest (step.applyInteger x)) i

theorem reconstructionFormulaAt_mem {σ : Type*} (steps : List (HistoryPivotStep σ))
    (env : σ → HistoryFormula σ) (i : Fin steps.length) :
    reconstructionFormulaAt steps env i ∈ reconstructionTests steps env := by
  induction steps generalizing env with
  | nil => exact Fin.elim0 i
  | cons step rest ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [reconstructionFormulaAt, reconstructionTests]
    · simpa only [reconstructionFormulaAt, Fin.cases_succ, reconstructionTests,
        List.mem_cons] using Or.inr (ih _ j)

theorem mem_reconstructionTests_iff {σ : Type*} (steps : List (HistoryPivotStep σ))
    (env : σ → HistoryFormula σ) (F : HistoryFormula σ) :
    F ∈ reconstructionTests steps env ↔ ∃ i, reconstructionFormulaAt steps env i = F := by
  constructor
  · induction steps generalizing env with
    | nil => simp [reconstructionTests]
    | cons step rest ih =>
      intro hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact ⟨0, rfl⟩
      · obtain ⟨i, hi⟩ := ih _ hF
        exact ⟨i.succ, hi⟩
  · rintro ⟨i, rfl⟩
    exact reconstructionFormulaAt_mem steps env i

theorem reconstructionFormulaAt_value {σ : Type*} (steps : List (HistoryPivotStep σ))
    (env : σ → HistoryFormula σ) (x₀ x : σ → ℤ)
    (henv : ∀ i, (env i).value (fun j => (x₀ j : ℚ)) = x i)
    (hx : ValidIntegerReconstruction steps x) (i : Fin steps.length) :
    (reconstructionFormulaAt steps env i).value (fun j => (x₀ j : ℚ)) =
      (reconstructedPivotAt steps x i : ℚ) := by
  induction steps generalizing env x with
  | nil => exact Fin.elim0 i
  | cons step rest ih =>
    have hev : (step.formula.bind env).value (fun j => (x₀ j : ℚ)) =
        (step.numerator x / step.s : ℤ) := by
      rw [HistoryFormula.value_bind]
      have he : (fun j => (env j).value (fun k => (x₀ k : ℚ))) =
          (fun j => (x j : ℚ)) := funext henv
      rw [he, step.formula_value_integer x hx.1]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hev
    · apply ih _ (step.applyInteger x) _ hx.2 j
      intro j
      by_cases hj : j = step.target
      · subst j
        simp only [Function.update_self, HistoryPivotStep.applyInteger, hev]
      · simp only [Function.update_of_ne hj, HistoryPivotStep.applyInteger, henv]

theorem smallDivisionTest_of_integer_value {σ : Type*} (F : HistoryFormula σ)
    (x : σ → ℤ) (y : ℤ) (hy : F.value (fun i => (x i : ℚ)) = y) (s : ℕ) :
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator)
      F.cleared.denominator s ↔ IsUnit (y : ZMod s) := by
  rw [F.cleared.integer_value_cleared x y hy]
  simp only [smallDivisionTest, dvd_mul_right, true_and,
    Int.mul_ediv_cancel_left y F.cleared.denominator_ne_zero]

/-- The entire original sequence of integrality and selected frequency-unit
conditions equals the finite family of cleared polynomial residue tests. -/
theorem reconstruction_small_tests_iff {σ : Type*} (steps : List (HistoryPivotStep σ))
    (x : σ → ℤ) (s : Fin steps.length → ℕ) :
    (∀ i, smallDivisionTest
      (MvPolynomial.eval₂Hom (RingHom.id ℤ) x
        (reconstructionFormulaAt steps HistoryFormula.prime i).cleared.numerator)
      (reconstructionFormulaAt steps HistoryFormula.prime i).cleared.denominator (s i)) ↔
    ValidIntegerReconstruction steps x ∧
      ∀ i, IsUnit ((reconstructedPivotAt steps x i : ℤ) : ZMod (s i)) := by
  have henv (i : σ) : (HistoryFormula.prime i).value (fun j => (x j : ℚ)) = x i :=
    HistoryFormula.value_prime i _
  constructor
  · intro h
    have hx : ValidIntegerReconstruction steps x := by
      apply (reconstructionTests_iff steps .prime x x henv).mp
      intro F hF
      obtain ⟨i, rfl⟩ := (mem_reconstructionTests_iff steps .prime F).mp hF
      exact (HistoryFormula.integralAt_iff _ x).mpr (h i).1
    refine ⟨hx, fun i => ?_⟩
    exact (smallDivisionTest_of_integer_value _ x _
      (reconstructionFormulaAt_value steps .prime x x henv hx i) (s i)).mp (h i)
  · rintro ⟨hx, hu⟩ i
    exact (smallDivisionTest_of_integer_value _ x _
      (reconstructionFormulaAt_value steps .prime x x henv hx i) (s i)).mpr (hu i)

end Ostmann

end OAI
