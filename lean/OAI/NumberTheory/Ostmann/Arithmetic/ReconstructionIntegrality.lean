import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructedHistoryTests

namespace OAI

/-! # Every original integer-divisibility gate is a cleared polynomial test -/

namespace Ostmann

open scoped Classical

def HistoryFormula.IntegralAt {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) : Prop :=
  ∃ y : ℤ, F.value (fun i => (x i : ℚ)) = y

theorem HistoryFormula.integralAt_iff {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) :
    F.IntegralAt x ↔ F.cleared.denominator ∣
      MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, F.cleared.integer_value_cleared x y hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (div_eq_iff (Int.cast_ne_zero.mpr F.cleared.denominator_ne_zero)).mpr
    have he : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℚ) =
        MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.cleared.numerator := by
      simpa [Int.castRingHom] using
        (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.cleared.numerator)
    rw [← he, hy, Int.cast_mul, mul_comm]

theorem HistoryPivotStep.valid_iff_integral {σ : Type*} (step : HistoryPivotStep σ) (x : σ → ℤ) :
    step.Valid x ↔ step.formula.IntegralAt x := by
  constructor
  · intro hx
    exact ⟨step.numerator x / step.s, step.formula_value_integer x hx⟩
  · rintro ⟨y, hy⟩
    rw [step.formula_value] at hy
    have he : (step.numerator x : ℚ) = (y : ℚ) * step.s :=
      (div_eq_iff (Int.cast_ne_zero.mpr step.s_ne_zero)).mp hy
    have hi : step.numerator x = step.s * y := by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_mul, he, mul_comm]
    exact ⟨y, hi⟩

noncomputable def reconstructionTests {σ : Type*} :
    List (HistoryPivotStep σ) → (σ → HistoryFormula σ) → List (HistoryFormula σ)
  | [], _ => []
  | step :: rest, env =>
      (step.formula.bind env) ::
        reconstructionTests rest (Function.update env step.target (step.formula.bind env))

/-- Inductively, the polynomial gates enforce exactly the original integer
reconstructions. They are not an independently assumed support predicate. -/
theorem reconstructionTests_iff {σ : Type*} (steps : List (HistoryPivotStep σ))
    (env : σ → HistoryFormula σ) (x₀ x : σ → ℤ)
    (henv : ∀ i, (env i).value (fun j => (x₀ j : ℚ)) = x i) :
    (∀ F ∈ reconstructionTests steps env, F.IntegralAt x₀) ↔ ValidIntegerReconstruction steps x := by
  induction steps generalizing env x with
  | nil => simp [reconstructionTests, ValidIntegerReconstruction]
  | cons step rest ih =>
    have hev : (step.formula.bind env).value (fun j => (x₀ j : ℚ)) =
        step.formula.value (fun j => (x j : ℚ)) := by
      rw [HistoryFormula.value_bind]
      congr 1
      funext i
      exact henv i
    have hhead : (step.formula.bind env).IntegralAt x₀ ↔ step.Valid x := by
      rw [step.valid_iff_integral]
      simp only [HistoryFormula.IntegralAt, hev]
    simp only [reconstructionTests, List.mem_cons, forall_eq_or_imp, ValidIntegerReconstruction]
    rw [hhead]
    constructor
    · rintro ⟨hs, hrest⟩
      refine ⟨hs, (ih _ _ ?_).mp hrest⟩
      intro i
      by_cases hi : i = step.target
      · subst i
        simp only [Function.update_self, HistoryPivotStep.applyInteger, hev, step.formula_value_integer x hs]
      · simp only [Function.update_of_ne hi, HistoryPivotStep.applyInteger, henv]
    · rintro ⟨hs, hrest⟩
      refine ⟨hs, (ih _ _ ?_).mpr hrest⟩
      intro i
      by_cases hi : i = step.target
      · subst i
        simp only [Function.update_self, HistoryPivotStep.applyInteger, hev, step.formula_value_integer x hs]
      · simp only [Function.update_of_ne hi, HistoryPivotStep.applyInteger, henv]

end Ostmann

end OAI
