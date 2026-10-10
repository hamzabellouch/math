import Mathlib.Data.Int.Cast.Field
import OAI.NumberTheory.Ostmann.Construction.HistoryReplacementList

namespace OAI

/-! # The cleared formulas evaluate to the actual integer pivot reconstructions -/

namespace Ostmann

open scoped Classical

structure HistoryPivotStep (σ : Type*) where
  target : σ
  left : List σ
  right : List σ
  v : ℤ
  w : ℤ
  s : ℤ
  s_ne_zero : s ≠ 0

namespace HistoryPivotStep

variable {σ : Type*}

noncomputable def formula (step : HistoryPivotStep σ) : HistoryFormula σ :=
  .solve (.listProduct (step.left.map .prime)) (.listProduct (step.right.map .prime))
    step.v step.w step.s step.s_ne_zero

def numerator (step : HistoryPivotStep σ) (x : σ → ℤ) : ℤ :=
  step.v * (step.right.map x).prod - step.w * (step.left.map x).prod

def Valid (step : HistoryPivotStep σ) (x : σ → ℤ) : Prop := step.s ∣ step.numerator x

noncomputable def applyInteger (step : HistoryPivotStep σ) (x : σ → ℤ) : σ → ℤ :=
  Function.update x step.target (step.numerator x / step.s)

theorem formula_value (step : HistoryPivotStep σ) (x : σ → ℤ) :
    step.formula.value (fun i => (x i : ℚ)) = (step.numerator x : ℚ) / step.s := by
  have hp (l : List σ) : (l.map (fun i => (x i : ℚ))).prod = ((l.map x).prod : ℚ) := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  simp only [formula, HistoryFormula.value_solve, HistoryFormula.value_listProduct,
    List.map_map, Function.comp_def, HistoryFormula.value_prime, hp, numerator,
    Int.cast_sub, Int.cast_mul]

theorem formula_value_integer (step : HistoryPivotStep σ) (x : σ → ℤ) (hx : step.Valid x) :
    step.formula.value (fun i => (x i : ℚ)) = (step.numerator x / step.s : ℤ) := by
  rw [formula_value, Int.cast_div hx (Int.cast_ne_zero.mpr step.s_ne_zero)]

theorem applyInteger_cast (step : HistoryPivotStep σ) (x : σ → ℤ) (hx : step.Valid x) :
    (fun i => (step.applyInteger x i : ℚ)) =
      Function.update (fun i => (x i : ℚ)) step.target (step.formula.value (fun i => (x i : ℚ))) := by
  classical
  funext i
  by_cases hi : i = step.target
  · subst i
    simp only [applyInteger, Function.update_self, formula_value_integer step x hx]
  · simp only [applyInteger, Function.update_of_ne hi]

theorem formula_cost (step : HistoryPivotStep σ) :
    step.formula.cost = step.left.length + step.right.length + 4 := by
  have hc (l : List σ) : (l.map (fun _ => (1 : ℕ))).sum = l.length := by
    induction l with
    | nil => rfl
    | cons i l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
  simp only [formula, HistoryFormula.cost, HistoryFormula.cost_listProduct, List.map_map,
    Function.comp_def, hc]
  omega

end HistoryPivotStep

noncomputable def reconstructIntegers {σ : Type*} : List (HistoryPivotStep σ) → (σ → ℤ) → σ → ℤ
  | [], x => x
  | step :: rest, x => reconstructIntegers rest (step.applyInteger x)

def ValidIntegerReconstruction {σ : Type*} : List (HistoryPivotStep σ) → (σ → ℤ) → Prop
  | [], _ => True
  | step :: rest, x => step.Valid x ∧ ValidIntegerReconstruction rest (step.applyInteger x)

noncomputable def integerReconstructionFormulas {σ : Type*} (steps : List (HistoryPivotStep σ)) :
    σ → HistoryFormula σ :=
  HistoryFormula.reconstructedFormulas (steps.map fun step => (step.target, step.formula))

theorem replay_integer_history {σ : Type*} (steps : List (HistoryPivotStep σ))
    (x : σ → ℤ) (hx : ValidIntegerReconstruction steps x) (i : σ) :
    HistoryFormula.replayValues (steps.map fun step => (step.target, step.formula))
      (fun j => (x j : ℚ)) i = (reconstructIntegers steps x i : ℚ) := by
  induction steps generalizing x with
  | nil => rfl
  | cons step rest ih =>
    rw [List.map_cons, HistoryFormula.replayValues, ← step.applyInteger_cast x hx.1]
    exact ih (step.applyInteger x) hx.2

theorem integerReconstructionFormulas_value {σ : Type*} (steps : List (HistoryPivotStep σ))
    (x : σ → ℤ) (hx : ValidIntegerReconstruction steps x) (i : σ) :
    (integerReconstructionFormulas steps i).value (fun j => (x j : ℚ)) =
      (reconstructIntegers steps x i : ℚ) := by
  rw [integerReconstructionFormulas, HistoryFormula.reconstructedFormulas_value]
  exact replay_integer_history steps x hx i

end Ostmann

end OAI
