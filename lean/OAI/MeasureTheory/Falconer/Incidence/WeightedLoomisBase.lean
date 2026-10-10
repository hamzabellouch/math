import OAI.MeasureTheory.Falconer.Incidence.WeightedLoomisStep

namespace OAI

/-! # Base and induction for the finite weighted projection inequality -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

private def twoCoordinateEquiv : (Fin 2 → X) ≃ (Fin 1 → X) × (Fin 1 → X) where
  toFun z := (eraseFinCoordinate 0 z,eraseFinCoordinate 1 z)
  invFun w := Fin.cons (w.2 0) (fun _ => w.1 0)
  left_inv z := by
    funext i
    fin_cases i <;> rfl
  right_inv w := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

theorem finite_weighted_loomis_one : FiniteWeightedLoomis 1 X := by
  classical
  intro f _hf
  simp only [Nat.cast_one,div_one,Real.rpow_one]
  change (∑ z : Fin 2 → X, ∏ i : Fin 2, f i (eraseFinCoordinate i z)) ≤
    ∏ i : Fin 2, ∑ y : Fin 1 → X, f i y
  simp only [Fin.prod_univ_two]
  have he : (∑ z : Fin 2 → X, f 0 (eraseFinCoordinate 0 z)*f 1 (eraseFinCoordinate 1 z)) =
      ∑ w : (Fin 1 → X) × (Fin 1 → X), f 0 w.1*f 1 w.2 := by
    rw [← (twoCoordinateEquiv (X := X)).symm.sum_comp]
    apply Finset.sum_congr rfl
    intro w _
    have hh := (twoCoordinateEquiv (X := X)).apply_symm_apply w
    exact congrArg (fun z : (Fin 1 → X) × (Fin 1 → X) => f 0 z.1*f 1 z.2) hh
  rw [he,Fintype.sum_prod_type]
  exact le_of_eq (by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro y _; rw [Finset.mul_sum])

theorem finite_weighted_loomis_whitney (n : ℕ) (hn : 1 ≤ n) : FiniteWeightedLoomis n X := by
  induction n,hn using Nat.le_induction with
  | base => exact finite_weighted_loomis_one
  | succ n hn ih => exact finite_weighted_loomis_step (by omega) ih

end Falconer

end OAI
