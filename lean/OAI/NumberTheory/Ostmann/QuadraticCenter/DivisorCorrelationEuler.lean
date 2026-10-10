import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import OAI.NumberTheory.Ostmann.Supply.SquarefreeEulerBound

namespace OAI

/-! # The exact Euler factor after summing the two divisor weights -/

namespace Ostmann

open scoped BigOperators

private theorem sum_powerset_prod_ite (P : Finset ℕ) (A B : ℕ → ℝ) :
    (∑ U ∈ P.powerset, ∏ p ∈ P, if p ∈ U then A p else B p) =
      ∏ p ∈ P, (A p + B p) := by
  classical
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro U hU
  have hUP := Finset.mem_powerset.mp hU
  rw [Finset.prod_ite]
  congr 1
  · congr 1
    exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hUP)
  · congr 1
    ext p
    simp

private theorem divisor_pair_local_factor (lam : ℝ) (r : ℕ → ℝ)
    (P U V : Finset ℕ) (hU : U ⊆ P) (hV : V ⊆ P) :
    lam ^ (U.card + V.card) * (∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else r p) =
      ∏ p ∈ P, if p ∈ U then (if p ∈ V then lam ^ 2 else lam * r p)
        else (if p ∈ V then lam * r p else 1) := by
  classical
  have hlam (U : Finset ℕ) (hU : U ⊆ P) :
      (∏ p ∈ P, if p ∈ U then lam else 1) = lam ^ U.card := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hU, Finset.prod_const]
  rw [pow_add, ← hlam U hU, ← hlam V hV, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases hu : p ∈ U <;> by_cases hv : p ∈ V <;> simp [hu, hv, pow_two]

theorem divisor_correlation_euler_product (P : Finset ℕ) (lam : ℝ) (r : ℕ → ℝ) :
    (∑ U ∈ P.powerset, ∑ V ∈ P.powerset,
      lam ^ (U.card + V.card) * (∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else r p)) =
        ∏ p ∈ P, (1 + lam ^ 2 + 2 * lam * r p) := by
  classical
  calc
    _ = ∑ U ∈ P.powerset, ∑ V ∈ P.powerset,
        ∏ p ∈ P, if p ∈ U then (if p ∈ V then lam ^ 2 else lam * r p)
          else (if p ∈ V then lam * r p else 1) := by
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      exact divisor_pair_local_factor lam r P U V (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV)
    _ = ∑ U ∈ P.powerset, ∏ p ∈ P,
        ((if p ∈ U then lam ^ 2 else lam * r p) + (if p ∈ U then lam * r p else 1)) := by
      apply Finset.sum_congr rfl
      intro U hU
      convert sum_powerset_prod_ite P (fun p => if p ∈ U then lam ^ 2 else lam * r p)
        (fun p => if p ∈ U then lam * r p else 1) using 1
      apply Finset.sum_congr rfl
      intro V hV
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hu : p ∈ U <;> by_cases hv : p ∈ V <;> simp [hu, hv]
    _ = ∑ U ∈ P.powerset, ∏ p ∈ P,
        if p ∈ U then lam ^ 2 + lam * r p else lam * r p + 1 := by
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.prod_congr rfl
      intro p hp
      split <;> simp_all
    _ = ∏ p ∈ P, ((lam ^ 2 + lam * r p) + (lam * r p + 1)) := sum_powerset_prod_ite P _ _
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      ring

end Ostmann

end OAI
