import Mathlib.Data.List.OfFn
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeWordCellGeometry
import OAI.NumberTheory.Ostmann.Characters.CharacterWordIntervals

namespace OAI

/-! # Integer interval endpoints for actual selected prime-cell words -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeCellLower (h : ℕ) : ℕ := ⌈Real.exp (h : ℝ)⌉₊
noncomputable def primeCellUpper (h : ℕ) : ℕ := ⌊Real.exp ((h : ℝ) + 1)⌋₊

theorem primeCell_interval (p h : ℕ) (hp : p.Prime) (hi : primeLogIndex p = h) :
    primeCellLower h ≤ p ∧ p ≤ primeCellUpper h := by
  have hh := (primeLogIndex_eq_iff p h hp).mp hi
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  constructor
  · apply Nat.ceil_le.mpr
    exact (Real.exp_lt_exp.mpr hh.1).le.trans_eq (Real.exp_log hp0)
  · apply Nat.le_floor
    exact (Real.exp_log hp0).symm.le.trans (Real.exp_le_exp.mpr hh.2)

theorem primeCell_products {n : ℕ} (h : Fin n → ℕ) :
    Real.exp (∑ i, (h i : ℝ)) ≤ (∏ i, primeCellLower (h i) : ℕ) ∧
      (∏ i, primeCellUpper (h i) : ℕ) ≤ Real.exp ((∑ i, (h i : ℝ)) + n) := by
  constructor
  · rw [Nat.cast_prod, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
      (fun i _ => Nat.le_ceil _)
  · rw [Nat.cast_prod]
    calc
      _ ≤ ∏ i : Fin n, Real.exp ((h i : ℝ) + 1) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
          (fun i _ => Nat.floor_le (Real.exp_pos _).le)
      _ = _ := by rw [← Real.exp_sum, Finset.sum_add_distrib]; simp

theorem primeCell_target_products {n : ℕ} (h : Fin n → ℕ) (T E c : ℝ)
    (htarget : |(∑ i, (h i : ℝ)) - T| ≤ E) (hc : E + n ≤ c) :
    Real.exp (T - c) ≤ (∏ i, primeCellLower (h i) : ℕ) ∧
      (∏ i, primeCellUpper (h i) : ℕ) ≤ Real.exp (T + c) := by
  obtain ⟨htlo, hthi⟩ := abs_le.mp htarget
  obtain ⟨hl, hu⟩ := primeCell_products h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · exact (Real.exp_le_exp.mpr (by linarith)).trans hl
  · exact hu.trans (Real.exp_le_exp.mpr (by linarith))

theorem list_primeCell_target_products (w : List ℕ) (T E c : ℝ)
    (htarget : |(w.sum : ℝ) - T| ≤ E) (hc : E + w.length ≤ c) :
    Real.exp (T - c) ≤ (∏ i : Fin w.length, primeCellLower (w.get i) : ℕ) ∧
      (∏ i : Fin w.length, primeCellUpper (w.get i) : ℕ) ≤ Real.exp (T + c) := by
  apply primeCell_target_products (fun i => w.get i) T E c _ hc
  have he : (∑ i : Fin w.length, w.get i) = w.sum := by
    rw [← List.sum_ofFn, List.ofFn_get]
  simpa only [← Nat.cast_sum, he] using htarget

end Ostmann

end OAI
