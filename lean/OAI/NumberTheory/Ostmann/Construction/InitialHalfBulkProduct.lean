import OAI.NumberTheory.Ostmann.Construction.InitialMovingBulkTree

namespace OAI

/-! # Lower product bounds for the two genuine half-bulk cutoffs -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfBulkWeight_product_lower {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (bulk : Fin (b + b) → P)
    (h : initialHalfBulkWeight value b d cb cd sl sr bulk ≠ 0) :
    Real.exp (2 * cb - 2) ≤ ((∏ i, value (bulk i) : ℕ) : ℝ) := by
  let y : MovingRegularSlot 0 (0 + 0) (b + b) → P :=
    fun j => Sum.elim Fin.elim0 bulk j.2
  have he : (initialHalfBulkWeight value b d cb cd sl sr bulk : ℂ) =
      initialMovingCutoffWeight value b d 0 cb cd sl sr y := by
    exact Complex.ofReal_mul _ _
  have hh : initialMovingCutoffWeight value b d 0 cb cd sl sr y ≠ 0 := by
    rw [← he]
    exact Complex.ofReal_ne_zero.mpr h
  have hl := initialMovingCutoffWeight_bulk_product_lower value hvalue b d 0 cb cd sl sr y hh
  exact le_of_lt (by simpa only [y, Sum.elim_inr, Nat.cast_prod] using hl)

theorem initialHalfBulkProduct_product_lower {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (n : ℕ) (slot : TreeLeafIndex n × Fin (b + b) → P)
    (h : initialHalfBulkProduct value b d cb cd sl sr n slot ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) ≤ ((∏ j, value (slot j) : ℕ) : ℝ) := by
  induction n with
  | zero =>
    have hl := initialHalfBulkWeight_product_lower value hvalue b d cb cd sl sr
      (fun i => slot ((), i)) h
    have hp := Fintype.prod_prod_type (fun j : Unit × Fin (b + b) => value (slot j))
    simp only [Fintype.prod_unique] at hp
    rw [pow_zero, Nat.cast_one, one_mul]
    change Real.exp (2 * cb - 2) ≤ ↑(∏ j : Unit × Fin (b + b), value (slot j))
    simp only [finite_univ_canonical] at hp hl ⊢
    rw [hp]
    exact hl
  | succ n ih =>
    have hL := ih (fun j => slot (.inl j.1, j.2)) (left_ne_zero_of_mul h)
    have hR := ih (fun j => slot (.inr j.1, j.2)) (right_ne_zero_of_mul h)
    have he : Real.exp ((2 ^ (n + 1) : ℕ) * (2 * cb - 2)) =
        Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) * Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) := by
      rw [← Real.exp_add, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
      congr 1
      ring
    rw [he]
    convert mul_le_mul hL hR (Real.exp_nonneg _) (Nat.cast_nonneg _) using 1
    rw [← Nat.cast_mul]
    congr 1
    have hp := Fintype.prod_prod_type
      (fun j : (TreeLeafIndex n ⊕ TreeLeafIndex n) × Fin (b + b) => value (slot j))
    have hs := Fintype.prod_sum_type
      (fun j : TreeLeafIndex n ⊕ TreeLeafIndex n => ∏ i : Fin (b + b), value (slot (j, i)))
    have hpL := Fintype.prod_prod_type
      (fun j : TreeLeafIndex n × Fin (b + b) => value (slot (.inl j.1, j.2)))
    have hpR := Fintype.prod_prod_type
      (fun j : TreeLeafIndex n × Fin (b + b) => value (slot (.inr j.1, j.2)))
    simp only [finite_univ_canonical] at hp hs hpL hpR ⊢
    exact hp.trans (hs.trans (congrArg₂ (· * ·) hpL.symm hpR.symm))

end Ostmann

end OAI
