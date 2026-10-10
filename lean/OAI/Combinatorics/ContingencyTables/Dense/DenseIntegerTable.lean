import OAI.Combinatorics.ContingencyTables.Dense.DenseAcceptance

namespace OAI

/-!
# Integral dense completion formulas

The sampler fills dependent cells by integer sums and differences. The
acceptance test is exactly nonnegativity of these integers; accepted
outputs have the prescribed natural margins.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

def integerTable (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ) :
    Option I → Option J → ℤ
  | some i, some j => z (i, j)
  | some i, none => R (some i) - ∑ j, (z (i, j) : ℤ)
  | none, some j => P (some j) - ∑ i, (z (i, j) : ℤ)
  | none, none => R none - ∑ j, (P (some j) : ℤ) + ∑ i, ∑ j, (z (i, j) : ℤ)

def naturalTable (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ) :
    Option I → Option J → ℕ := fun i j => (integerTable R P z i j).toNat

theorem integerTable_cast (R : Option I → ℕ) (P : Option J → ℕ)
    (z : I × J → ℕ) (i : Option I) (j : Option J) :
    (integerTable R P z i j : ℝ) =
      table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (fun _ _ => 1) (fun p => (z p : ℝ)) i j := by
  cases i <;> cases j <;>
    simp only [integerTable, table, Int.cast_natCast, Int.cast_sub, Int.cast_add,
      Int.cast_sum, one_mul]

theorem scaled_integerTable_cast (R : Option I → ℕ) (P : Option J → ℕ)
    (w : I → J → ℕ) (hw : ∀ i j, 0 < w i j) (z : I × J → ℕ) :
    table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (fun i j => (w i j : ℝ))
      (fun p => (z p : ℝ) / (w p.1 p.2 : ℝ)) =
        (fun i j => (integerTable R P z i j : ℝ)) := by
  have hfree (i : I) (j : J) : (w i j : ℝ) * ((z (i, j) : ℝ) / (w i j : ℝ)) = z (i, j) :=
    mul_div_cancel₀ _ (by exact_mod_cast ne_of_gt (hw i j))
  funext i j
  rw [integerTable_cast]
  cases i <;> cases j <;> simp only [table, hfree, one_mul]

theorem integerTable_recover (R : Option I → ℕ) (P : Option J → ℕ)
    (X : Option I → Option J → ℕ) (hR : ∀ i, ∑ j, X i j = R i)
    (hP : ∀ j, ∑ i, X i j = P j) :
    integerTable R P (fun p => X (some p.1) (some p.2)) = (fun i j => (X i j : ℤ)) := by
  have hr : ∀ i, ∑ j, (X i j : ℝ) = (R i : ℝ) := by
    intro i
    exact_mod_cast hR i
  have hc : ∀ j, ∑ i, (X i j : ℝ) = (P j : ℝ) := by
    intro j
    exact_mod_cast hP j
  have heq := table_recover (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
    (fun _ _ => 1) (fun _ _ => by norm_num) (fun i j => (X i j : ℝ)) hr hc
  simp only [div_one] at heq
  funext i j
  apply Int.cast_injective (α := ℝ)
  rw [integerTable_cast]
  exact congrFun (congrFun heq i) j

theorem integer_acceptance_iff (R : Option I → ℕ) (P : Option J → ℕ)
    (w : I → J → ℕ) (hw : ∀ i j, 0 < w i j) (z : I × J → ℕ) :
    (∀ i j, 0 ≤ table (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
      (fun i j => (w i j : ℝ)) (fun p => (z p : ℝ) / (w p.1 p.2 : ℝ)) i j) ↔
        ∀ i j, 0 ≤ integerTable R P z i j := by
  rw [scaled_integerTable_cast R P w hw z]
  constructor
  · intro h i j
    have hij := h i j
    change (0 : ℝ) ≤ (integerTable R P z i j : ℝ) at hij
    exact_mod_cast hij
  · intro h i j
    change (0 : ℝ) ≤ (integerTable R P z i j : ℝ)
    exact_mod_cast h i j

theorem naturalTable_cast (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ)
    (hz : ∀ i j, 0 ≤ integerTable R P z i j) (i : Option I) (j : Option J) :
    (naturalTable R P z i j : ℝ) = (integerTable R P z i j : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg (hz i j)

theorem naturalTable_rows (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ)
    (hz : ∀ i j, 0 ≤ integerTable R P z i j) (i : Option I) :
    ∑ j, naturalTable R P z i j = R i := by
  apply Nat.cast_injective (R := ℝ)
  push_cast
  simp_rw [naturalTable_cast R P z hz, integerTable_cast]
  exact table_rows _ _ _ _ i

theorem naturalTable_columns (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ)
    (hz : ∀ i j, 0 ≤ integerTable R P z i j) (htotal : ∑ i, R i = ∑ j, P j) (j : Option J) :
    ∑ i, naturalTable R P z i j = P j := by
  apply Nat.cast_injective (R := ℝ)
  push_cast
  simp_rw [naturalTable_cast R P z hz, integerTable_cast]
  exact table_columns _ _ _ _ (by exact_mod_cast htotal) j

theorem naturalTable_free (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ) (i : I) (j : J) :
    naturalTable R P z (some i) (some j) = z (i, j) := by
  simp only [naturalTable, integerTable, Int.toNat_natCast]

theorem naturalTable_unique (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ)
    (hz : ∀ i j, 0 ≤ integerTable R P z i j)
    (X : Option I → Option J → ℕ) (hR : ∀ i, ∑ j, X i j = R i)
    (hP : ∀ j, ∑ i, X i j = P j) (hX : ∀ i j, X (some i) (some j) = z (i, j)) :
    naturalTable R P z = X := by
  have htotal : ∑ i, R i = ∑ j, P j := by
    simp_rw [← hR, ← hP]
    exact Finset.sum_comm
  have heq : (fun i j => (naturalTable R P z i j : ℝ)) = (fun i j => (X i j : ℝ)) := by
    apply table_unique
    · intro i
      have ha := naturalTable_rows R P z hz i
      exact_mod_cast ha.trans (hR i).symm
    · intro j
      have ha := naturalTable_columns R P z hz htotal j
      exact_mod_cast ha.trans (hP j).symm
    · intro i j
      rw [naturalTable_free, hX]
  funext i j
  exact Nat.cast_injective (congrFun (congrFun heq i) j)

end ContingencyTables.DenseAffine

end OAI
