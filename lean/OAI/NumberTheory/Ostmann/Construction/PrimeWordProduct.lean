import OAI.NumberTheory.Ostmann.Construction.PrimeCellWordPriors

namespace OAI

/-! # Logarithmic size of an actual sampled prime-cell word -/

namespace Ostmann

open scoped BigOperators

theorem sampled_cell_word_log_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (h : Fin n → ℕ) (x : Fin n → P)
    (hx : productPrior (fun i => primeCellWordPrior P (h i)) x ≠ 0) :
    (∑ i, (h i : ℝ)) ≤ Real.log (∏ i, ((x i : ℕ) : ℝ)) ∧
      Real.log (∏ i, ((x i : ℕ) : ℝ)) ≤ (∑ i, (h i : ℝ)) + n := by
  have hcell (i : Fin n) : primeLogIndex (x i) = h i :=
    primeCellWordPrior_support P (h i) (x i)
      ((Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i))
  have hlog (i : Fin n) : (h i : ℝ) < Real.log ((x i : ℕ) : ℝ) ∧
      Real.log ((x i : ℕ) : ℝ) ≤ (h i : ℝ) + 1 := by
    simpa only [hcell i] using primeLogIndex_bounds (x i) (hP _ (x i).property)
  rw [Real.log_prod (fun i _ => by exact_mod_cast (hP _ (x i).property).ne_zero)]
  constructor
  · exact Finset.sum_le_sum (fun i _ => (hlog i).1.le)
  · calc
      _ ≤ ∑ i : Fin n, ((h i : ℝ) + 1) := Finset.sum_le_sum (fun i _ => (hlog i).2)
      _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem sampled_cell_word_target_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (h : Fin n → ℕ) (x : Fin n → P) (T E : ℝ)
    (hx : productPrior (fun i => primeCellWordPrior P (h i)) x ≠ 0)
    (htarget : |(∑ i, (h i : ℝ)) - T| ≤ E) :
    |Real.log (∏ i, ((x i : ℕ) : ℝ)) - T| ≤ E + n := by
  obtain ⟨hlo, hhi⟩ := sampled_cell_word_log_bounds P hP h x hx
  obtain ⟨htlo, hthi⟩ := abs_le.mp htarget
  apply abs_le.mpr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) n]

end Ostmann

end OAI
