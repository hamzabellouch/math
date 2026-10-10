import OAI.NumberTheory.TwoPoint.Walks.ColumnRankRelations

namespace OAI

/-! Concrete fixed-column coefficients and the size hypothesis for random-prime rank. -/

namespace TwoPointCorrelations

open Finset Matrix

namespace SignedStep

def columnCoefficient (a : SignedStep) (h other : ℕ) : ℤ :=
  (if a.forward then 1 else -1) * (h : ℤ) * a.padding * other

/-- Once the other columns are fixed, the coefficient contains no prime
variable from the resampled column. -/
lemma displacement_eq_columnCoefficient (a : SignedStep) (h p other : ℕ)
    (htuple : a.tuple = p * other) :
    a.displacement h = a.columnCoefficient h other * p := by
  simp only [displacement, columnCoefficient, htuple, Nat.cast_mul]
  ring

lemma abs_columnCoefficient (a : SignedStep) (h other : ℕ) :
    |a.columnCoefficient h other| = (h : ℤ) * a.padding * other := by
  cases hb : a.forward <;> simp [columnCoefficient, hb, abs_mul]

end SignedStep

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

lemma integerColumnDeparture_abs_sum_le (label : ℕ → α) (t : ℕ → ℤ) (n : ℕ) :
    (∑ z, |integerColumnDeparture label t n z|) ≤ ∑ a ∈ range n, |t a| := by
  calc
    _ ≤ ∑ z, ∑ a ∈ range n, |if label a = z then t a else 0| := by
      apply sum_le_sum
      intro z _
      exact abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      simp only [apply_ite abs, abs_zero]
      simp [eq_comm]

omit [Fintype ρ] [DecidableEq ρ] in
lemma columnDifference_abs_sum_le (label : ℕ → α) (t : ℕ → ℤ)
    (left right : ρ → ℕ) (i : ρ) :
    (∑ z, |columnDifference label t left right i z|) ≤
      (∑ a ∈ range (left i), |t a|) + ∑ a ∈ range (right i), |t a| := by
  calc
    _ ≤ ∑ z, (|integerColumnDeparture label t (left i) z| +
          |integerColumnDeparture label t (right i) z|) := by
      apply sum_le_sum
      intro z _
      simpa only [columnDifference, sub_eq_add_neg, abs_neg] using
        abs_add_le (integerColumnDeparture label t (left i) z)
          (-integerColumnDeparture label t (right i) z)
    _ = _ := sum_add_distrib
    _ ≤ _ := add_le_add (integerColumnDeparture_abs_sum_le label t (left i))
      (integerColumnDeparture_abs_sum_le label t (right i))

omit [Fintype ρ] [DecidableEq ρ] in
lemma columnDifference_abs_sum_le_uniform (label : ℕ → α) (t : ℕ → ℤ)
    (left right : ρ → ℕ) (N T : ℕ)
    (hl : ∀ i, left i ≤ N) (hr : ∀ i, right i ≤ N)
    (ht : ∀ a < N, |t a| ≤ (T : ℤ)) (i : ρ) :
    (∑ z, |columnDifference label t left right i z|) ≤ (2 * N * T : ℕ) := by
  have hprefix (n : ℕ) (hn : n ≤ N) : (∑ a ∈ range n, |t a|) ≤ (N * T : ℕ) := by
    calc
      _ ≤ ∑ _a ∈ range n, (T : ℤ) :=
        sum_le_sum (fun a ha => ht a ((mem_range.mp ha).trans_le hn))
      _ = (n : ℤ) * T := by simp
      _ ≤ (N : ℤ) * T := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Nat.cast_nonneg _)
      _ = _ := by simp
  have h := (columnDifference_abs_sum_le label t left right i).trans
    (add_le_add (hprefix _ (hl i)) (hprefix _ (hr i)))
  convert h using 1
  push_cast
  ring

omit [DecidableEq ρ] in
lemma abs_primeDifference_le (P : Finset ℕ) (Q : ℕ) (hQ : ∀ p ∈ P, p ≤ Q)
    (w : ρ → α → ℤ) (pivot : ρ → α) (hp : Function.Injective pivot)
    (B : ℕ) (hrow : ∀ i, (∑ z, |w i z|) ≤ (B : ℤ))
    (y z : ρ → P) (i : ρ) :
    |primeDifference P (fun i j => w i (pivot j)) y z i| ≤ (B * Q : ℕ) := by
  have hdelta (j : ρ) : |((y j).val : ℤ) - ((z j).val : ℤ)| ≤ (Q : ℤ) := by
    have hy : ((y j).val : ℤ) ≤ Q := by exact_mod_cast hQ _ (y j).property
    have hz : ((z j).val : ℤ) ≤ Q := by exact_mod_cast hQ _ (z j).property
    have hy0 : (0 : ℤ) ≤ (y j).val := Nat.cast_nonneg _
    have hz0 : (0 : ℤ) ≤ (z j).val := Nat.cast_nonneg _
    exact abs_le.mpr (by constructor <;> omega)
  have hpivot : (∑ j, |w i (pivot j)|) ≤ (B : ℤ) := by
    calc
      _ = ∑ a ∈ univ.image pivot, |w i a| := (sum_image (fun _ _ _ _ h => hp h)).symm
      _ ≤ ∑ a, |w i a| := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => abs_nonneg _)
      _ ≤ _ := hrow i
  change |∑ j, w i (pivot j) * (((y j).val : ℤ) - ((z j).val : ℤ))| ≤ _
  calc
    _ ≤ ∑ j, |w i (pivot j) * (((y j).val : ℤ) - ((z j).val : ℤ))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |w i (pivot j)| * (Q : ℤ) := by
      apply sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hdelta j) (abs_nonneg _)
    _ = (∑ j, |w i (pivot j)|) * Q := (sum_mul univ _ _).symm
    _ ≤ (B : ℤ) * Q := mul_le_mul_of_nonneg_right hpivot (Nat.cast_nonneg _)
    _ = _ := by simp

omit [DecidableEq ρ] in
lemma primeDifference_natAbs_le (P : Finset ℕ) (Q : ℕ) (hQ : ∀ p ∈ P, p ≤ Q)
    (w : ρ → α → ℤ) (pivot : ρ → α) (hp : Function.Injective pivot)
    (B : ℕ) (hrow : ∀ i, (∑ z, |w i z|) ≤ (B : ℤ))
    (y z : ρ → P) (i : ρ) :
    (primeDifference P (fun i j => w i (pivot j)) y z i).natAbs ≤ B * Q := by
  have h := abs_primeDifference_le P Q hQ w pivot hp B hrow y z i
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

end TwoPointCorrelations

end OAI
