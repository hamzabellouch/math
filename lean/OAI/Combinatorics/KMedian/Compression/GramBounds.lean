import Mathlib

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix
variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
                                                                      
theorem gram_entry_bound (A : Matrix R C ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (c d : C) :
    |(A.transpose*A) c d| ≤ (Fintype.card R:ℤ)*M^2 := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ r, |A r c*A r d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R, M^2 := sum_le_sum (fun r _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hA r c) (hA r d) (abs_nonneg _) hM)
    _ = _ := by simp

omit [Fintype C] [DecidableEq C] in
theorem gram_rhs_bound (A : Matrix R C ℤ) (w : R → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (hw : ∀ r, |w r| ≤ M) (c : C) :
    |(A.transpose*ᵥw) c| ≤ (Fintype.card R:ℤ)*M^2 := by
  change |∑ r, A r c*w r| ≤ _
  calc
    _ ≤ ∑ r, |A r c*w r| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R, M^2 := sum_le_sum (fun r _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hA r c) (hw r) (abs_nonneg _) hM)
    _ = _ := by simp

theorem gram_det_bound (A : Matrix R C ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) :
    |(A.transpose*A).det| ≤ (Nat.factorial (Fintype.card C):ℤ)*
      ((Fintype.card R:ℤ)*M^2)^(Fintype.card C) := by
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) (gram_entry_bound A M hM hA))

theorem gram_cramer_bound (A : Matrix R C ℤ) (w : R → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (hw : ∀ r, |w r| ≤ M) (c : C) :
    |((A.transpose*A).cramer (A.transpose*ᵥw)) c| ≤ (Nat.factorial (Fintype.card C):ℤ)*
      ((Fintype.card R:ℤ)*M^2)^(Fintype.card C) := by
  rw [Matrix.cramer_apply]
  have hentry : ∀ i j, |((A.transpose*A).updateCol c (A.transpose*ᵥw)) i j| ≤
      (Fintype.card R:ℤ)*M^2 := by
    intro i j
    by_cases hj : j=c
    · subst j
      simpa using gram_rhs_bound A w M hM hA hw i
    · simpa [Matrix.updateCol_apply,hj] using gram_entry_bound A M hM hA i j
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) hentry)

end MetricKMedian.Compression

end OAI
