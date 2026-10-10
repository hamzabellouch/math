import Mathlib
import OAI.Analysis.FreeWords.FactorialSum

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators

noncomputable section

theorem factorial_sqrt_bound {r p q : ℕ} (hp : p ≤ r) (hq : q ≤ r) :
    Real.sqrt ((p.factorial:ℝ) * q.factorial) ≤ (r.factorial:ℝ) := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Nat.cast_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity), pow_two]
  exact mul_le_mul (by exact_mod_cast Nat.factorial_le hp)
    (by exact_mod_cast Nat.factorial_le hq) (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem sum_cuts_numeric (m : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ q : Fin (m+2), Real.sqrt ((q.val.factorial:ℝ) * (m+1-q).factorial) * t^(m+1)) +
      (∑ j : Fin (m+1), (Real.sqrt ((j.val.factorial:ℝ) * (m-j).factorial) +
        t ^ 2 * Real.sqrt (((j.val+1).factorial:ℝ) * (m+1-j).factorial)) * t^m) ≤
      5 * Real.sqrt (m.factorial:ℝ) * t^m +
        ((2*(m+1)+1:ℝ) * (m+1).factorial) * t^(m+1) := by
  have hn : (∑ q : Fin (m+2), Real.sqrt ((q.val.factorial:ℝ) * (m+1-q).factorial) * t^(m+1)) ≤
      (m+2:ℝ) * (m+1).factorial * t^(m+1) := by
    calc
      _ ≤ ∑ q : Fin (m+2), ((m+1).factorial:ℝ) * t^(m+1) := by
        exact Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_right
          (factorial_sqrt_bound (by omega) (Nat.sub_le _ _)) (pow_nonneg ht _))
      _ = _ := by simp; ring
  have hl : (∑ j : Fin (m+1), Real.sqrt ((j.val.factorial:ℝ) * (m-j).factorial)) ≤
      5 * Real.sqrt (m.factorial:ℝ) := by
    simpa only [← Fin.sum_univ_eq_sum_range, factorialRoot] using factorialRoot_sum m
  have hs : (∑ j : Fin (m+1), Real.sqrt (((j.val+1).factorial:ℝ) * (m+1-j).factorial)) ≤
      (m+1:ℝ) * (m+1).factorial := by
    calc
      _ ≤ ∑ j : Fin (m+1), ((m+1).factorial:ℝ) := by
        exact Finset.sum_le_sum (fun j _ => factorial_sqrt_bound (by omega) (Nat.sub_le _ _))
      _ = _ := by simp
  have ht' : t^2*t^m ≤ t^(m+1) := by
    calc
      _ = t^(m+1)*t := by rw [pow_succ t m, pow_two]; ring
      _ ≤ _ := mul_le_of_le_one_right (pow_nonneg ht (m+1)) ht1
  have hs' : (t^2 * (∑ j : Fin (m+1), Real.sqrt (((j.val+1).factorial:ℝ) * (m+1-j).factorial))) * t^m ≤
      ((m+1:ℝ) * (m+1).factorial) * t^(m+1) := by
    calc
      _ = (∑ j : Fin (m+1), Real.sqrt (((j.val+1).factorial:ℝ) * (m+1-j).factorial)) * (t^2*t^m) := by ring
      _ ≤ ((m+1:ℝ) * (m+1).factorial) * (t^2*t^m) := mul_le_mul_of_nonneg_right hs (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left ht' (by positivity)
  have hl' := mul_le_mul_of_nonneg_right hl (pow_nonneg ht m)
  have he : (∑ j : Fin (m+1), (Real.sqrt ((j.val.factorial:ℝ) * (m-j).factorial) +
      t ^ 2 * Real.sqrt (((j.val+1).factorial:ℝ) * (m+1-j).factorial)) * t^m) =
      (∑ j : Fin (m+1), Real.sqrt ((j.val.factorial:ℝ) * (m-j).factorial))*t^m +
      (t^2 * (∑ j : Fin (m+1), Real.sqrt (((j.val+1).factorial:ℝ) * (m+1-j).factorial)))*t^m := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [he]
  nlinarith

end

end KKFreeWords
end

end OAI
