import Mathlib
import OAI.Probability.SKBarriers.Interpolation.AdaptiveODERegular

namespace OAI

section

section
noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem cumulativeGapMap_sum (k : ℕ) (q : Fin (k+1) → ℝ) :
    ∑ b, cumulativeGapMap k q b = q (Fin.last k) := by
  rw [Fin.sum_univ_succ]
  simp only [cumulativeGapMap_zero,cumulativeGapMap_succ,Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ q
  have h2 := Fin.sum_univ_castSucc q
  linarith

theorem cumulativeGapMap_castSucc (k : ℕ) (q : Fin (k+2) → ℝ) (b : Fin (k+1)) :
    cumulativeGapMap (k+1) q b.castSucc = cumulativeGapMap k (fun i => q i.castSucc) b := by
  refine Fin.cases ?_ (fun i => ?_) b
  · rfl
  · rfl

theorem cumulativeGapMap_partial_sum (k : ℕ) (q : Fin (k+1) → ℝ) (l : Fin (k+1)) :
    (∑ b, if b ≤ l then cumulativeGapMap k q b else 0) = q l := by
  induction k with
  | zero => simp [Fin.eq_zero l]
  | succ k ih =>
    refine Fin.lastCases ?_ (fun l => ?_) l
    · simp only [Fin.le_last,ite_true,cumulativeGapMap_sum]
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.castSucc_le_castSucc_iff,cumulativeGapMap_castSucc]
      have h : ¬ Fin.last (k+1) ≤ l.castSucc := by simp [Fin.le_def]; omega
      rw [ite_eq_right h,add_zero]
      exact ih (fun i => q i.castSucc) l

theorem adaptive_field_summation (k : ℕ) (r w : Fin (k+1) → ℝ) :
    (∑ b, cumulativeGapMap k r b*(1-∑ l, if b ≤ l then w l*r l else 0)) =
      r (Fin.last k)-∑ l, w l*(r l)^2 := by
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,cumulativeGapMap_sum,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  have he (b : Fin (k+1)) : cumulativeGapMap k r b*(if b ≤ l then w l*r l else 0) =
      (if b ≤ l then cumulativeGapMap k r b else 0)*(w l*r l) := by split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul,cumulativeGapMap_partial_sum]
  ring

theorem adaptive_pressure_algebra (k : ℕ) (r w e : Fin (k+1) → ℝ) (β : ℝ) :
    -(β^2/4)*(1-∑ l, w l*((r l)^2+e l))+
      (β^2/2)*(∑ b, cumulativeGapMap k r b*(1-∑ l, if b ≤ l then w l*r l else 0)) =
      (β^2/4)*(-1+2*r (Fin.last k)-∑ l, w l*(r l)^2+∑ l, w l*e l) := by
  rw [adaptive_field_summation]
  simp only [mul_add,Finset.sum_add_distrib]
  ring
end SK.Analytic

end
end

end

end OAI
