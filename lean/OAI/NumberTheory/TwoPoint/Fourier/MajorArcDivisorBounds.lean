import OAI.NumberTheory.TwoPoint.Fourier.MajorArcGCD
import Mathlib.NumberTheory.Harmonic.Bounds

namespace OAI

/-! The divided-scale volume pays for the gcd sum. The main term costs
only sqrt(q)(1+log q), while endpoint rounding has an explicit q factor. -/

namespace TwoPointCorrelations

open Finset

lemma major_arc_divisor_reciprocal (q : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, (d:ℝ)⁻¹) ≤ 1+Real.log q := by
  have hs : q.divisors ⊆ Icc 1 q := by
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdq hq,Nat.le_of_dvd hq hdq⟩
  calc
    _  ≤  ∑ d ∈ Icc 1 q, (d:ℝ)⁻¹ := sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
    _ = (harmonic q:ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    _  ≤  _ := harmonic_le_one_add_log q

lemma major_arc_divisor_weighted (q : ℕ) (hq : 0 < q) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∑ d ∈ q.divisors, Real.sqrt ((q/d:ℕ):ℝ)*(A/(d:ℝ)+B))  ≤
      Real.sqrt (q:ℝ)*((1+Real.log q)*A+(q:ℝ)*B) := by
  calc
    _  ≤  ∑ d ∈ q.divisors, Real.sqrt (q:ℝ)*(A/(d:ℝ)+B) := by
      apply sum_le_sum
      intro d _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.div_le_self q d
    _ = Real.sqrt (q:ℝ)*(A*(∑ d ∈ q.divisors,(d:ℝ)⁻¹)+(q.divisors.card:ℝ)*B) := by
      rw [mul_sum]
      simp only [div_eq_mul_inv,sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul]
    _  ≤  _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply add_le_add
      · simpa only [mul_comm] using mul_le_mul_of_nonneg_left
          (major_arc_divisor_reciprocal q hq) hA
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self q) hB

lemma major_arc_log_overhead {W : ℝ} (hW : 1 ≤ W) :
    1+Real.log W ≤ 101*W^(1/100:ℝ) := by
  have hp : 1 ≤ W^(1/100:ℝ) := Real.one_le_rpow hW (by norm_num)
  have hl := Real.log_le_rpow_div (show 0 ≤ W by linarith) (show (0:ℝ) < 1/100 by norm_num)
  nlinarith

end TwoPointCorrelations

end OAI
