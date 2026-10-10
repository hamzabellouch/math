import OAI.NumberTheory.TotientAsymptotic.FordUnbandedMass
import OAI.NumberTheory.TotientAsymptotic.CollisionAlgebra
import OAI.NumberTheory.TotientAsymptotic.FordCofactorStep
import OAI.NumberTheory.TotientAsymptotic.ThirdPrimeSize

namespace OAI

/-! The first failed row strictly separates the retained primes from the tail. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordRowSum (N : ℕ) (u : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc (j+1) N, a (r-j)*u r

lemma fordRowSum_le_previous {N j : ℕ} (hj : 0 < j) (u : ℕ → ℝ)
    (hu : ∀ r, 0 ≤ u r) : fordRowSum N u j ≤ fordRowSum N u (j-1) := by
  unfold fordRowSum
  calc
    _ ≤ ∑ r ∈ Finset.Icc (j+1) N, a (r-(j-1))*u r := by
      apply Finset.sum_le_sum
      intro r hr
      have hr := Finset.mem_Icc.mp hr
      apply mul_le_mul_of_nonneg_right _ (hu r)
      exact a_monotone_positive (by omega) (by omega)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        have hr := Finset.mem_Icc.mp hr
        exact Finset.mem_Icc.mpr (by omega)
      · intro r hr _
        have hr := Finset.mem_Icc.mp hr
        exact mul_nonneg (a_pos (by omega)).le (hu r)

lemma xi_monotone (x : ℝ) : Monotone (xi x) := by
  intro i j hij
  have hh : ((m x-j:ℕ):ℝ) ≤ (m x-i:ℕ) := by
    exact_mod_cast Nat.sub_le_sub_left hij (m x)
  have he : Real.exp (-((m x-i:ℕ):ℝ)/40) ≤ Real.exp (-((m x-j:ℕ):ℝ)/40) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold xi
  linarith

lemma first_failed_row_separates {x : ℝ} {N j : ℕ} (hj : 0 < j)
    (u : ℕ → ℝ) (hu : ∀ r, 0 ≤ u r)
    (hprev : fordRowSum N u (j-1) ≤ xi x (j-1)*u (j-1))
    (hfail : xi x j*u j < fordRowSum N u j) : u j < u (j-1) := by
  have hs := fordRowSum_le_previous (N:=N) hj u hu
  have hxi := xi_monotone x (Nat.sub_le j 1)
  have hpos := (xi_bounds x (j-1)).1
  have hm := mul_le_mul_of_nonneg_right hxi (hu j)
  nlinarith only [hs,hprev,hfail,hpos,hm]

lemma clamped_doubleLog_mono {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    max 0 (Real.log (Real.log (p:ℝ))) ≤ max 0 (Real.log (Real.log (q:ℝ))) := by
  by_cases hp1 : p=1
  · simp only [hp1,Nat.cast_one,Real.log_one,Real.log_zero,max_self]
    exact le_max_left _ _
  · have hp' : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    apply max_le_max le_rfl
    apply Real.log_le_log (Real.log_pos hp')
    exact Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hpq)

lemma fordPrime_lt_of_coordinate_lt {n i j : ℕ}
    (h : fordPrimeCoordinate n i < fordPrimeCoordinate n j) :
    fordPrime n i < fordPrime n j := by
  by_contra hh
  have hh := clamped_doubleLog_mono (fordPrime_pos n j) (Nat.le_of_not_gt hh)
  exact (not_lt_of_ge hh) h

theorem first_failed_row_prime_separation {x : ℝ} {n N j : ℕ} (hj : 0 < j)
    (hprev : fordRowSum N (fordPrimeCoordinate n) (j-1) ≤
      xi x (j-1)*fordPrimeCoordinate n (j-1))
    (hfail : xi x j*fordPrimeCoordinate n j < fordRowSum N (fordPrimeCoordinate n) j) :
    fordPrime n j < fordPrime n (j-1) := by
  apply fordPrime_lt_of_coordinate_lt
  exact first_failed_row_separates hj _ (fun r => le_max_left _ _) hprev hfail

lemma failed_row_coordinate_pos {x : ℝ} {n N j : ℕ}
    (hfail : xi x j*fordPrimeCoordinate n j < fordRowSum N (fordPrimeCoordinate n) j) :
    0 < fordPrimeCoordinate n j := by
  by_contra hh
  have hj : fordPrimeCoordinate n j ≤ 0 := le_of_not_gt hh
  have hs : fordRowSum N (fordPrimeCoordinate n) j ≤ 0 := by
    apply Finset.sum_nonpos
    intro r hr
    have hr := Finset.mem_Icc.mp hr
    apply mul_nonpos_of_nonneg_of_nonpos (a_pos (by omega)).le
    exact (ford_coordinate_antitone n (by omega)).trans hj
  have hprod : 0 ≤ xi x j*fordPrimeCoordinate n j :=
    mul_nonneg (zero_le_one.trans (xi_bounds x j).1) (le_max_left _ _)
  linarith

lemma failed_row_index {x : ℝ} {n N j : ℕ}
    (hfail : xi x j*fordPrimeCoordinate n j < fordRowSum N (fordPrimeCoordinate n) j) :
    j < n.primeFactorsList.length := by
  have hh := failed_row_coordinate_pos hfail
  have hr : 0 < primeDoubleLog n j :=
    (lt_max_iff.mp hh).resolve_left (lt_irrefl 0)
  exact fordPrime_index_of_doubleLog_pos hr

lemma positive_ford_coordinate_lower {n j : ℕ} (hj : 0 < fordPrimeCoordinate n j) :
    (1/100:ℝ) ≤ fordPrimeCoordinate n j := by
  have hp3 : 3 ≤ fordPrime n j := by
    by_contra hp
    have hp12 : fordPrime n j=1 ∨ fordPrime n j=2 := by
      have := fordPrime_pos n j
      omega
    rcases hp12 with hp | hp
    · simp [fordPrimeCoordinate,primeDoubleLog,hp] at hj
    · have hl2 : Real.log (Real.log 2) < 0 := Real.log_neg
        (Real.log_pos (by norm_num)) (by linarith [Real.log_two_lt_d9])
      have hh : max 0 (Real.log (Real.log 2))=0 := max_eq_left hl2.le
      simp only [fordPrimeCoordinate,primeDoubleLog,hp,Nat.cast_ofNat,hh,lt_self_iff_false] at hj
  have hl3 : (1/100:ℝ) ≤ Real.log (Real.log 3) := by
    have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hi := inv_anti₀ (by norm_num : (0:ℝ)<109/100)
      (show (109/100:ℝ) ≤ Real.log 3 by linarith [Real.log_three_gt_d9])
    have hh := Real.one_sub_inv_le_log_of_pos hl
    norm_num at hi
    linarith
  exact (hl3.trans (le_max_right _ _)).trans
    (clamped_doubleLog_mono (by norm_num : 0 < (3:ℕ)) hp3)

end TotientAsymptotic

end

end OAI
