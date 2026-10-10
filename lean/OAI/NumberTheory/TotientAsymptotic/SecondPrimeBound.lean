import OAI.NumberTheory.TotientAsymptotic.PreimageLoglogBound
import OAI.NumberTheory.TotientAsymptotic.BootstrapLargeHead

namespace OAI

/-! All nonleading prime coordinates lie below the ambient log-log scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma ford_second_prime_sq_le {n : ℕ} (hn : 0 < n) : (fordPrime n 1)^2 ≤ n := by
  have ho := fordPrime_le_first n 1
  have hp := Nat.mul_le_mul_right (fordPrime n 1) ho
  have ht := Nat.le_mul_of_pos_right (fordPrime n 0*fordPrime n 1) (fordCofactor_pos n 2)
  rw [← ford_first_two_factorization hn] at ht
  simpa only [pow_two] using hp.trans ht

lemma all_preimages_square_bound : ∀ᶠ x : ℝ in atTop,
    ∀ n : ℕ,0 < n → (n.totient:ℝ) ≤ x → (n:ℝ) ≤ x^2 := by
  obtain ⟨C,hC,hpre⟩ := preimage_loglog_bound
  have hsmall := Real.isLittleO_log_id_atTop.bound (show (0:ℝ)<1/C by positivity)
  filter_upwards [hsmall,eventually_ge_atTop (Real.exp (Real.exp 1)),
    eventually_gt_atTop (1:ℝ)] with x hx hxexp hx1
  have hx0 : 0 < x := by linarith only [hx1]
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hlog : Real.log x ≤ (1/C)*x := (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs,abs_of_pos hx0,id_eq] using hx)
  have hBx : B x ≤ Real.log x := by
    have hh := Real.log_le_sub_one_of_pos hl
    change Real.log (Real.log x) ≤ Real.log x
    linarith only [hh]
  have hCB : C*B x ≤ x := by
    have hh := mul_le_mul_of_nonneg_left (hBx.trans hlog) hC.le
    simpa only [← mul_assoc,mul_one_div_cancel hC.ne',one_mul] using hh
  intro n hn hφ
  calc
    (n:ℝ) ≤ C*x*B x := hpre x hxexp n hn hφ
    _ = x*(C*B x) := by ring
    _ ≤ x*x := mul_le_mul_of_nonneg_left hCB hx0.le
    _ = x^2 := by ring

lemma all_preimages_second_coordinate : ∀ᶠ x : ℝ in atTop,
    ∀ n : ℕ,0 < n → (n.totient:ℝ) ≤ x → fordPrimeCoordinate n 1 ≤ B x := by
  filter_upwards [all_preimages_square_bound,B_tendsto.eventually (eventually_ge_atTop (0:ℝ)),
    eventually_gt_atTop (1:ℝ)] with x hx hB hx1
  intro n hn hφ
  have hnat : (fordPrime n 1:ℝ)^2 ≤ (n:ℝ) := by exact_mod_cast ford_second_prime_sq_le hn
  have hs : (fordPrime n 1:ℝ)^2 ≤ x^2 := hnat.trans (hx n hn hφ)
  have hprime : (fordPrime n 1:ℝ) ≤ x := by
    nlinarith only [hs,Nat.cast_nonneg (α:=ℝ) (fordPrime n 1),hx1]
  by_cases he : fordPrime n 1=1
  · simpa only [fordPrimeCoordinate,primeDoubleLog,he,Nat.cast_one,Real.log_one,
      Real.log_zero,max_self] using hB
  have hp1 : (1:ℝ) < fordPrime n 1 := by
    exact_mod_cast (show 1 < fordPrime n 1 from lt_of_le_of_ne (fordPrime_pos n 1) (Ne.symm he))
  apply max_le hB
  exact Real.log_le_log (Real.log_pos hp1)
    (Real.log_le_log (zero_lt_one.trans hp1) hprime)

end TotientAsymptotic

end

end OAI
