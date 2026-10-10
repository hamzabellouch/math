import OAI.NumberTheory.JointDickman.Arithmetic.SmoothedBilinear

namespace OAI

/-! # Removing a logarithmic weight from a bounded exponential sum -/
namespace JointDickman
open Finset

lemma sum_log_Icc_factorial (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.log n) = Real.log (N.factorial:ℝ) := by
  have hprod : (∏ n ∈ Icc 1 N, n) = N.factorial := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [prod_Icc_succ_top (by omega),ih,Nat.factorial_succ]
      ring
  rw [←Real.log_prod (fun n hn => by exact_mod_cast (show n ≠ 0 by have := (mem_Icc.mp hn).1; omega)),
    ←Nat.cast_prod,hprod]

lemma sum_log_quotient_le (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Icc 1 N, (Real.log N-Real.log n)) ≤ (N:ℝ) := by
  rw [sum_sub_distrib,sum_const,Nat.card_Icc]
  simp only [Nat.add_sub_cancel,nsmul_eq_mul,sum_log_Icc_factorial]
  have hs := Stirling.le_log_factorial_stirling hN.ne'
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hpi : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

theorem logarithmic_weight_error (g : ℕ → ℂ) (N : ℕ) (hN : 0 < N)
    (hg : ∀ n ∈ Icc 1 N, ‖g n‖ ≤ 1) :
    ‖(Real.log N:ℂ)*(∑ n ∈ Icc 1 N, g n) -
      ∑ n ∈ Icc 1 N, (Real.log n:ℂ)*g n‖ ≤ (N:ℝ) := by
  have he : (Real.log N:ℂ)*(∑ n ∈ Icc 1 N, g n) -
      ∑ n ∈ Icc 1 N, (Real.log n:ℂ)*g n =
      ∑ n ∈ Icc 1 N, ((Real.log N-Real.log n:ℝ):ℂ)*g n := by
    rw [mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    push_cast
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun n hn => ?_)).trans (sum_log_quotient_le N hN)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hlog : 0 ≤ Real.log N-Real.log n := sub_nonneg.mpr
    (Real.log_le_log hn0 (by exact_mod_cast (mem_Icc.mp hn).2))
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hg n hn) hlog

theorem unweighted_sum_le_logarithmic_sum (g : ℕ → ℂ) (N : ℕ) (hN : 0 < N)
    (hg : ∀ n ∈ Icc 1 N, ‖g n‖ ≤ 1) :
    Real.log N * ‖∑ n ∈ Icc 1 N, g n‖ ≤
      (N:ℝ) + ‖∑ n ∈ Icc 1 N, (Real.log n:ℂ)*g n‖ := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ = ‖(Real.log N:ℂ)*(∑ n ∈ Icc 1 N, g n)‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
    _ ≤ ‖(Real.log N:ℂ)*(∑ n ∈ Icc 1 N, g n) -
        ∑ n ∈ Icc 1 N, (Real.log n:ℂ)*g n‖ +
        ‖∑ n ∈ Icc 1 N, (Real.log n:ℂ)*g n‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := add_le_add (logarithmic_weight_error g N hN hg) le_rfl

end JointDickman

end OAI
