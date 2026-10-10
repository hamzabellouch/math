import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Failure

namespace OAI

namespace MetricKMedianRecovery.LogPolynomial

lemma affine_log_bound (B D : ℝ) : ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 2 ≤ x →
    B+D*Real.log x ≤ A*Real.log x := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|B|/Real.log 2+|D|+1,by positivity,?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog0 : 0 ≤ Real.log x := (Real.log_nonneg (by linarith : 1 ≤ x))
  have hfirst : |B| ≤ (|B|/Real.log 2)*Real.log x := by
    calc
      _ = (|B|/Real.log 2)*Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  nlinarith [le_abs_self B,le_abs_self D,
    mul_le_mul_of_nonneg_right (le_abs_self D) hlog0]

lemma amplification_polynomial (c A g : ℝ) (e : ℕ) (hc : 0 ≤ c) (hg : 0 < g) :
    ∃ K d : ℕ, ∀ N L : ℕ, (L:ℝ) ≤ A*Real.log ((N:ℝ)+2) →
      ⌈Real.log (1/FailureBudget.failure g e N)/Real.exp (-c*L)⌉₊ ≤ K*(N+2)^d := by
  let m := ⌈c*A⌉₊
  let K := ⌈|Real.log (24/g)|+(e:ℝ)+1⌉₊
  refine ⟨K,m+1,?_⟩
  intro N L hL
  let b : ℝ := (N:ℝ)+2
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : 1 ≤ b := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hlog : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hexp : Real.exp (c*L) ≤ b^m := by
    have hmul : c*(L:ℝ) ≤ (m:ℝ)*Real.log b := by
      calc
        _ ≤ c*(A*Real.log b) := mul_le_mul_of_nonneg_left hL hc
        _ = (c*A)*Real.log b := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hlog
    calc
      _ ≤ Real.exp ((m:ℝ)*Real.log b) := Real.exp_le_exp.mpr hmul
      _ = b^m := by rw [Real.exp_nat_mul,Real.exp_log hb]
  have hlogb : Real.log b ≤ b := (Real.log_le_sub_one_of_pos hb).trans (by linarith)
  have hq : Real.log (1/FailureBudget.failure g e N) ≤
      (|Real.log (24/g)|+(e:ℝ))*b := by
    rw [FailureBudget.failure_log hg]
    have hconst : Real.log (24/g) ≤ |Real.log (24/g)| * b := by
      exact (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hb1)
    nlinarith [mul_le_mul_of_nonneg_left hlogb (Nat.cast_nonneg (α := ℝ) e)]
  have hnonneg : 0 ≤ (|Real.log (24/g)|+(e:ℝ))*b := by positivity
  have hdiv : Real.log (1/FailureBudget.failure g e N)/Real.exp (-c*L) ≤
      (|Real.log (24/g)|+(e:ℝ))*b^(m+1) := by
    rw [show -c*(L:ℝ) = -(c*L) by ring,Real.exp_neg,div_inv_eq_mul]
    calc
      _ ≤ ((|Real.log (24/g)|+(e:ℝ))*b)*Real.exp (c*L) :=
        mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
      _ ≤ ((|Real.log (24/g)|+(e:ℝ))*b)*b^m := mul_le_mul_of_nonneg_left hexp hnonneg
      _ = _ := by ring
  have hK : |Real.log (24/g)|+(e:ℝ)+1 ≤ (K:ℝ) := Nat.le_ceil _
  have hreal : Real.log (1/FailureBudget.failure g e N)/Real.exp (-c*L) ≤
      (K:ℝ)*b^(m+1) := by
    apply hdiv.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb.le _)
    linarith
  apply Nat.ceil_le.mpr
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,b] using hreal

end MetricKMedianRecovery.LogPolynomial

end OAI
