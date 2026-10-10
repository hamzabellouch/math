import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteVariance
import OAI.Combinatorics.KMedian.Probability.ProbabilitySupport

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

omit [Fintype I] in
 theorem expect_abs_centered_le_sqrt (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    μ.expect (fun ω => |X ω-μ.expect X|) ≤ Real.sqrt (μ.variance X) := by
  have hs := μ.sq_expect_le_expect_sq (fun ω => |X ω-μ.expect X|)
  simp only [sq_abs] at hs
  exact (Real.le_sqrt (μ.expect_nonneg (fun _ => abs_nonneg _)) (μ.variance_nonneg X)).mpr hs

omit [Fintype I] in
 theorem adjacent_variance (μ : FiniteLaw Ω) (X : Ω → ℝ) {m q : ℝ}
    (hm : 0 ≤ m) (hx : ∀ ω, 0 < μ.weight ω → X ω=m ∨ X ω=m+1)
    (hmean : μ.expect X=q) : μ.variance X ≤ q := by
  have hsq : μ.expect (fun ω => (X ω)^2)=(2*m+1)*q-m*(m+1) := by
    calc
      _ = μ.expect (fun ω => (2*m+1)*X ω-m*(m+1)) := by
        apply μ.expect_congr_support
        intro ω hω
        rcases hx ω hω with h | h <;> rw [h] <;> ring
      _ = _ := by rw [expect_sub, expect_mul, expect_const, hmean]
  rw [variance_eq, hsq, hmean]
  nlinarith only [sq_nonneg (q-m), hm]

theorem variance_sum_le (μ : FiniteLaw Ω) (X : I → Ω → ℝ) (q v : I → ℝ)
    (hmean : ∀ i, μ.expect (X i)=q i)
    (hvar : ∀ i, μ.variance (X i) ≤ v i)
    (hpair : ∀ i j, i ≠ j → μ.expect (fun ω => X i ω*X j ω) ≤ q i*q j) :
    μ.variance (fun ω => ∑ i, X i ω) ≤ ∑ i, v i := by
  classical
  have hs : μ.expect (fun ω => (∑ i, X i ω)^2) ≤ (∑ i, q i)^2+∑ i, v i := by
    have hp : ∀ i j, μ.expect (fun ω => X i ω*X j ω) ≤ q i*q j+(if i=j then v i else 0) := by
      intro i j
      by_cases h : i=j
      · subst j
        have hv := hvar i
        rw [variance_eq, hmean i] at hv
        simpa only [ite_true, sq] using (by linarith only [hv] : μ.expect (fun ω => (X i ω)^2) ≤ q i^2+v i)
      · simpa only [ite_eq_right h, add_zero] using hpair i j h
    calc
      _ = ∑ i, ∑ j, μ.expect (fun ω => X i ω*X j ω) := by
        simp_rw [sq, sum_mul_sum, expect_sum]
      _ ≤ ∑ i, ∑ j, (q i*q j+if i=j then v i else 0) :=
        sum_le_sum (fun i _ => sum_le_sum (fun j _ => hp i j))
      _ = _ := by
        simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum, ← sum_mul, sq]
  rw [variance_eq, expect_sum]
  simp only [hmean] at *
  linarith only [hs]

omit [Fintype I] in
 theorem variance_mul (μ : FiniteLaw Ω) (X : Ω → ℝ) (g : ℝ) :
    μ.variance (fun ω => g*X ω)=g^2*μ.variance X := by
  rw [variance_eq, variance_eq, expect_mul]
  simp_rw [mul_pow, expect_mul]
  ring

end MetricKMedian.FiniteLaw
end
end

end OAI
