import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteKernels
import OAI.Combinatorics.KMedian.Probability.ProbabilitySupport

namespace OAI

namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω : Type*} [Fintype Ω]

noncomputable def run (μ : FiniteLaw Ω) (K : ℕ → Ω → FiniteLaw Ω) : ℕ → FiniteLaw Ω
  | 0 => μ
  | n+1 => (run μ K n).bind (K n)

 theorem run_invariant (μ : FiniteLaw Ω) (K : ℕ → Ω → FiniteLaw Ω)
    (P : ℕ → Ω → Prop) (hzero : ∀ ω, 0 < μ.weight ω → P 0 ω)
    (hstep : ∀ n ω, P n ω → ∀ ξ, 0 < (K n ω).weight ξ → P (n+1) ξ) :
    ∀ n ω, 0 < (run μ K n).weight ω → P n ω := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    exact property_bind (run μ K n) (K n) _ (fun ω hω => hstep n ω (ih ω hω))

theorem run_drift (μ : FiniteLaw Ω) (K : ℕ → Ω → FiniteLaw Ω)
    (f : ℕ → Ω → ℝ) (error : ℕ → ℝ)
    (hstep : ∀ n ω, 0 < (run μ K n).weight ω →
      (K n ω).expect (f (n+1)) ≤ f n ω+error n) :
    ∀ n, (run μ K n).expect (f n) ≤ μ.expect (f 0)+∑ r ∈ range n, error r := by
  intro n
  induction n with
  | zero => simp only [run, range_zero, sum_empty, add_zero, le_refl]
  | succ n ih =>
    have hs := (run μ K n).expect_mono_support (hstep n)
    rw [expect_add, expect_const] at hs
    rw [run, expect_bind, sum_range_succ]
    linarith only [ih, hs]

 theorem run_geometric (μ : FiniteLaw Ω) (K : ℕ → Ω → FiniteLaw Ω)
    (f : ℕ → Ω → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hstep : ∀ n ω, 0 < (run μ K n).weight ω →
      (K n ω).expect (f (n+1)) ≤ ρ*f n ω) :
    ∀ n, (run μ K n).expect (f n) ≤ ρ^n*μ.expect (f 0) := by
  intro n
  induction n with
  | zero => simp only [run, pow_zero, one_mul, le_refl]
  | succ n ih =>
    have hs := (run μ K n).expect_mono_support (hstep n)
    rw [expect_mul] at hs
    rw [run, expect_bind]
    calc
      _ ≤ ρ*(run μ K n).expect (f n) := hs
      _ ≤ ρ*(ρ^n*μ.expect (f 0)) := mul_le_mul_of_nonneg_left ih hρ
      _ = _ := by rw [pow_succ]; ring

 theorem decay_exp {h : ℝ} (hh : h ≤ 2) (n : ℕ) :
    (1-h/2)^n ≤ Real.exp (-(n:ℝ)*h/2) := by
  have hbase : 1-h/2 ≤ Real.exp (-h/2) := by
    simpa only [sub_eq_add_neg, neg_div, add_comm] using Real.add_one_le_exp (-h/2)
  have hp := pow_le_pow_left₀ (show (0:ℝ) ≤ 1-h/2 by linarith only [hh]) hbase n
  calc
    _ ≤ (Real.exp (-h/2))^n := hp
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

 theorem run_survival (μ : FiniteLaw Ω) (K : ℕ → Ω → FiniteLaw Ω)
    (y : ℕ → Ω → ℝ) {h Λ : ℝ} {T : ℕ} (hh : h ≤ 2)
    (hzero : μ.expect (y 0)=1) (hT : Λ ≤ (T:ℝ)*h)
    (hstep : ∀ n ω, 0 < (run μ K n).weight ω →
      (K n ω).expect (y (n+1)) ≤ (1-h/2)*y n ω) :
    (run μ K T).expect (y T) ≤ Real.exp (-Λ/2) := by
  have ht := run_geometric μ K y (show 0 ≤ 1-h/2 by linarith only [hh]) hstep T
  rw [hzero, mul_one] at ht
  exact (ht.trans (decay_exp hh T)).trans
    (Real.exp_le_exp.mpr (by linarith only [hT]))

end MetricKMedian.FiniteLaw

end OAI
