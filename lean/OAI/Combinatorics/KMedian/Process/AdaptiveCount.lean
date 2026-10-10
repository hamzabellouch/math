import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteProcess

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem run_failure (μ : FiniteLaw Ω) (K : ℕ → Ω → FiniteLaw Ω)
    (P : ℕ → Ω → Prop) [∀ n, DecidablePred (P n)] {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hzero : μ.prob (fun ω => ¬P 0 ω)=0)
    (hstep : ∀ n ω, 0 < (run μ K n).weight ω → P n ω →
      (K n ω).prob (fun ξ => ¬P (n+1) ξ) ≤ ρ) :
    ∀ n, (run μ K n).prob (fun ω => ¬P n ω) ≤ (n:ℝ)*ρ := by
  classical
  intro n
  induction n with
  | zero => simpa only [run,hzero,Nat.cast_zero,zero_mul] using le_refl (0:ℝ)
  | succ n ih =>
    have hs := (run μ K n).expect_mono_support (f := fun ω => (K n ω).prob (fun ξ => ¬P (n+1) ξ))
      (h := fun ω => (if ¬P n ω then 1 else 0)+ρ) (by
        intro ω hω
        by_cases hh : P n ω
        · simpa only [hh,not_true_eq_false,ite_false,zero_add] using hstep n ω hω hh
        · rw [ite_eq_left hh]
          exact ((K n ω).prob_le_one _).trans (by linarith only [hρ]))
    change (run μ K n).expect (fun ω => (K n ω).prob (fun ξ => ¬P (n+1) ξ)) ≤ _ at hs
    rw [expect_add,expect_const] at hs
    change _ ≤ (run μ K n).prob (fun ω => ¬P n ω)+ρ at hs
    change ((run μ K n).bind (K n)).expect (fun ω => if ¬P (n+1) ω then 1 else 0) ≤ _
    rw [expect_bind,Nat.cast_add,Nat.cast_one]
    change (run μ K n).expect (fun ω => (K n ω).prob (fun ξ => ¬P (n+1) ξ)) ≤ _
    linarith only [hs,ih]

 theorem run_count_tail [DecidableEq Ω] (s₀ : Ω) (K : ℕ → Ω → FiniteLaw Ω)
    (M : Ω → ℝ) {C ρ : ℝ} (hρ : 0 ≤ ρ)
    (hstep : ∀ n ω, 0 < (run (dirac s₀) K n).weight ω →
      (K n ω).prob (fun ξ => M ω+C < M ξ) ≤ ρ) :
    ∀ n, (run (dirac s₀) K n).prob (fun ω => M s₀+(n:ℝ)*C < M ω) ≤ (n:ℝ)*ρ := by
  classical
  have hp := run_failure (dirac s₀) K (fun n ω => M ω ≤ M s₀+(n:ℝ)*C) hρ
    (by simp only [prob,expect_dirac,Nat.cast_zero,zero_mul,add_zero,le_refl,not_true_eq_false,ite_false])
    (by
      intro n ω hω hM
      apply le_trans _ (hstep n ω hω)
      apply prob_mono
      intro ξ hξ
      have hx : M s₀+(n+1:ℕ)*C < M ξ := lt_of_not_ge hξ
      push_cast at hx
      linarith only [hx,hM])
  intro n
  simpa only [not_le] using hp n

end MetricKMedian.FiniteLaw
end
end

end OAI
