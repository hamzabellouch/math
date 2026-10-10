import OAI.NumberTheory.Ostmann.QuadraticCenter.WalshMoments

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem real_moment_le_sign_moment_of_correlations
    {ι α β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (R : Finset β)
    (χ : β → α → ℝ) (e : α → ι → ℕ) (b : α → ℝ)
    (k : ℕ) (Y E : ℝ)
    (hcor : ∀ f : Fin k → α,
      |∑ m ∈ R, ∏ j, χ m (f j)| ≤
        Y * (if ∀ i, Even (∑ j, e (f j) i) then 1 else 0) + E) :
    (∑ m ∈ R, (∑ a, b a * χ m a) ^ k) ≤
      Y * signMean (fun ε => (∑ a, |b a| * signMonomial (e a) ε) ^ k) +
        E * (∑ a, |b a|) ^ k := by
  classical
  have hpower (m : β) : (∑ a, b a * χ m a) ^ k =
      ∑ f : Fin k → α, (∏ j, b (f j)) * ∏ j, χ m (f j) := by
    simpa only [Fintype.piFinset_univ, Finset.prod_mul_distrib] using
      Finset.sum_pow' Finset.univ (fun a => b a * χ m a) k
  have habspower : (∑ a, |b a|) ^ k =
      ∑ f : Fin k → α, ∏ j, |b (f j)| := by
    simpa only [Fintype.piFinset_univ] using
      Finset.sum_pow' Finset.univ (fun a => |b a|) k
  simp_rw [hpower]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ f : Fin k → α, (∏ j, |b (f j)|) *
        (Y * (if ∀ i, Even (∑ j, e (f j) i) then 1 else 0) + E) := by
      apply Finset.sum_le_sum
      intro f hf
      calc
        _ ≤ |(∏ j, b (f j)) * ∑ m ∈ R, ∏ j, χ m (f j)| := le_abs_self _
        _ = (∏ j, |b (f j)|) * |∑ m ∈ R, ∏ j, χ m (f j)| := by
          rw [abs_mul, Finset.abs_prod]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcor f)
          (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    _ = _ := by
      rw [signMean_power_sum, habspower]
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

end Ostmann.QuadraticCenter

end OAI
