import OAI.Combinatorics.Ryser.Probability.Finite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample
namespace FiniteLaw

variable {Ω I : Type*} [Fintype Ω]

def variance (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  μ.expectation (fun ω => (f ω - μ.expectation f) ^ 2)

def covariance (μ : FiniteLaw Ω) (f g : Ω → ℝ) : ℝ :=
  μ.expectation (fun ω =>
    (f ω - μ.expectation f) * (g ω - μ.expectation g))

theorem variance_nonneg (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    0 ≤ μ.variance f :=
  μ.expectation_nonneg (fun ω => sq_nonneg (f ω - μ.expectation f))

theorem covariance_self (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.covariance f f = μ.variance f := by
  simp only [covariance, variance, pow_two]

theorem variance_add_sq_mean_sub_eq (μ : FiniteLaw Ω)
    (f : Ω → ℝ) (b : ℝ) :
    μ.variance f + (μ.expectation f - b) ^ 2 =
      μ.expectation (fun ω => (f ω - b) ^ 2) := by
  calc
    μ.variance f + (μ.expectation f - b) ^ 2 =
        μ.expectation (fun ω =>
          (f ω - μ.expectation f) ^ 2 +
            (2 * (μ.expectation f - b)) * (f ω - μ.expectation f) +
            (μ.expectation f - b) ^ 2) := by
      rw [expectation_add, expectation_add, expectation_smul,
        expectation_sub, expectation_const, expectation_const]
      simp [variance]
    _ = μ.expectation (fun ω => (f ω - b) ^ 2) := by
      congr 1
      funext ω
      ring

theorem variance_eq_expectation_sq_sub_sq (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.variance f = μ.expectation (fun ω => (f ω) ^ 2) -
      (μ.expectation f) ^ 2 := by
  apply (eq_sub_iff_add_eq).2
  simpa only [sub_zero] using μ.variance_add_sq_mean_sub_eq f 0

theorem variance_le_expectation_sub_const_sq (μ : FiniteLaw Ω)
    (f : Ω → ℝ) (b : ℝ) :
    μ.variance f ≤ μ.expectation (fun ω => (f ω - b) ^ 2) := by
  have h := μ.variance_add_sq_mean_sub_eq f b
  nlinarith [sq_nonneg (μ.expectation f - b)]

theorem variance_le_expectation_sq (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.variance f ≤ μ.expectation (fun ω => (f ω) ^ 2) := by
  simpa only [sub_zero] using μ.variance_le_expectation_sub_const_sq f 0

theorem covariance_eq_expectation_mul_sub_mul (μ : FiniteLaw Ω)
    (f g : Ω → ℝ) :
    μ.covariance f g = μ.expectation (fun ω => f ω * g ω) -
      μ.expectation f * μ.expectation g := by
  calc
    μ.covariance f g = μ.expectation (fun ω =>
        f ω * g ω - μ.expectation g * f ω - μ.expectation f * g ω +
          μ.expectation f * μ.expectation g) := by
      unfold covariance
      congr 1
      funext ω
      ring
    _ = μ.expectation (fun ω => f ω * g ω) -
        μ.expectation f * μ.expectation g := by
      rw [expectation_add, expectation_sub, expectation_sub,
        expectation_smul, expectation_smul, expectation_const]
      ring

theorem variance_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.variance (fun ω => f ω + g ω) =
      μ.variance f + μ.variance g + 2 * μ.covariance f g := by
  calc
    μ.variance (fun ω => f ω + g ω) = μ.expectation (fun ω =>
        (f ω - μ.expectation f) ^ 2 + (g ω - μ.expectation g) ^ 2 +
          2 * ((f ω - μ.expectation f) * (g ω - μ.expectation g))) := by
      unfold variance
      rw [expectation_add]
      congr 1
      funext ω
      ring
    _ = μ.variance f + μ.variance g + 2 * μ.covariance f g := by
      rw [expectation_add, expectation_add, expectation_smul]
      rfl

theorem variance_add_of_covariance_zero (μ : FiniteLaw Ω) (f g : Ω → ℝ)
    (hcov : μ.covariance f g = 0) :
    μ.variance (fun ω => f ω + g ω) = μ.variance f + μ.variance g := by
  rw [variance_add, hcov]
  ring

theorem variance_add_le (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.variance (fun ω => f ω + g ω) ≤
      2 * μ.variance f + 2 * μ.variance g := by
  calc
    μ.variance (fun ω => f ω + g ω) = μ.expectation (fun ω =>
        ((f ω - μ.expectation f) + (g ω - μ.expectation g)) ^ 2) := by
      unfold variance
      rw [expectation_add]
      congr 1
      funext ω
      ring
    _ ≤ μ.expectation (fun ω =>
        2 * (f ω - μ.expectation f) ^ 2 +
          2 * (g ω - μ.expectation g) ^ 2) := by
      apply μ.expectation_mono
      intro ω
      nlinarith [sq_nonneg ((f ω - μ.expectation f) -
        (g ω - μ.expectation g))]
    _ = 2 * μ.variance f + 2 * μ.variance g := by
      rw [expectation_add, expectation_smul, expectation_smul]
      rfl

theorem expectation_finset_sum (μ : FiniteLaw Ω) (S : Finset I)
    (f : I → Ω → ℝ) :
    μ.expectation (fun ω => ∑ i ∈ S, f i ω) =
      ∑ i ∈ S, μ.expectation (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem covariance_finset_sum_left (μ : FiniteLaw Ω) (S : Finset I)
    (f : I → Ω → ℝ) (g : Ω → ℝ) :
    μ.covariance (fun ω => ∑ i ∈ S, f i ω) g =
      ∑ i ∈ S, μ.covariance (f i) g := by
  unfold covariance
  rw [expectation_finset_sum μ S f]
  simp_rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  exact expectation_finset_sum μ S
    (fun i ω => (f i ω - μ.expectation (f i)) * (g ω - μ.expectation g))

theorem covariance_finset_sum_right (μ : FiniteLaw Ω) (S : Finset I)
    (g : Ω → ℝ) (f : I → Ω → ℝ) :
    μ.covariance g (fun ω => ∑ i ∈ S, f i ω) =
      ∑ i ∈ S, μ.covariance g (f i) := by
  unfold covariance
  rw [expectation_finset_sum μ S f]
  simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact expectation_finset_sum μ S
    (fun i ω => (g ω - μ.expectation g) * (f i ω - μ.expectation (f i)))

theorem variance_sum_le (μ : FiniteLaw Ω) (S : Finset I) (f : I → Ω → ℝ) :
    μ.variance (fun ω => ∑ i ∈ S, f i ω) ≤
      (S.card : ℝ) * ∑ i ∈ S, μ.variance (f i) := by
  classical
  calc
    μ.variance (fun ω => ∑ i ∈ S, f i ω) =
        μ.expectation (fun ω =>
          (∑ i ∈ S, (f i ω - μ.expectation (f i))) ^ 2) := by
      simp only [variance, expectation_finset_sum, Finset.sum_sub_distrib]
    _ ≤ μ.expectation (fun ω =>
        (S.card : ℝ) * ∑ i ∈ S, (f i ω - μ.expectation (f i)) ^ 2) := by
      apply μ.expectation_mono
      intro ω
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
        (Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : I => (1 : ℝ))
          (fun i => f i ω - μ.expectation (f i)))
    _ = (S.card : ℝ) * ∑ i ∈ S, μ.variance (f i) := by
      simp only [expectation_smul, expectation_finset_sum, variance]

theorem variance_sum_of_pairwise_covariance_zero
    (μ : FiniteLaw Ω) (S : Finset I) (f : I → Ω → ℝ)
    (hcov : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → μ.covariance (f i) (f j) = 0) :
    μ.variance (fun ω => ∑ i ∈ S, f i ω) =
      ∑ i ∈ S, μ.variance (f i) := by
  classical
  rw [← covariance_self μ (fun ω => ∑ i ∈ S, f i ω), covariance_finset_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [covariance_finset_sum_right]
  calc
    (∑ j ∈ S, μ.covariance (f i) (f j)) = μ.covariance (f i) (f i) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        exact hcov i hi j hj (Ne.symm hji)
      · intro hnot
        exact (hnot hi).elim
    _ = μ.variance (f i) := covariance_self μ (f i)

theorem variance_sum_of_pairwise_expectation_mul
    (μ : FiniteLaw Ω) (S : Finset I) (f : I → Ω → ℝ)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      μ.expectation (fun ω => f i ω * f j ω) =
        μ.expectation (f i) * μ.expectation (f j)) :
    μ.variance (fun ω => ∑ i ∈ S, f i ω) =
      ∑ i ∈ S, μ.variance (f i) := by
  apply μ.variance_sum_of_pairwise_covariance_zero S f
  intro i hi j hj hij
  rw [covariance_eq_expectation_mul_sub_mul, hpair i hi j hj hij, sub_self]

theorem variance_le_sq_of_bounds (μ : FiniteLaw Ω) (f : Ω → ℝ) {L : ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hfL : ∀ ω, f ω ≤ L) :
    μ.variance f ≤ L ^ 2 := by
  calc
    μ.variance f ≤ μ.expectation (fun ω => (f ω) ^ 2) :=
      μ.variance_le_expectation_sq f
    _ ≤ μ.expectation (fun _ => L ^ 2) :=
      μ.expectation_mono (fun ω => pow_le_pow_left₀ (hf0 ω) (hfL ω) 2)
    _ = L ^ 2 := μ.expectation_const (L ^ 2)

theorem chebyshev (μ : FiniteLaw Ω) (f : Ω → ℝ) {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => t ≤ |f ω - μ.expectation f|) ≤ μ.variance f / t ^ 2 := by
  calc
    μ.prob (fun ω => t ≤ |f ω - μ.expectation f|) ≤
        μ.prob (fun ω => t ^ 2 ≤ (f ω - μ.expectation f) ^ 2) := by
      apply μ.prob_mono
      intro ω hω
      simpa only [sq_abs] using pow_le_pow_left₀ ht.le hω 2
    _ ≤ μ.variance f / t ^ 2 :=
      μ.prob_ge_le_expectation_div
        (fun ω => (f ω - μ.expectation f) ^ 2)
        (fun ω => sq_nonneg (f ω - μ.expectation f)) (pow_pos ht 2)

theorem prob_gt_mean_bound_add_le (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (m t : ℝ) (hm : μ.expectation f ≤ m) (ht : 0 < t) :
    μ.prob (fun ω => m + t < f ω) ≤ μ.variance f / t ^ 2 := by
  calc
    μ.prob (fun ω => m + t < f ω) ≤
        μ.prob (fun ω => t ≤ |f ω - μ.expectation f|) := by
      apply μ.prob_mono
      intro ω hω
      calc
        t ≤ f ω - μ.expectation f := by linarith
        _ ≤ |f ω - μ.expectation f| := le_abs_self _
    _ ≤ μ.variance f / t ^ 2 := μ.chebyshev f ht

theorem variance_le_sq_mul_prob_of_anchor (μ : FiniteLaw Ω)
    (f : Ω → ℝ) (P : Ω → Prop) (b L : ℝ)
    (hoff : ∀ ω, ¬ P ω → f ω = b)
    (hbound : ∀ ω, P ω → |f ω - b| ≤ L) :
    μ.variance f ≤ L ^ 2 * μ.prob P := by
  classical
  calc
    μ.variance f ≤ μ.expectation (fun ω => (f ω - b) ^ 2) :=
      μ.variance_le_expectation_sub_const_sq f b
    _ ≤ μ.expectation (fun ω => L ^ 2 * (if P ω then 1 else 0)) := by
      apply μ.expectation_mono
      intro ω
      by_cases hp : P ω
      · have hsq : (f ω - b) ^ 2 ≤ L ^ 2 := by
          simpa only [sq_abs] using
            pow_le_pow_left₀ (abs_nonneg (f ω - b)) (hbound ω hp) 2
        simpa [hp] using hsq
      · simp [hp, hoff ω hp]
    _ = L ^ 2 * μ.prob P := by
      rw [expectation_smul, ← μ.prob_eq_expectation P]

end FiniteLaw
end RyserCoveringCounterexample

end

end OAI
