import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

structure FinitePrior (ι : Type*) [Fintype ι] where
  mass : ι → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  mass_total : ∑ i, mass i = 1

namespace FinitePrior
variable {ι : Type*} [Fintype ι]

def mean (μ : FinitePrior ι) (f : ι → ℝ) : ℝ := ∑ i, μ.mass i * f i

theorem mean_nonneg (μ : FinitePrior ι) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ μ.mean f := Finset.sum_nonneg fun i _ => mul_nonneg (μ.mass_nonneg i) (hf i)

@[simp] theorem mean_const (μ : FinitePrior ι) (c : ℝ) : μ.mean (fun _ => c) = c := by
  simp only [mean, ← Finset.sum_mul, μ.mass_total, one_mul]

theorem variance_identity (μ : FinitePrior ι) (f : ι → ℝ) :
    μ.mean (fun i => (f i - μ.mean f)^2) = μ.mean (fun i => (f i)^2) - (μ.mean f)^2 := by
  change (∑ i, μ.mass i * (f i - μ.mean f)^2) = _
  simp_rw [show ∀ i, μ.mass i * (f i - μ.mean f)^2 =
      μ.mass i * (f i)^2 - (2 * μ.mean f) * (μ.mass i * f i) +
        (μ.mean f)^2 * μ.mass i from fun i => by ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    μ.mass_total, mul_one]
  change μ.mean (fun i => (f i)^2) - (2 * μ.mean f) * μ.mean f + (μ.mean f)^2 = _
  ring

theorem mean_sq_le (μ : FinitePrior ι) (f : ι → ℝ) :
    (μ.mean f)^2 ≤ μ.mean (fun i => (f i)^2) := by
  have h := μ.mean_nonneg (f := fun i => (f i - μ.mean f)^2) (fun _ => sq_nonneg _)
  rw [variance_identity] at h
  linarith

theorem positive_mean_sq (μ : FinitePrior ι) (f : ι → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hmean : a ≤ μ.mean f) :
    a^2 ≤ μ.mean (fun i => (f i)^2) := by
  calc
    a^2 ≤ (μ.mean f)^2 := pow_le_pow_left₀ ha hmean 2
    _ ≤ μ.mean (fun i => (f i)^2) := μ.mean_sq_le f

end FinitePrior

def finiteStatistic {ι : Type*} (s : Finset ι) (ψ T : ι → ℝ) : ℝ :=
  ∑ a ∈ s, ψ a * (T a)^2

theorem cardinal_mul_sum_sq_ge {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ a ∈ s, f a)^2 ≤ (s.card : ℝ) * ∑ a ∈ s, (f a)^2 := by
  simpa only [one_pow, mul_one, Finset.sum_const, nsmul_eq_mul, mul_comm]
    using Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ => (1 : ℝ))

theorem finiteStatistic_lower {ι : Type*} (s : Finset ι) (ψ T : ι → ℝ)
    {ψ₀ a : ℝ} (hψ₀ : 0 ≤ ψ₀) (ha : 0 ≤ a)
    (hψ : ∀ x ∈ s, ψ₀ ≤ ψ x)
    (hmean : (s.card : ℝ) * a ≤ ∑ x ∈ s, T x) :
    ψ₀ * (s.card : ℝ) * a^2 ≤ finiteStatistic s ψ T := by
  have hsum : (s.card : ℝ) * a^2 ≤ ∑ x ∈ s, (T x)^2 := by
    by_cases hs : s.card = 0
    · simp only [hs, Nat.cast_zero, zero_mul]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    · have hcard : 0 < (s.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
      have hj := cardinal_mul_sum_sq_ge s T
      have hma : 0 ≤ (s.card : ℝ) * a := mul_nonneg hcard.le ha
      have hsq := pow_le_pow_left₀ hma hmean 2
      nlinarith
  calc
    ψ₀ * (s.card : ℝ) * a^2 = ψ₀ * ((s.card : ℝ) * a^2) := by ring
    _ ≤ ψ₀ * (∑ x ∈ s, (T x)^2) := mul_le_mul_of_nonneg_left hsum hψ₀
    _ = ∑ x ∈ s, ψ₀ * (T x)^2 := Finset.mul_sum _ _ _
    _ ≤ finiteStatistic s ψ T := by
      exact Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_right (hψ x hx) (sq_nonneg _)

end Ostmann.Construction

end

end OAI
