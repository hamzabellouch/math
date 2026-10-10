import OAI.Probability.SwitchChain.FixedBlockMarginal

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteVariance

open FixedBlockMarginal (average)

variable {X I : Type*} [Fintype X] [Fintype I]

def variance (f : X → ℝ) : ℝ := average (fun x => (f x - average f) ^ 2)

theorem average_add (f g : X → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp only [average, Finset.sum_add_distrib, add_div]

theorem average_sub (f g : X → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp only [average, Finset.sum_sub_distrib, sub_div]

theorem average_mul (c : ℝ) (f : X → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : I → X → ℝ) :
    average (fun x => ∑ i, f i x) = ∑ i, average (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

theorem variance_eq [Nonempty X] (f : X → ℝ) :
    variance f = average (fun x => (f x) ^ 2) - (average f) ^ 2 := by
  have heq : (fun x => (f x - average f) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * average f) * f x + (average f) ^ 2) := by
    funext x
    ring
  rw [variance, heq, average_add, average_sub, average_mul,
    FixedBlockMarginal.average_const]
  ring

theorem average_center [Nonempty X] (f : X → ℝ) :
    average (fun x => f x - average f) = 0 := by
  rw [average_sub, FixedBlockMarginal.average_const, sub_self]

theorem variance_equiv {Y : Type*} [Fintype Y] (e : X ≃ Y) (f : Y → ℝ) :
    variance (fun x => f (e x)) = variance f := by
  unfold variance
  rw [FixedBlockMarginal.average_equiv]
  exact FixedBlockMarginal.average_equiv e (fun y => (f y - average f) ^ 2)

theorem mixture_variance {K : Type*} [Fintype K]
    (Y : K → Type*) [∀ k, Fintype (Y k)] [∀ k, Nonempty (Y k)]
    (p : K → ℝ) (f : ∀ k, Y k → ℝ) :
    (∑ k, p k * average (fun y => (f k y - ∑ l, p l * average (f l)) ^ 2)) =
      (∑ k, p k * variance (f k)) +
      ∑ k, p k * (average (f k) - ∑ l, p l * average (f l)) ^ 2 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [variance_eq]
  have heq : (fun y => (f k y - ∑ l, p l * average (f l)) ^ 2) =
      (fun y => (f k y) ^ 2 - (2 * ∑ l, p l * average (f l)) * f k y +
        (∑ l, p l * average (f l)) ^ 2) := by
    funext y
    ring
  rw [heq, average_add, average_sub, average_mul, FixedBlockMarginal.average_const]
  ring

theorem mixture_centered_row_bound {K : Type*} [Fintype K]
    (Y : K → Type*) [∀ k, Fintype (Y k)] [∀ k, Nonempty (Y k)]
    (p : K → ℝ) (hp : ∀ k, 0 ≤ p k)
    (f : I → ∀ k, Y k → ℝ)
    (hfixed : ∀ k, variance (fun y => ∑ i, f i k y) ≤
      2 * ∑ i, variance (f i k))
    (hmean : (∑ k, p k * (∑ i, average (f i k)) ^ 2) ≤
      2 * ∑ i, ∑ k, p k * (average (f i k)) ^ 2) :
    (∑ k, p k * average (fun y => (∑ i, f i k y) ^ 2)) ≤
      2 * ∑ i, ∑ k, p k * average (fun y => (f i k y) ^ 2) := by
  have hfixed' (k : K) := hfixed k
  simp_rw [variance_eq, average_sum] at hfixed'
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hfixed' k) (hp k))
  simp only [mul_sub, Finset.sum_sub_distrib] at hs
  have hrew (q : I → K → ℝ) :
      (∑ k, p k * (2 * ∑ i, q i k)) = 2 * ∑ i, ∑ k, p k * q i k := by
    calc
      _ = ∑ k, 2 * (∑ i, p k * q i k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Finset.mul_sum]
        ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hrew, hrew] at hs
  linarith

end Problem315.FiniteVariance

end

end OAI
