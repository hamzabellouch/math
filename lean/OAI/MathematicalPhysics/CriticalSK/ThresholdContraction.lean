import OAI.MathematicalPhysics.CriticalSK.Main

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
namespace CriticalSK

section ThresholdComparison
variable {ι : Type*} [Fintype ι]

lemma kernel_centered_l1_bound {K : Matrix ι ι ℝ} {μ p : ι → ℝ} {c : ℝ}
    (hmass : ∑ x, p x = ∑ x, μ x)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y)
    (hbound : ∀ x, ∑ y, |K x y - μ y| ≤ c) :
    (∑ y, |(∑ x, p x * K x y) - μ y|) ≤ c * ∑ x, |p x - μ x| := by
  have hid (y : ι) : (∑ x, p x * K x y) - μ y =
      ∑ x, (p x - μ x) * (K x y - μ y) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hstat, hmass]
    ring
  simp_rw [hid]
  calc
    _ ≤ ∑ y, ∑ x, |(p x - μ x) * (K x y - μ y)| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ x, |p x - μ x| * ∑ y, |K x y - μ y| := by
      simp_rw [abs_mul]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ x, |p x - μ x| * c :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

variable [DecidableEq ι]

lemma kernel_power_tv_bound {K : Matrix ι ι ℝ} {μ : ι → ℝ} {c : ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hμ : ∀ y, 0 ≤ μ y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hmass : ∑ y, μ y = 1)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y)
    (hc : 0 ≤ c) (hbound : ∀ x, (1 / 2 : ℝ) * ∑ y, |K x y - μ y| ≤ c / 2)
    (k : ℕ) (x : ι) :
    (1 / 2 : ℝ) * ∑ y, |(K ^ k) x y - μ y| ≤ c ^ k := by
  have hb : ∀ z, ∑ y, |K z y - μ y| ≤ c := fun z => by linarith [hbound z]
  have hpow : ∀ k : ℕ, ∀ z, ∑ y, |(K ^ k) z y - μ y| ≤ 2 * c ^ k := by
    intro k
    induction k with
    | zero =>
      intro z
      simpa using kernel_row_l1_le_two (K := K ^ 0)
        (kernel_pow_nonneg hK 0) hμ (kernel_pow_sum hrow 0) hmass z
    | succ k ih =>
      intro z
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      calc
        _ ≤ c * ∑ y, |(K ^ k) z y - μ y| :=
          kernel_centered_l1_bound ((kernel_pow_sum hrow k z).trans hmass.symm) hstat hb
        _ ≤ c * (2 * c ^ k) := mul_le_mul_of_nonneg_left (ih z) hc
        _ = 2 * c ^ (k + 1) := by rw [pow_succ]; ring
  linarith [hpow k x]

end ThresholdComparison

end CriticalSK
end

end OAI
