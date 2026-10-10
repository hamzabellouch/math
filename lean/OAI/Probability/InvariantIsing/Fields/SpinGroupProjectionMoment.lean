import OAI.Probability.InvariantIsing.Fields.SpinGroupProjection
import OAI.Probability.InvariantIsing.Core.FiniteWeightedCauchy

namespace OAI

/-! The expected number of flips in the nearest group-slice projection.
The input consists of ordinary count variances, which can be checked
under the independent canonical site law. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cast_nat_distance_eq_abs (a b : ℕ) :
    (((a - b) + (b - a) : ℕ) : ℝ) = |(a : ℝ) - b| := by
  by_cases h : b ≤ a
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
  · have h' : a ≤ b := (Nat.le_of_not_ge h)
    rw [Nat.sub_eq_zero_of_le h', zero_add, Nat.cast_sub h',
      abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h'))]
    ring

lemma spinGroupProjection_distance_real {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (σ : Spin N) :
    (hammingDist σ (spinGroupProjection group k hk σ) : ℝ) =
      ∑ a, |(spinGroupCount group σ a : ℝ) - k a| := by
  rw [spinGroupProjection_distance, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact cast_nat_distance_eq_abs _ _

theorem spinGroupProjection_expected_distance {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (p : Spin N → ℝ)
    (hp : ∀ σ, 0 ≤ p σ) (hpSum : ∑ σ, p σ = 1) :
    (∑ σ, p σ * (hammingDist σ (spinGroupProjection group k hk σ) : ℝ)) ≤
      ∑ a, Real.sqrt (∑ σ, p σ * ((spinGroupCount group σ a : ℝ) - k a) ^ 2) := by
  simp_rw [spinGroupProjection_distance_real, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  have hnonneg : 0 ≤ ∑ σ, p σ * |(spinGroupCount group σ a : ℝ) - k a| :=
    Finset.sum_nonneg (fun σ _ => mul_nonneg (hp σ) (abs_nonneg _))
  have he := finite_weighted_sum_abs_le_sqrt p
    (fun σ => |(spinGroupCount group σ a : ℝ) - k a|) hp hpSum
  simpa only [abs_of_nonneg hnonneg, sq_abs] using he

theorem spinGroupProjection_expected_distance_le {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (p : Spin N → ℝ)
    (hp : ∀ σ, 0 ≤ p σ) (hpSum : ∑ σ, p σ = 1) (V : A → ℝ)
    (hV : ∀ a, (∑ σ, p σ * ((spinGroupCount group σ a : ℝ) - k a) ^ 2) ≤ V a) :
    (∑ σ, p σ * (hammingDist σ (spinGroupProjection group k hk σ) : ℝ)) ≤
      ∑ a, Real.sqrt (V a) :=
  (spinGroupProjection_expected_distance group k hk p hp hpSum).trans
    (Finset.sum_le_sum (fun a _ => Real.sqrt_le_sqrt (hV a)))

end InvariantIsing

end

end OAI
