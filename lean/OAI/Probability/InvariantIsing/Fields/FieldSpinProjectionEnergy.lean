import OAI.Probability.InvariantIsing.Core.FiniteWeightedCauchy
import OAI.Probability.InvariantIsing.Fields.SpinHammingEnergy

namespace OAI

/-! Energy lost by projection in a possibly unbounded external field.
The Euclidean estimate is suited to averaging under Gaussian path laws. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma fieldEnergy_projection_sq {N : ℕ} (z : Fin N → ℝ) (σ τ : Spin N) :
    (fieldEnergy z σ - fieldEnergy z τ) ^ 2 ≤
      4 * (∑ i, z i ^ 2) * (hammingDist σ τ : ℝ) := by
  have he : fieldEnergy z σ - fieldEnergy z τ =
      ∑ i, z i * (spinValue (σ i) - spinValue (τ i)) := by
    simp only [fieldEnergy, mul_sub, Finset.sum_sub_distrib]
  have hd : (∑ i, (spinValue (σ i) - spinValue (τ i)) ^ 2) =
      4 * (hammingDist σ τ : ℝ) := by
    have h := spinVector_sub_norm_sq σ τ
    rw [EuclideanSpace.real_norm_sq_eq] at h
    exact h
  rw [he]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ z
    (fun i => spinValue (σ i) - spinValue (τ i))
  rw [hd] at hc
  nlinarith

theorem fieldEnergy_projection_mean_le {N : ℕ} (z : Fin N → ℝ)
    (f : Spin N → Spin N) (p : Spin N → ℝ)
    (hp : ∀ σ, 0 ≤ p σ) (hpSum : ∑ σ, p σ = 1) :
    |∑ σ, p σ * (fieldEnergy z σ - fieldEnergy z (f σ))| ≤
      2 * Real.sqrt ((∑ i, z i ^ 2) *
        (∑ σ, p σ * (hammingDist σ (f σ) : ℝ))) := by
  have hz : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hd : 0 ≤ ∑ σ, p σ * (hammingDist σ (f σ) : ℝ) :=
    Finset.sum_nonneg (fun σ _ => mul_nonneg (hp σ) (Nat.cast_nonneg _))
  have he : (∑ σ, p σ * (fieldEnergy z σ - fieldEnergy z (f σ)) ^ 2) ≤
      4 * (∑ i, z i ^ 2) * (∑ σ, p σ * (hammingDist σ (f σ) : ℝ)) := by
    calc
      _ ≤ ∑ σ, p σ * (4 * (∑ i, z i ^ 2) * (hammingDist σ (f σ) : ℝ)) :=
        Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left
          (fieldEnergy_projection_sq z σ (f σ)) (hp σ))
      _ = _ := by
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (mul_nonneg hz hd)]
  norm_num
  exact (finite_weighted_sum_sq_le p
    (fun σ => fieldEnergy z σ - fieldEnergy z (f σ)) hp hpSum).trans (by nlinarith [he])

end InvariantIsing

end

end OAI
