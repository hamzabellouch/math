import OAI.Probability.SpanningForest.DyadicPathLimit
import OAI.Probability.SpanningForest.DyadicGaussianBound
import OAI.Probability.SpanningForest.DyadicTimes

namespace OAI

noncomputable section

namespace Problem336.SampledUnitPath

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open DyadicGaussianBound

def pathBlock (τ : ℕ → ℝ≥0) (ω : ℕ → ℝ) (m : ℕ) : C(unitInterval, ℝ) :=
  DyadicPathLimit.unitPath (fun t => sample τ ω ((m : ℝ) + t))

section Measurability

variable [MeasurableSpace C(unitInterval, ℝ)] [BorelSpace C(unitInterval, ℝ)]

theorem measurable_pathBlock (τ : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (fun ω : ℕ → ℝ => pathBlock τ ω m) :=
  DyadicPathLimit.measurable_unitPath _ (fun _ => measurable_sample τ _)

theorem measurable_pathBlocks (τ : ℕ → ℝ≥0) :
    Measurable (fun ω : ℕ → ℝ => pathBlock τ ω) :=
  Measurable.of_eval (measurable_pathBlock τ)

end Measurability

lemma shift_grid (m n j : ℕ) :
    ((m * 2 ^ n + j : ℕ) : ℝ) / (2 : ℝ) ^ n =
      (m : ℝ) + DyadicInterpolation.grid n j := by
  unfold DyadicInterpolation.grid
  push_cast
  field_simp

lemma shift_grid_succ (m n j : ℕ) :
    ((m * 2 ^ n + j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n =
      (m : ℝ) + DyadicInterpolation.grid n (j + 1) := by
  rw [Nat.add_assoc]
  exact shift_grid m n (j + 1)

def bound (n : ℕ) : ℝ := SchauderTail.incrementRatio ^ (n + 1)

lemma bound_nonneg (n : ℕ) : 0 ≤ bound n :=
  pow_nonneg SchauderTail.incrementRatio_nonneg _

lemma summable_bound : Summable bound := by
  change Summable (fun n : ℕ => SchauderTail.incrementRatio ^ (n + 1))
  simpa only [pow_succ] using
    SchauderTail.summable_incrementRatio.mul_right SchauderTail.incrementRatio

variable {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
variable (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ))
variable (idx : ℕ → ℕ → ℕ)
variable (hidx : ∀ n k, τ (idx n k) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n)

include hμ idx hidx

theorem ae_block_increment_bound :
    ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ n in atTop, ∀ j < 2 ^ (n + 1),
      |sample τ ω ((m : ℝ) + DyadicInterpolation.grid (n + 1) (j + 1)) -
        sample τ ω ((m : ℝ) + DyadicInterpolation.grid (n + 1) j)| ≤ bound n := by
  filter_upwards [ae_all_sample_increment_bound hμ idx hidx] with ω hω
  intro m
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω m)
  filter_upwards [eventually_ge_atTop N] with n hn
  intro j hj
  have h := hN (n + 1) (by omega) ⟨j, hj⟩
  simpa only [shift_grid_succ, shift_grid, bound] using h

theorem ae_pathBlock_grid :
    ∀ᵐ ω ∂μ, ∀ m n j : ℕ, ∀ (_ : j ≤ 2 ^ n) (t : unitInterval),
      (t : ℝ) = DyadicInterpolation.grid n j →
      pathBlock τ ω m t = sample τ ω ((m : ℝ) + t) := by
  filter_upwards [ae_block_increment_bound hμ idx hidx] with ω hω
  intro m n j hj t ht
  exact DyadicPathLimit.unitPath_grid _ bound bound_nonneg summable_bound
    (hω m) n j hj t ht

theorem ae_sample_zero : ∀ᵐ ω ∂μ, sample τ ω 0 = 0 := by
  filter_upwards [ae_time_consistent hμ, ae_zero_coordinates hμ] with ω hc hz
  have hi : τ (idx 0 0) = 0 := by simpa using hidx 0 0
  have hs := sample_time_eq hc (idx 0 0)
  simpa [hi, hz _ hi] using hs

theorem ae_pathBlock_endpoints :
    ∀ᵐ ω ∂μ, ∀ m : ℕ,
      pathBlock τ ω m 0 = sample τ ω m ∧
      pathBlock τ ω m 1 = sample τ ω ((m : ℝ) + 1) := by
  filter_upwards [ae_pathBlock_grid hμ idx hidx] with ω hω
  intro m
  constructor
  · simpa using hω m 0 0 (by norm_num) 0 (by simp [DyadicInterpolation.grid])
  · exact hω m 0 1 (by norm_num) 1 (by simp [DyadicInterpolation.grid])

omit hμ idx hidx in

theorem ae_canonical_pathBlock_grid
    {μ : Measure (ℕ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ
      (CountableBrownian.family DyadicTimes.enumeration)) :
    ∀ᵐ ω ∂μ, ∀ m n j : ℕ, ∀ (_ : j ≤ 2 ^ n) (t : unitInterval),
      (t : ℝ) = DyadicInterpolation.grid n j →
      pathBlock DyadicTimes.enumeration ω m t =
        sample DyadicTimes.enumeration ω ((m : ℝ) + t) :=
  ae_pathBlock_grid hμ Nat.pair (by intro n k; simp [DyadicTimes.grid])

end Problem336.SampledUnitPath

end

end OAI
