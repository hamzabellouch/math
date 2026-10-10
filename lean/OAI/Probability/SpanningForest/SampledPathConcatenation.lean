import OAI.Probability.SpanningForest.SampledUnitPath
import OAI.Probability.SpanningForest.PathConcatenation

namespace OAI

noncomputable section

namespace Problem336.SampledPathConcatenation

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal
open SampledUnitPath DyadicGaussianBound

local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ, ℝ) := borel _
local instance : BorelSpace C(ℝ, ℝ) := ⟨rfl⟩

def fullPath (τ : ℕ → ℝ≥0) (ω : ℕ → ℝ) : C(ℝ, ℝ) :=
  PathConcatenation.concatPath (pathBlock τ ω)

theorem measurable_fullPath (τ : ℕ → ℝ≥0) : Measurable (fullPath τ) :=
  PathConcatenation.measurable_concatPath.comp (measurable_pathBlocks τ)

variable {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
variable (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ))
variable (idx : ℕ → ℕ → ℕ)
variable (hidx : ∀ n k, τ (idx n k) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n)
include hμ idx hidx

theorem ae_fullPath_block_grid :
    ∀ᵐ ω ∂μ, ∀ m n j : ℕ, ∀ (_ : j ≤ 2 ^ n) (t : unitInterval),
      (t : ℝ) = DyadicInterpolation.grid n j →
      fullPath τ ω ((m : ℝ) + t) = sample τ ω ((m : ℝ) + t) := by
  filter_upwards [ae_pathBlock_grid hμ idx hidx, ae_pathBlock_endpoints hμ idx hidx,
    ae_sample_zero hμ idx hidx] with ω hg he hz
  intro m n j hj t ht
  change PathConcatenation.concat (pathBlock τ ω) ((m : ℝ) + t) = _
  rw [PathConcatenation.concat_nat_add]
  have hsum : (∑ k ∈ Finset.range m,
      (pathBlock τ ω k PathConcatenation.rightEnd -
        pathBlock τ ω k PathConcatenation.leftEnd)) = sample τ ω m - sample τ ω 0 := by
    change (∑ k ∈ Finset.range m, (pathBlock τ ω k 1 - pathBlock τ ω k 0)) = _
    simp_rw [(he _).1, (he _).2]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      Finset.sum_range_sub (fun k : ℕ => sample τ ω (k : ℝ)) m
  rw [hsum, hz, sub_zero, hg m n j hj t ht]
  change sample τ ω m + (sample τ ω ((m : ℝ) + t) - pathBlock τ ω m 0) = _
  rw [(he m).1]
  ring

omit hμ idx hidx in

lemma grid_decompose (n k : ℕ) :
    ∃ (m j : ℕ) (t : unitInterval), j ≤ 2 ^ n ∧
      (t : ℝ) = DyadicInterpolation.grid n j ∧
      DyadicInterpolation.grid n k = (m : ℝ) + t := by
  let m := k / 2 ^ n
  let j := k % 2 ^ n
  have hp : 0 < 2 ^ n := by positivity
  have hj : j < 2 ^ n := Nat.mod_lt _ hp
  have hjR : (j : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hj.le
  let t : unitInterval := ⟨DyadicInterpolation.grid n j,
    ⟨by unfold DyadicInterpolation.grid; positivity,
      by unfold DyadicInterpolation.grid; exact (div_le_one (by positivity)).mpr hjR⟩⟩
  refine ⟨m, j, t, hj.le, rfl, ?_⟩
  change (k : ℝ) / (2 : ℝ) ^ n = (m : ℝ) + (j : ℝ) / (2 : ℝ) ^ n
  have hkj : j + 2 ^ n * m = k := Nat.mod_add_div k (2 ^ n)
  have hcast : (j : ℝ) + (2 : ℝ) ^ n * (m : ℝ) = k := by exact_mod_cast hkj
  apply (div_eq_iff (by positivity : (2 : ℝ) ^ n ≠ 0)).mpr
  field_simp
  nlinarith

theorem ae_fullPath_grid :
    ∀ᵐ ω ∂μ, ∀ n k : ℕ,
      fullPath τ ω (DyadicInterpolation.grid n k) =
        sample τ ω (DyadicInterpolation.grid n k) := by
  filter_upwards [ae_fullPath_block_grid hμ idx hidx] with ω hω
  intro n k
  obtain ⟨m, j, t, hj, ht, hdecomp⟩ := grid_decompose n k
  rw [hdecomp]
  exact hω m n j hj t ht

theorem ae_fullPath_coordinates :
    ∀ᵐ ω ∂μ, ∀ n k : ℕ,
      fullPath τ ω ((k : ℝ) / (2 : ℝ) ^ n) = ω (idx n k) := by
  filter_upwards [ae_fullPath_grid hμ idx hidx, ae_time_consistent hμ] with ω hg hc
  intro n k
  rw [show ((k : ℝ) / (2 : ℝ) ^ n) = DyadicInterpolation.grid n k from rfl, hg n k]
  have hs := sample_time_eq hc (idx n k)
  simpa [hidx, DyadicInterpolation.grid, NNReal.coe_div, NNReal.coe_pow] using hs

end Problem336.SampledPathConcatenation

end

end OAI
