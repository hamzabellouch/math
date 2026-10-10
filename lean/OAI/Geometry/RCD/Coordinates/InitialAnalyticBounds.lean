import OAI.Geometry.RCD.Coordinates.WorkingNormalizerBound
import OAI.Geometry.RCD.Sobolev.HarmonicBochnerConstruction

namespace OAI

/-! # Fixed analytic bounds from a capped initial splitting error -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A local volume ratio and the raw initial splitting error bound any
chosen exact normalizer on a smaller working set. This applies in particular
to the root member of the all-scale normalized family. -/
theorem initial_normalizer_norm_sq_le_two (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    {p : X} {r ε C : ℝ} {w : X → Euclidean n}
    (hfirst : FirstOrderSplittingOn μ hQ p r ε u w)
    (s : Set X) (hs : MeasurableSet s) (hsub : s ⊆ ball p r)
    (hsne : μ s ≠ 0) (hsfin : μ s ≠ ∞)
    (hrne : μ (ball p r) ≠ 0) (hrfin : μ (ball p r) ≠ ∞)
    (hC : 1 ≤ C) (hε : 0 ≤ ε)
    (hratio : μ.real (ball p r) ≤ C * μ.real s)
    (hsmall : (n : ℝ) ^ 2 * (C * ε) ≤ 1 / 2)
    (A : Euclidean n ≃L[ℝ] Euclidean n)
    (hA : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u) s hs A) :
    ‖(A : Euclidean n →L[ℝ] Euclidean n)‖ ^ 2 ≤ 2 := by
  apply normalizer_norm_sq_le_two_of_sub_id μ hQ _ s hs A hA
  exact (meanGram_sub_id_norm_le_of_subset μ hQ u hs hsub hsne hsfin hrne hrfin
    (zero_le_one.trans hC) hε hratio hfirst.gram).trans hsmall

/-- Capping the initial error by one gives a fixed all-direction gradient
bound, independent of the eventual normalized splitting tolerance. -/
theorem splittingDirectionBound_sq_le {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ((splittingDirectionBound n ε hε : ℝ≥0) : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
  have h : (n : ℝ) * (1 + ε) ≤ 2 * n := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  change ((n : ℝ) * (1 + ε)) ^ 2 ≤ _
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (show 0 ≤ 1 + ε by linarith)]

omit [BorelSpace X] [ProperSpace X] in
/-- The common half-error volume regime bounds the loss from the initial
ball to the smaller root ball by a fixed dimensional factor. -/
theorem initial_working_volume_ratio (μ : Measure X) (n : ℕ) (p q : X)
    {T omega : ℝ} (hT : 0 < T) (homega : 0 < omega)
    (hlarge : |μ.real (ball p (2 * T)) / (omega * (2 * T) ^ n) - 1| ≤ 1 / 2)
    (hsmall : |μ.real (ball q (T / 16)) / (omega * (T / 16) ^ n) - 1| ≤ 1 / 2) :
    μ.real (ball p (2 * T)) ≤ (3 * (32 : ℝ) ^ n) * μ.real (ball q (T / 16)) := by
  have hup : μ.real (ball p (2 * T)) ≤ (3 / 2 : ℝ) * (omega * (2 * T) ^ n) := by
    apply (div_le_iff₀ (by positivity : 0 < omega * (2 * T) ^ n)).mp
    linarith [(abs_le.mp hlarge).2]
  have hlo : (1 / 2 : ℝ) * (omega * (T / 16) ^ n) ≤ μ.real (ball q (T / 16)) := by
    apply (le_div_iff₀ (by positivity : 0 < omega * (T / 16) ^ n)).mp
    linarith [(abs_le.mp hsmall).1]
  calc
    _ ≤ (3 / 2 : ℝ) * (omega * (2 * T) ^ n) := hup
    _ = (3 * (32 : ℝ) ^ n) * ((1 / 2 : ℝ) * (omega * (T / 16) ^ n)) := by
      rw [show 2 * T = 32 * (T / 16) by ring, mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)

end RegularPointCoordinates

end

end OAI
