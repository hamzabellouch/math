import OAI.Geometry.RCD.Transport.NearbyEndpointPlan
import OAI.Geometry.RCD.Coordinates.RegularMovingVolume

namespace OAI

/-! # Uniform normalized compression for actual nearby-endpoint plans -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)

include hX in
theorem near_regular_compression_bound (hn : 2 ≤ n) {o : X} (ho : IsRegular n o)
    (p z : ℕ → X) (R : ℕ → ℝ) (hp : Tendsto p atTop (𝓝 o))
    (hz : Tendsto z atTop (𝓝 o)) (hR : ∀ k, 0 < R k) (hR0 : Tendsto R atTop (𝓝 0))
    {A θ : ℝ} (hA : 0 < A) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k,
      (ENNReal.ofReal (segmentCost n * (R k)^n /
        ((hausdorff n X).real (ball (p k) (R k)) * (θ * R k)^n))).toReal *
          (hausdorff n X).real (ball (z k) (A * R k)) ≤ C := by
  let μ := hausdorff n X
  let f k := μ.real (ball (p k) (R k)) / (R k)^n
  let g k := μ.real (ball (z k) (A * R k)) / (A * R k)^n
  have hf : Tendsto f atTop (𝓝 (euclideanUnitVolume n)) :=
    hX.regular_moving_volume_limit hn ho p R hp hR hR0
  have hg : Tendsto g atTop (𝓝 (euclideanUnitVolume n)) :=
    hX.regular_moving_volume_limit hn ho z (fun k => A * R k) hz
      (fun k => mul_pos hA (hR k)) (by simpa using hR0.const_mul A)
  have hv (k : ℕ) : 0 < μ.real (ball (p k) (R k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (hR k)).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hcost : 0 ≤ segmentCost n := by
    dsimp only [segmentCost]
    positivity
  have he (k : ℕ) :
      (ENNReal.ofReal (segmentCost n * (R k)^n /
        (μ.real (ball (p k) (R k)) * (θ * R k)^n))).toReal *
        μ.real (ball (z k) (A * R k)) =
      (segmentCost n * A^n / θ^n) * (g k / f k) := by
    rw [ENNReal.toReal_ofReal (by
      exact div_nonneg (mul_nonneg hcost (pow_pos (hR k) n).le)
        (mul_pos (hv k) (pow_pos (mul_pos hθ (hR k)) n)).le)]
    dsimp only [f,g]
    rw [mul_pow,mul_pow]
    field_simp [hA.ne',hθ.ne',(hR k).ne',(hv k).ne']
  have hh : Tendsto (fun k =>
      (ENNReal.ofReal (segmentCost n * (R k)^n /
        (μ.real (ball (p k) (R k)) * (θ * R k)^n))).toReal *
        μ.real (ball (z k) (A * R k))) atTop
      (𝓝 ((segmentCost n * A^n / θ^n) * (euclideanUnitVolume n / euclideanUnitVolume n))) := by
    exact ((hg.div hf (euclideanUnitVolume_pos n).ne').const_mul _).congr
      (fun k => (he k).symm)
  obtain ⟨C,hC⟩ := hh.bddAbove_range
  exact ⟨max 0 C,le_max_left _ _,fun k => (hC (mem_range_self k)).trans (le_max_right _ _)⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
