import OAI.Geometry.RCD.Heat.CompactHeatInterpolationMean
import OAI.Geometry.RCD.Heat.CompactHeatInterpolationLaws
import OAI.Geometry.RCD.Coordinates.KernelHeatBoundedRegularity

namespace OAI

/-! # Limits of actual heat means from the prescribed law limit -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem interpolationMean_law_limit (i : ℕ → ℕ) (t : Ioo (0 : ℝ) 1)
    (Q₀ : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (i k) t) atTop (𝓝 Q₀))
    (H : X →ᵇ ℝ) :
    Tendsto (fun k => D.interpolationMean H (i k) t) atTop
      (𝓝 (∫ x, H x ∂(Q₀ : Measure X))) := by
  have hh := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) H
  apply hh.congr'
  exact Eventually.of_forall fun k => by
    change (∫ x, H x ∂(D.interpolationLaw (i k) t : Measure X)) =
      D.interpolationMean H (i k) t
    rw [D.interpolationLaw_integral,D.interpolationMean_eq_density]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

theorem heat_interpolationMean_law_limit (i : ℕ → ℕ) (t : Ioo (0 : ℝ) 1)
    (Q₀ : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (i k) t) atTop (𝓝 Q₀))
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a) :
    let H := kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) a f
    Tendsto (fun k => D.interpolationMean H (i k) t) atTop
      (𝓝 (∫ x, H x ∂(Q₀ : Measure X))) := by
  intro H
  obtain ⟨hLip,hBound⟩ := hX.kernelHeat_bounded_regularity hn p
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) f A hf a ha
  let Hb : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup H hLip.continuous A
    (fun x => by simpa only [Real.norm_eq_abs] using hBound x)
  exact D.interpolationMean_law_limit i t Q₀ hweak Hb

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
