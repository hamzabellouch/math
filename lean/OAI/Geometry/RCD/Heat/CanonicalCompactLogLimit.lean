import OAI.Geometry.RCD.Heat.CanonicalCompactLogLower
import OAI.Geometry.RCD.Heat.CanonicalCompactLogUpper

namespace OAI

/-! # Uniform logarithmic small-noise limit of the actual heat kernel

On any fixed bounded ball, the kernel at time ε*T/2 has scaled logarithm
converging uniformly to -dist²/(2*T). Both estimates are proved for the
same canonical RCD kernel; no heat-kernel asymptotic is assumed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_compact_log_limit (hK : K ≤ 0)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T) (hT1 : T < 1) :
    TendstoUniformly (fun k (q : closedBall p R × closedBall p R) =>
      ε k*Real.log (hX.canonicalHeatKernel hn p (ε k*T/2) q.1 q.2))
      (fun q => -(dist (q.1 : X) (q.2 : X))^2/(2*T)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro η hη
  have hl := hX.canonicalHeatKernel_compact_log_lower hn p hK ε hε hε1 hε0
    (isCompact_closedBall p R) (isCompact_closedBall p R) hT hT1 (half_pos hη)
  have hu := hX.canonicalHeatKernel_bounded_log_upper hn p ε hε hε1 hε0 hR hT hT1 (half_pos hη)
  filter_upwards [hl,hu] with k hkl hku
  intro q
  have hl' := hkl q.1 q.1.property q.2 q.2.property
  have hu' := hku q.1 q.1.property q.2 q.2.property
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
