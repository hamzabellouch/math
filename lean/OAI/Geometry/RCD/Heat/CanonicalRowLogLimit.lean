import OAI.Geometry.RCD.Heat.CanonicalAllTimeLogLimit

namespace OAI

/-! # Uniform row logarithms on a bounded endpoint support -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_row_log_limit (hK : K ≤ 0) {S : Set X}
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (hdS : ∀ a : S, dist p a ≤ R) (x : X) {t : ℝ} (ht : 0 < t) :
    TendstoUniformly (fun k (a : S) => ε k*Real.log
      (hX.canonicalHeatKernel hn p (ε k*t/2) x a))
      (fun a => -dist x (a : X)^2/(2*t)) atTop := by
  let M := max R (dist x p)
  have hM : 0 ≤ M := hR.trans (le_max_left _ _)
  let inc : S → closedBall p M × closedBall p M := fun a =>
    (⟨x,mem_closedBall.mpr (le_max_right _ _)⟩,
      ⟨a,mem_closedBall.mpr (by rw [dist_comm]; exact (hdS a).trans (le_max_left _ _))⟩)
  exact (hX.canonicalHeatKernel_compact_log_limit_allTimes hn p hK ε hε hε0 hM ht).comp inc

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
