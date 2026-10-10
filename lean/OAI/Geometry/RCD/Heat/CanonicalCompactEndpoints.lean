import OAI.Geometry.RCD.Heat.CanonicalCompactLogLimit

namespace OAI

/-! # The logarithmic heat-kernel limit on compact endpoint types -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_endpoint_log_limit (hK : K ≤ 0)
    {S T : Set X} (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R) :
    TendstoUniformly (fun k (q : S × T) =>
      ε k*Real.log (hX.canonicalHeatKernel hn p (ε k/4) q.1 q.2))
      (fun q => -(dist (q.1 : X) (q.2 : X))^2) atTop := by
  let inc : S × T → closedBall p R × closedBall p R := fun q =>
    (⟨q.1,by rw [mem_closedBall,dist_comm]; exact hdS q.1⟩,
     ⟨q.2,by rw [mem_closedBall,dist_comm]; exact hdT q.2⟩)
  have hh := (hX.canonicalHeatKernel_compact_log_limit hn p hK ε hε hε1 hε0 hR
    (T := (1:ℝ)/2) (by norm_num) (by norm_num)).comp inc
  convert hh using 1
  · funext k q
    dsimp only [Function.comp_def,inc]
    congr 2
    ring_nf
  · funext q
    dsimp [inc]
    ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
