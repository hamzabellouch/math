import OAI.Geometry.RCD.Heat.CanonicalCompactEndpoints

namespace OAI

/-! # The compact logarithmic kernel limit at a fixed fraction of the time -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_fraction_log_limit (hK : K ≤ 0)
    {S T : Set X} (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a:S, dist p a ≤ R) (hdT : ∀ b:T, dist p b ≤ R)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    TendstoUniformly (fun k (q : S × T) =>
      ε k*Real.log (hX.canonicalHeatKernel hn p (ε k/4*s) q.1 q.2))
      (fun q => -(dist (q.1 : X) (q.2 : X))^2/s) atTop := by
  have hz : Tendsto (fun k => ε k*s) atTop (𝓝 0) := by
    simpa only [zero_mul] using hε0.mul_const s
  have hh := hX.canonicalHeatKernel_endpoint_log_limit hn p hK (fun k => ε k*s)
    (fun k => mul_pos (hε k) hs)
    (fun k => (mul_le_mul_of_nonneg_right (hε1 k) hs.le).trans (by simpa using hs1)) hz hR hdS hdT
  let M : ℝ →L[ℝ] ℝ := s⁻¹ • ContinuousLinearMap.id ℝ ℝ
  have hscale := M.uniformContinuous.comp_tendstoUniformly hh
  convert hscale using 1
  · funext k q
    change ε k*Real.log (hX.canonicalHeatKernel hn p (ε k/4*s) q.1 q.2) =
      s⁻¹*(ε k*s*Real.log (hX.canonicalHeatKernel hn p (ε k*s/4) q.1 q.2))
    rw [show ε k*s/4=ε k/4*s by ring]
    field_simp
  · funext q
    change -(dist (q.1:X) (q.2:X))^2/s=s⁻¹*(-(dist (q.1:X) (q.2:X))^2)
    ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
