import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.FanCoordinates

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem fanCoordinates_fixed_smooth (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P) {t s : ℝ}
    (ht : (t,s) ∈ fanDomain x P) :
    ContDiffAt ℝ ∞ (fun r => fanCoordinates x P (t,r)) s :=
  ((fanCoordinates_smooth x hP _ ht).contDiffAt ((fanDomain_open x hP).mem_nhds ht)).comp s
    (contDiffAt_const.prodMk contDiffAt_id)

 theorem fan_energy_smooth_at (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P) {t s : ℝ}
    (ht : (t,s) ∈ fanDomain x P) : ContDiffAt ℝ ∞ (fun r => ‖(P r).2‖^2) s := by
  have hq := fanCoordinates_fixed_smooth x hP ht
  have hm := (fanCoordinates_ode x P ht).1
  have hg := (metric_smooth x _ hm).contDiffAt ((chartAt (Model n) x).open_target.mem_nhds hm)
  have hs := ((hg.comp s hq.fst).clm_apply hq.snd).clm_apply hq.snd
  apply hs.congr_of_eventuallyEq
  have hn : ∀ᶠ r in 𝓝 s, (t,r) ∈ fanDomain x P :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds ((fanDomain_open x hP).mem_nhds ht)
  filter_upwards [hn] with r hr
  exact (fanCoordinates_energy x P hr).symm

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
