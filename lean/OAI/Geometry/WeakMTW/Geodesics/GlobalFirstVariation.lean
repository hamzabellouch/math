import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.FanCoordinates
import OAI.Geometry.WeakMTW.Geodesics.EnergyFirstVariation

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

 theorem fanMomentum_hasDerivAt {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P) (t : ℝ) :
    HasDerivAt (fanMomentum P) (deriv (fun s => ‖(P s).2‖^2) 0 / 2) t := by
  let x := geodesic (P 0) t
  let U := fanDomain x P
  let q := fanCoordinates x P
  let c : ℝ × ℝ → Model n := fun z => (q z).1
  let V : ℝ × ℝ → Model n := fun z => (q z).2
  have hU : IsOpen U := fanDomain_open x hP
  have ht : (t,0) ∈ U := (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hq : ContDiffOn ℝ ∞ q U := fanCoordinates_smooth x hP
  have hc : ContDiffOn ℝ 2 c U := hq.fst.of_le
    (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hdq := ((hq _ ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)
  have hdt := (fanCoordinates_ode x P ht).2
  have hm := (fanCoordinates_ode x P ht).1
  have hDG := ((metric_smooth x _ hm).contDiffAt
    ((chartAt (Model n) x).open_target.mem_nhds hm)).differentiableAt (by simp)
  have he : (fun s => metric x (c (t,s)) (V (t,s)) (V (t,s))) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => ‖(P s).2‖^2) := by
    have hh : ∀ᶠ s in 𝓝 (0 : ℝ), (t,s) ∈ U :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds ht)
    filter_upwards [hh] with s hs
    exact fanCoordinates_energy x P hs
  have hpair := FirstVariation.energy_pairing_hasDerivAt hU hc
    (fun z hz => (fanCoordinates_ode x P hz).2.fst) ht hdq.snd hDG
    (metric_symmetric x _) (fun v hv => metric_positive x hm hv) hdt.snd he
  apply hpair.congr_of_eventuallyEq
  have hh : ∀ᶠ r in 𝓝 t, (r,0) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds ht)
  filter_upwards [hh] with r hr
  exact fanMomentum_coord x hP hr

 theorem fanMomentum_affine {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P) (t : ℝ) :
    fanMomentum P t = fanMomentum P 0 + t * (deriv (fun s => ‖(P s).2‖^2) 0 / 2) := by
  let K := deriv (fun s => ‖(P s).2‖^2) 0 / 2
  have hd : ∀ r : ℝ, HasDerivAt (fun r => fanMomentum P r - r*K) 0 r := by
    intro r
    have hh := (fanMomentum_hasDerivAt hP r).sub ((hasDerivAt_id r).mul_const K)
    change HasDerivAt (fun r => fanMomentum P r - r*K) (K-1*K) r at hh
    simpa only [one_mul,sub_self] using hh
  have hh := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) t 0
  simp only [zero_mul,sub_zero] at hh
  exact sub_eq_iff_eq_add.mp hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
