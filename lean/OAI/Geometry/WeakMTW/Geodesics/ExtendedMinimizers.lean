import Mathlib
import OAI.Geometry.WeakMTW.Variations.BrokenActionMinimum
import OAI.Geometry.WeakMTW.Geodesics.FiberSmooth
import OAI.Geometry.WeakMTW.Geodesics.ShortFan
import OAI.Geometry.WeakMTW.Geodesics.GaussChartFan
import OAI.Geometry.WeakMTW.Geodesics.FanEnergySmooth
import OAI.Geometry.WeakMTW.Variations.MomentumSeparation
import OAI.Geometry.WeakMTW.Geodesics.FlowVariationInjective

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem minimizing_fan_zero_endpoint_zero_state (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P)
    (b : M) (hbase : ∀ s, (P s).1 = b) {L : ℝ} (hL : 1 < L)
    (hmin : dist b (geodesic (P 0) L) = L*‖(P 0).2‖)
    (hx : (1,0) ∈ fanDomain x P)
    (hc : HasDerivAt (fun s => (fanCoordinates x P (1,s)).1) 0 0) :
    HasDerivAt (fun s => fanCoordinates x P (1,s)) 0 0 := by
  obtain ⟨ε,hε,hεk,hsh,hZ⟩ := short_fan_bridge x hP hx (lt_min zero_lt_one (sub_pos.mpr hL))
  have hε₁ : ε < 1 := lt_of_lt_of_le hεk (min_le_left _ _)
  have hεL : 1+ε ≤ L := by have := lt_of_lt_of_le hεk (min_le_right _ _); linarith
  have ha : (1-ε,0) ∈ fanDomain x P := hsh.self_of_nhds.1
  have hS := hsh.self_of_nhds.2.2
  have heq : ∀ s : ℝ, (1-ε,s) ∈ fanDomain x P →
      flowCoordinates x ε (fanCoordinates x P (1-ε,s)) = fanCoordinates x P (1,s) := by
    intro s hs
    rw [flowCoordinates_fan x P hs]
    congr 1
    exact Prod.ext (by dsimp; ring) rfl
  have hzeq : flowCoordinates x ε (fanCoordinates x P (1,0)) = fanCoordinates x P (1+ε,0) := by
    rw [flowCoordinates_fan x P hx,add_comm ε 1]
  have hz : (1+ε,0) ∈ fanDomain x P := by
    have hh := hZ.2.1
    have hhx : geodesicFlow 1 (P 0) ∈ (stateChart x).source := hx
    change geodesicFlow ε ((stateChart x).symm (stateChart x (geodesicFlow 1 (P 0)))) ∈ _ at hh
    rw [(stateChart x).left_inv hhx,← geodesicFlow_add,add_comm ε 1] at hh
    exact hh
  have hK : ContDiffAt ℝ ∞ (chartCost x)
      ((fanCoordinates x P (1-ε,0)).1,(fanCoordinates x P (1,0)).1) := by
    simpa only [heq 0 ha] using hS.2.2.1
  have hZ' : ContDiffAt ℝ ∞ (chartCost x)
      ((fanCoordinates x P (1,0)).1,(fanCoordinates x P (1+ε,0)).1) := by
    simpa only [hzeq] using hZ.2.2.1
  have hm : dist b (geodesic (P 0) (1+ε)) = (1+ε)*‖(P 0).2‖ := by
    have hh := minimizing_segment_dist (P 0) (L := L) (a := 0) (b := 1+ε)
      (by simpa only [hbase] using hmin) le_rfl (by linarith) hεL
    simpa only [geodesic_zero,hbase,sub_zero] using hh
  have hlocal := brokenAction_minimum x hP b hbase hε hε₁ hm ha hx hz
  let c : ℝ → Model n := fun s => (fanCoordinates x P (1,s)).1
  let V : ℝ → Model n := fun s => (fanCoordinates x P (1,s)).2
  let a : ℝ → Model n := fun s => (fanCoordinates x P (1-ε,s)).1
  let p : ℝ → Model n →L[ℝ] ℝ := fun s => metric x (c s) (V s)
  let A : ℝ → Model n →L[ℝ] ℝ := fun s =>
    metric x (a s) (fanCoordinates x P (1-ε,s)).2
  have hq := fanCoordinates_fixed_smooth x hP hx
  have hqa := fanCoordinates_fixed_smooth x hP ha
  have hgt := (fanCoordinates_ode x P hx).1
  have hg : DifferentiableAt ℝ (metric x) (c 0) :=
    ((metric_smooth x _ hgt).contDiffAt ((chartAt (Model n) x).open_target.mem_nhds hgt)).differentiableAt (by simp)
  have hv : HasDerivAt V (deriv V 0) 0 := (hq.snd.differentiableAt (by simp)).hasDerivAt
  have hp : HasDerivAt p (metric x (c 0) (deriv V 0)) 0 := momentum_hasDerivAt_zero_base hg hc hv
  have hps := brokenAction_null_momentum (A := A) hε.ne' (fan_energy_smooth_at x hP hx) hqa.fst hc hp hK hZ' hlocal
  have hshort : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ w : Model n × Model n,
      fderiv ℝ (chartCost x) (a s,c s) w = ε*(p s w.2-A s w.1) := by
    filter_upwards [hsh] with s hs
    have hh := hs.2.2.2.2.2
    rw [heq s hs.1] at hh
    exact hh
  have hgauss : ∀ᶠ s in 𝓝 (0 : ℝ), A s (deriv a s) = (1-ε)/2*deriv (fun r => ‖(P r).2‖^2) s := by
    filter_upwards [hsh] with s hs
    have hh := gauss_chart_fan x hP b hbase (1-ε) s hs.1
    change A s (deriv a s) = (1-ε)*(deriv (fun r => ‖(P r).2‖^2) s/2) at hh
    nlinarith only [hh]
  have hpzero := hps hshort hgauss
  have hVzero : deriv V 0 = 0 := zero_momentum_zero_velocity hg
    (fun w hw => metric_positive x hgt hw) hc hv (hpzero ▸ hp)
  have hv0 : HasDerivAt V 0 0 := hVzero ▸ hv
  simpa only [← Prod.zero_eq_mk] using hc.prodMk hv0

 theorem radial_interior_no_focal_fan (b : M) (v w : TangentSpace (model n) b)
    (hv : v ∈ injectivityDomain b) (x : M)
    (hx : exp b v ∈ (chartAt (Model n) x).source)
    (hd : HasDerivAt (fun s : ℝ => chartAt (Model n) x (exp b (v+s•w))) 0 0) : w = 0 := by
  let P : ℝ → TangentBundle (model n) M := fun s => ⟨b,v+s•w⟩
  have hP := vertical_fan_smooth b v w
  have hp₀ : P 0 = (⟨b,v⟩ : TangentBundle (model n) M) := by
    simp only [P, zero_smul, add_zero]
  have hbase : ∀ s, (P s).1 = b := fun _ => rfl
  obtain ⟨L,hL,he⟩ := injectivity_extended_minimizer hv
  have hmin : dist b (geodesic (P 0) L) = L*‖(P 0).2‖ := by simpa [P] using he
  have hx' : (1,0) ∈ fanDomain x P := by
    apply (stateChart_source x _).mpr
    change geodesic (P 0) 1 ∈ (chartAt (Model n) x).source
    simpa only [hp₀,← exp_eq_geodesic] using hx
  have hc : HasDerivAt (fun s => (fanCoordinates x P (1,s)).1) 0 0 := by
    convert hd using 1
    funext s
    change chartAt (Model n) x (geodesic (P s) 1) = _
    rw [← exp_eq_geodesic]
  have hstate := minimizing_fan_zero_endpoint_zero_state x hP b hbase hL hmin hx' hc
  have hb : P 0 ∈ (stateChart b).source := by
    apply (stateChart_source b _).mpr
    exact mem_chart_source (Model n) b
  exact vertical_zero_state_derivative b v w (fan_zero_state_derivative x b hP hx' hb hstate)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
