import OAI.Geometry.RCD.Transport.PointedLocalGeodesic
import OAI.Analysis.RCDHeat.DynamicalPlan

namespace OAI

/-! # Local transport paths stay in the prescribed interior image ball -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_local_plan_support {n : ℕ} {S τ η R B : ℝ}
    (hτ : 0≤τ) (hτS : τ<S) (hroom : τ+2*η<S)
    (hηB : η<B) (z : Euclidean n) (hzR : ‖z‖+η<R)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (P : ℕ → ProbabilityMeasure C(Time,X))
    (hgeo : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), IsGeodesic γ)
    (h0 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 0) (p k)≤τ*r k)
    (h1 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 1) (p k)≤τ*r k)
    (hz0 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), v k (γ 0)∈closedBall z η)
    (hz1 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), v k (γ 1)∈closedBall z η) :
    ∀ᶠ k in atTop, ∀ᵐ γ ∂(P k : Measure C(Time,X)),
      ∀ t : Time, dist (γ t) (p k)≤R*r k ∧ v k (γ t)∈closedBall z B := by
  let e := fun k => Real.sqrt (2*(ε k*(4*τ+ε k)))
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,Real.sqrt_zero] using
      ((hεlim.mul (hεlim.const_add (4*τ))).const_mul 2).sqrt
  have hrad : Tendsto (fun k => e k+2*ε k) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using he.add (hεlim.const_mul 2)
  filter_upwards [hεlim.eventually (Iio_mem_nhds (sub_pos.mpr hroom)),
    he.eventually (Iio_mem_nhds (sub_pos.mpr hηB)),
    hrad.eventually (Iio_mem_nhds (sub_pos.mpr hzR))] with k hk hki hkr
  filter_upwards [hgeo k,h0 k,h1 k,hz0 k,hz1 k] with γ hγ hγ0 hγ1 hγz0 hγz1
  have hroomk : τ+2*η+ε k≤S := by linarith
  have hpoints := pointed_local_geodesic_within (hr k) hτS.le hroomk (hv k)
    hγ hγ0 hγ1 z hγz0 hγz1
  intro t
  have him := pointed_local_geodesic_image (hr k) hτ hτS.le (hε k) hroomk (hv k)
    hγ hγ0 hγ1 z hγz0 hγz1 t
  change dist (v k (γ t)) z≤η+e k at him
  have hnorm : ‖v k (γ t)‖≤η+e k+‖z‖ := by
    have ht := dist_triangle (v k (γ t)) z 0
    simp only [dist_zero_right] at ht
    linarith
  have hphysical := (abs_le.mp (pointed_radial_distance (hr k) (hτ.trans hτS.le)
    (hv k) (hpoints t))).1
  refine ⟨(div_le_iff₀ (hr k)).mp ?_,?_⟩
  · linarith
  · exact him.trans (by linarith)

end RegularPointCoordinates

end

end OAI
