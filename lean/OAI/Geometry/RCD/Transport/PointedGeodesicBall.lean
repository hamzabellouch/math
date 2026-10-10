import OAI.Geometry.RCD.Transport.PointedGeodesicInterpolation
import OAI.Geometry.RCD.Harmonic.PointedRadialDistance
import OAI.Analysis.RCDHeat.DynamicalPlan

namespace OAI

/-! # Source geodesics remain asymptotically in the Euclidean endpoint ball -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_geodesic_radius_bound {n : ℕ} {p : X} {r S ρ ε : ℝ}
    (hr : 0<r) (hρ : 0≤ρ) (hε : 0≤ε) (hroom : 3*ρ≤S)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {γ : C(Time,X)} (hγ : IsGeodesic γ)
    (h0 : dist (γ 0) p≤ρ*r) (h1 : dist (γ 1) p≤ρ*r) (t : Time) :
    dist (γ t) p/r≤ρ+4*ε+Real.sqrt (2*(ε*(4*ρ+ε))) := by
  have hρS : ρ≤S := by linarith
  have hS : 0≤S := hρ.trans hρS
  have hD : dist (γ 0) (γ 1)≤2*ρ*r := by
    have hh := dist_triangle (γ 0) p (γ 1)
    rw [dist_comm p (γ 1)] at hh
    linarith
  have htD : dist (γ t) (γ 0)≤dist (γ 0) (γ 1) := by
    rw [hγ t 0]
    change |(t:ℝ)-0| *dist (γ 0) (γ 1)≤dist (γ 0) (γ 1)
    simp only [sub_zero,abs_of_nonneg t.2.1]
    exact mul_le_of_le_one_left dist_nonneg t.2.2
  have htS : dist (γ t) p≤S*r := by
    have hh := dist_triangle (γ t) (γ 0) p
    nlinarith [mul_le_mul_of_nonneg_right hroom hr.le]
  have hb (s : Time) (hs : dist (γ s) p≤ρ*r) : ‖v (γ s)‖≤ρ+2*ε := by
    have hh := (abs_le.mp (pointed_radial_distance hr hS hv
      (hs.trans (mul_le_mul_of_nonneg_right hρS hr.le)))).2
    have hd := (div_le_iff₀ hr).mpr hs
    linarith
  have ha : ‖(1-(t:ℝ)) • v (γ 0)+(t:ℝ) • v (γ 1)‖≤ρ+2*ε := by
    calc
      _ ≤ ‖(1-(t:ℝ)) • v (γ 0)‖+‖(t:ℝ) • v (γ 1)‖ := norm_add_le _ _
      _ = (1-(t:ℝ))*‖v (γ 0)‖+(t:ℝ)*‖v (γ 1)‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg t.2.1,
          abs_of_nonneg (sub_nonneg.mpr t.2.2)]
      _ ≤ (1-(t:ℝ))*(ρ+2*ε)+(t:ℝ)*(ρ+2*ε) := add_le_add
        (mul_le_mul_of_nonneg_left (hb 0 h0) (sub_nonneg.mpr t.2.2))
        (mul_le_mul_of_nonneg_left (hb 1 h1) t.2.1)
      _ = ρ+2*ε := by ring
  have he := pointed_geodesic_interpolation hr hρ hε hroom hv hγ h0 h1 t
  have ht := dist_triangle (v (γ t)) ((1-(t:ℝ)) • v (γ 0)+(t:ℝ) • v (γ 1)) 0
  simp only [dist_zero_right] at ht
  have hh := (abs_le.mp (pointed_radial_distance hr hS hv htS)).1
  linarith

variable [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem pointed_plan_inner_support {n : ℕ} {S ρ R : ℝ}
    (hρ : 0≤ρ) (hroom : 3*ρ≤S) (hρR : ρ<R)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (P : ℕ → ProbabilityMeasure C(Time,X))
    (hgeo : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), IsGeodesic γ)
    (h0 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 0) (p k)≤ρ*r k)
    (h1 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 1) (p k)≤ρ*r k) :
    ∀ᶠ k in atTop, ∀ᵐ γ ∂(P k : Measure C(Time,X)),
      ∀ t : Time, dist (γ t) (p k)≤R*r k := by
  have he : Tendsto (fun k => 4*ε k+Real.sqrt (2*(ε k*(4*ρ+ε k)))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,Real.sqrt_zero,add_zero] using
      (hεlim.const_mul 4).add (((hεlim.mul (hεlim.const_add (4*ρ))).const_mul 2).sqrt)
  filter_upwards [he.eventually (Iio_mem_nhds (sub_pos.mpr hρR))] with k hk
  filter_upwards [hgeo k,h0 k,h1 k] with γ hγ hγ0 hγ1
  intro t
  apply (div_le_iff₀ (hr k)).mp
  exact (pointed_geodesic_radius_bound (hr k) hρ (hε k) hroom (hv k) hγ hγ0 hγ1 t).trans
    (by linarith)

end RegularPointCoordinates

end

end OAI
