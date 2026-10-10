import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.NormalDifferential
import OAI.Geometry.WeakMTW.Coordinates.LocalDistance

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold

namespace CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem quadratic_speed_eq {B : MetricTensor E} {v : ℝ → E} {w : E} {a K : ℝ}
    (hd : HasDerivAt v w a) (hzero : v a = 0)
    (he : ∀ᶠ t in 𝓝 a, B (v t) (v t) = K * (t - a) ^ 2) : B w w = K := by
  have hc : Continuous (fun z : E => B z z) := B.continuous.clm_apply continuous_id
  have hl := hc.continuousAt.tendsto.comp hd.tendsto_slope
  have he' : (fun t => B (slope v a t) (slope v a t)) =ᶠ[𝓝[≠] a] (fun _ => K) := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hta
    have hne : t - a ≠ 0 := sub_ne_zero.mpr hta
    simp only [slope, hzero, vsub_eq_sub, sub_zero, map_smul, smul_apply, smul_eq_mul]
    rw [ht]
    field_simp
  exact tendsto_nhds_unique hl (tendsto_const_nhds.congr' he'.symm)
end
end CoordinateGeometry

namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

 theorem eventually_dist_normal (x z : M) {y₀ : E}
    (N : NormalFlow (metric x) (chartAt E x).target y₀)
    (hz : z ∈ (chartAt E x).source)
    (hzero : (0 : E) ∈ (N.normalAt (chartAt E x z)).source) :
    ∀ᶠ y in 𝓝 z, dist z y = N.time * Real.sqrt (metric x (chartAt E x z)
      ((normalChart x z N).symm y) ((normalChart x z N).symm y)) := by
  let e := normalChart x z N
  have hz' : z ∈ e.target := normalChart_target_center x z N hz hzero
  have hi : e.symm z = 0 := by
    have h := e.left_inv (show (0 : E) ∈ e.source by rw [normalChart_source]; exact hzero)
    change (normalChart x z N).symm (normalChart x z N 0) = 0 at h
    rwa [normalChart_zero x z N hz hzero] at h
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hz')
  have hc : ContinuousAt (fun y => N.time * Real.sqrt (metric x (chartAt E x z)
      (e.symm y) (e.symm y))) z :=
    continuousAt_const.mul ((continuousAt_const.clm_apply
      (e.symm.continuousAt hz')).clm_apply (e.symm.continuousAt hz')).sqrt
  have hsmall : ∀ᶠ y in 𝓝 z, N.time * Real.sqrt (metric x (chartAt E x z)
      (e.symm y) (e.symm y)) < r := by
    apply hc.eventually_lt_const
    simpa [hi] using hr
  filter_upwards [e.open_target.mem_nhds hz', hsmall] with y hy hys
  have he := normal_distance_of_ball x z N hz hzero hr hrs (e.map_target hy) hys
  change dist z (e (e.symm y)) = _ at he
  rw [e.right_inv hy] at he
  exact he

 theorem coordinate_speed_of_local_distance (x : M) {c : ℝ → E} {a C : ℝ} {w : E}
    (hc : HasDerivAt c w a) (hct : c a ∈ (chartAt E x).target)
    (hC : 0 ≤ C)
    (he : ∀ᶠ t in 𝓝 a,
      dist ((chartAt E x).symm (c a)) ((chartAt E x).symm (c t)) = C * |t - a|) :
    metric x (c a) w w = C ^ 2 := by
  let z := (chartAt E x).symm (c a)
  have hz : z ∈ (chartAt E x).source := (chartAt E x).map_target hct
  have hcz : chartAt E x z = c a := (chartAt E x).right_inv hct
  obtain ⟨N⟩ := exists_normalFlow (chartAt E x).open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv) hct
  have hzero : (0 : E) ∈ (N.normalAt (c a)).source := N.center_mem
  let ν : ℝ → E := fun t => (N.normalAt (c a)).symm (c t)
  have hνd : HasDerivAt ν (N.time⁻¹ • w) a := by
    simpa only [ν, Function.comp_def, smul_apply, ContinuousLinearMap.id_apply] using
      (N.normalAt_inverse_hasFDerivAt_center (chartAt E x).open_target (metric_smooth x)
        (fun z hz v hv => metric_positive x hz hv) hzero).comp_hasDerivAt a hc
  have hν₀ : ν a = 0 := by
    have h := (N.normalAt (c a)).left_inv hzero
    simpa only [N.normalAt_zero (chartAt E x).open_target (metric_smooth x)
      (fun z hz v hv => metric_positive x hz hv) hzero] using h
  have hγc : ContinuousAt (fun t => (chartAt E x).symm (c t)) a :=
    ((chartAt E x).symm.continuousAt hct).comp hc.continuousAt
  have hn := hγc (eventually_dist_normal x z N hz (by simpa only [hcz] using hzero))
  have heq : ∀ᶠ t in 𝓝 a, metric x (c a) (ν t) (ν t) =
      (C / N.time) ^ 2 * (t - a) ^ 2 := by
    filter_upwards [he, hn, hc.continuousAt.preimage_mem_nhds
      ((chartAt E x).open_target.mem_nhds hct)] with t het hnt ht
    have hpos : 0 ≤ metric x (c a) (ν t) (ν t) := by
      by_cases hv : ν t = 0
      · simp [hv]
      · exact (metric_positive x hct hv).le
    change dist z ((chartAt E x).symm (c t)) = _ at het
    change dist z ((chartAt E x).symm (c t)) = N.time *
      Real.sqrt (metric x (chartAt E x z)
        ((N.normalAt (chartAt E x z)).symm (chartAt E x ((chartAt E x).symm (c t))))
        ((N.normalAt (chartAt E x z)).symm (chartAt E x ((chartAt E x).symm (c t))))) at hnt
    rw [hcz, (chartAt E x).right_inv ht] at hnt
    have hh : Real.sqrt (metric x (c a) (ν t) (ν t)) = C * |t - a| / N.time := by
      apply (eq_div_iff N.time_pos.ne').mpr
      nlinarith [het, hnt]
    have hs := (Real.sqrt_eq_iff_eq_sq hpos
      (div_nonneg (mul_nonneg hC (abs_nonneg _)) N.time_pos.le)).mp hh
    rw [hs]
    simp only [div_pow, mul_pow, sq_abs]
    ring
  have hq := quadratic_speed_eq hνd hν₀ heq
  simp only [map_smul, smul_apply, smul_eq_mul] at hq
  have hT := N.time_pos.ne'
  field_simp at hq
  nlinarith
end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
