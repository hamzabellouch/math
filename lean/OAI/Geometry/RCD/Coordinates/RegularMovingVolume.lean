import OAI.Geometry.RCD.Coordinates.RegularVolumeConvergence
import OAI.Geometry.RCD.Metric.PointedCompactness
import OAI.Geometry.RCD.Metric.ModelVolumeComparison
import OAI.Geometry.RCD.Metric.VolumeDensity

namespace OAI

/-! # Absolute volume limits at moving centers near a regular point

The single all-center neighborhood obtained from Bishop--Gromov suffices for
arbitrary centers tending to the regular point and arbitrary shrinking radii.
-/

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

theorem regular_moving_volume_limit {μ : Measure X} (m : ℕ) {p : X} {a ω : ℝ}
    (ha : 0≤a) (hω : 0<ω)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m+1) p)
    (hvolume : EuclideanRescalingVolumeConvergence μ (m+1) p ω)
    (hBG : BallVolumeComparison μ (comparisonModelVolume m a))
    (hdensity : ∀ y, SmallScaleVolumeUpper μ (comparisonModelVolume m a) y ω)
    (hfinite : ∀ y r, μ (ball y r)≠∞)
    (q : ℕ → X) (r : ℕ → ℝ) (hq : Tendsto q atTop (𝓝 p))
    (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => μ.real (ball (q k) (r k))/(r k)^(m+1)) atTop (𝓝 ω) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := min 1 (ε/(2*ω))
  have hη : 0<η := lt_min zero_lt_one (div_pos hε (by positivity))
  obtain ⟨D,hD,-,hvol⟩ := exists_uniform_volume_neighborhood m ha hω hη
    (min_le_left _ _) zero_lt_one hcompact hregular hvolume hBG hdensity hfinite
  have hqc : ∀ᶠ k in atTop, dist p (q k)<D := by
    have hh := hq.eventually (ball_mem_nhds p hD)
    simpa only [mem_ball,dist_comm] using hh
  have hrc : ∀ᶠ k in atTop, r k<D := hr0.eventually (gt_mem_nhds hD)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hqc.and hrc)
  refine ⟨N,?_⟩
  intro k hk
  have hv := hvol (q k) (hN k hk).1.le (r k) (hr k) (hN k hk).2.le
  have hid : μ.real (ball (q k) (r k))/(r k)^(m+1)-ω=
      ω*(μ.real (ball (q k) (r k))/(ω*(r k)^(m+1))-1) := by
    field_simp [hω.ne', (pow_pos (hr k) (m+1)).ne']
  rw [Real.dist_eq,hid,abs_mul,abs_of_pos hω]
  have hηε := min_le_right (1:ℝ) (ε/(2*ω))
  have hh := (le_div_iff₀ (by positivity : 0<2*ω)).mp hηε
  have hh' := mul_le_mul_of_nonneg_left hv hω.le
  change η*(2*ω)≤ε at hh
  nlinarith

variable [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_moving_volume_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {p : X} (hp : IsRegular n p)
    (q : ℕ → X) (r : ℕ → ℝ) (hq : Tendsto q atTop (𝓝 p))
    (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => (hausdorff n X).real (ball (q k) (r k))/(r k)^n)
      atTop (𝓝 (euclideanUnitVolume n)) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
  obtain ⟨a,ha,hBG⟩ := hX.exists_model_ballVolumeComparison hn
  exact RegularPointCoordinates.regular_moving_volume_limit m ha (euclideanUnitVolume_pos (m+1))
    (hX.pointedRescalingPrecompactness hn p) hp (hX.regular_volume_convergence hn hp)
    hBG (hX.smallScaleVolumeUpper hn ha)
    (fun y r => (hX.finiteOnBounded (ball y r) isBounded_ball).ne)
    q r hq hr hr0

end RegularPointCoordinates

end

end OAI
