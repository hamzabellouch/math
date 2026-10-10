import OAI.Analysis.CircleDomains.Topology.SphereChartInverseControl
import OAI.Analysis.CircleDomains.Sobolev.SphericalAreaLocalization
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace OAI

/-! Quadratic local area growth for the fixed physical sphere metric, at
finite points. This compares its actual chart with the area chart. -/

open Set Filter Function Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem sphericalArea_singleton (p : Sphere) : sphericalArea {p} = 0 := by
  rw [sphericalArea, Measure.map_apply OnePoint.continuous_coe.measurable
    (measurableSet_singleton p)]
  cases p using OnePoint.rec with
  | infty => simp
  | coe z =>
    have he : ((↑) : ℂ → Sphere) ⁻¹' {(z : Sphere)} = {z} := by
      ext w
      simp
    rw [he]
    exact withDensity_absolutelyContinuous volume _ (measure_singleton z)

theorem sphericalAreaDensity_le_four (z : ℂ) : sphericalAreaDensity z ≤ 4 := by
  rw [sphericalAreaDensity, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ ^ 2)]

theorem exists_small_spherical_ball_area_bound (z : ℂ) :
    ∃ (R : ℝ), 0 < R ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ r : ℝ≥0, (r : ℝ) < R →
        sphericalArea (ball (z : Sphere) r) ≤ K * (r : ℝ≥0∞) ^ 2 := by
  obtain ⟨L, W, hW, hL⟩ := finite_sphere_chart_inverse_control z
  have hc : Continuous (fun p : Sphere => (roundSphereEquiv p : RoundAmbient)) :=
    continuous_subtype_val.comp roundSphereEquiv.continuous
  obtain ⟨R, hR, hRW⟩ := Metric.mem_nhds_iff.mp (hc.continuousAt.preimage_mem_nhds hW)
  let K : ℝ≥0∞ := 4 * (↑(L + 1) : ℝ≥0∞) ^ 2 * NNReal.pi
  refine ⟨R, hR, K, by dsimp [K]; finiteness, ?_⟩
  intro r hr
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' ball (z : Sphere) r
  have hAB : A ⊆ closedBall z ((L + 1 : ℝ≥0) * r) := by
    intro w hw
    have hwR : (w : Sphere) ∈ ball (z : Sphere) R :=
      (ball_subset_ball hr.le) hw
    have hb := hL w (hRW hwR)
    have hd : dist (w : Sphere) (z : Sphere) < r := hw
    change dist w z ≤ (L + 1 : ℝ≥0) * r
    calc
      dist w z ≤ L * dist (w : Sphere) (z : Sphere) := hb
      _ ≤ L * r := mul_le_mul_of_nonneg_left hd.le L.coe_nonneg
      _ ≤ (L + 1 : ℝ≥0) * r :=
        mul_le_mul_of_nonneg_right (by simp) r.coe_nonneg
  rw [sphericalArea, Measure.map_apply OnePoint.continuous_coe.measurable measurableSet_ball,
    withDensity_apply _ (OnePoint.continuous_coe.measurable measurableSet_ball)]
  calc
    _ ≤ ∫⁻ _ in A, (4 : ℝ≥0∞) := by
      apply lintegral_mono
      intro w
      exact (ENNReal.ofReal_le_ofReal (sphericalAreaDensity_le_four w)).trans_eq (by norm_num)
    _ = 4 * volume A := by simp
    _ ≤ 4 * volume (closedBall z ((L + 1 : ℝ≥0) * r)) :=
      mul_le_mul' le_rfl (measure_mono hAB)
    _ = K * (r : ℝ≥0∞) ^ 2 := by
      rw [Complex.volume_closedBall]
      rw [show ENNReal.ofReal ((L + 1 : ℝ≥0) * r) =
        (↑(L + 1) : ℝ≥0∞) * ↑r from by
          rw [← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul], mul_pow]
      dsimp [K]
      ring

end CircleDomainRigidity

end

end OAI
