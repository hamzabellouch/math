import OAI.MeasureTheory.Falconer.Geometry.ChartCoordinates
import OAI.MeasureTheory.Falconer.Angular.GnomonicInverse
import OAI.MeasureTheory.Falconer.Angular.GnomonicLaw

namespace OAI

/-! # Affine hyperplanes in chart coordinates come from linear spherical slabs -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {n : ℕ}

theorem coordinateJoin_one_eq_northLift (p : Space n) : coordinateJoin p 1 = northLift p := by
  rw [coordinateJoin_eq]
  rfl

theorem normalized_affine_chart_inner_le (v p : Space n) (s : ℝ) (hv : ‖v‖ = 1) :
    |inner ℝ (NormedSpace.normalize (coordinateJoin v (-s))) (gnomonicChart p : Space (n+1))| ≤
      |inner ℝ v p-s| := by
  have hn : 1 ≤ ‖coordinateJoin v (-s)‖ := by
    have hh := coordinateJoin_norm_sq v (-s)
    rw [hv] at hh
    nlinarith [norm_nonneg (coordinateJoin v (-s)),sq_nonneg s]
  have hp : 1 ≤ ‖northLift p‖ := by
    have hh := northLift_norm_sq p
    nlinarith [norm_nonneg (northLift p),sq_nonneg ‖p‖]
  have hn0 : 0 < ‖coordinateJoin v (-s)‖ := by linarith
  have hp0 : 0 < ‖northLift p‖ := by linarith
  have hni : ‖coordinateJoin v (-s)‖⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_iff₀ hn0).mpr (by simpa only [one_mul] using hn)
  have hpi : ‖northLift p‖⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_iff₀ hp0).mpr (by simpa only [one_mul] using hp)
  have hi : inner ℝ (coordinateJoin v (-s)) (northLift p) = inner ℝ v p-s := by
    rw [← coordinateJoin_one_eq_northLift,coordinateJoin_inner]
    ring
  change |inner ℝ (‖coordinateJoin v (-s)‖⁻¹ • coordinateJoin v (-s))
    (‖northLift p‖⁻¹ • northLift p)| ≤ _
  rw [inner_smul_left,inner_smul_right,conj_trivial,hi,abs_mul,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hn0.le),abs_of_nonneg (inv_nonneg.mpr hp0.le)]
  calc
    _ ≤ 1*(1*|inner ℝ v p-s|) :=
      mul_le_mul hni (mul_le_mul_of_nonneg_right hpi (abs_nonneg _))
        (by positivity) zero_le_one
    _ = _ := by ring

theorem gnomonic_affine_plate_transport (μ : Measure (Space n)) (v : Space n) (s r : ℝ)
    (hv : ‖v‖ = 1) :
    ∃ w : Sphere (n+1),
      μ {p | |inner ℝ v p-s| ≤ r} ≤
        (Measure.map gnomonicChart μ) {u | |inner ℝ (w:Space (n+1)) (u:Space (n+1))| ≤ r} := by
  have hn : coordinateJoin v (-s) ≠ 0 := by
    intro hz
    have hh := coordinateJoin_norm_sq v (-s)
    rw [hz,norm_zero,hv] at hh
    nlinarith [sq_nonneg s]
  let w : Sphere (n+1) := ⟨NormedSpace.normalize (coordinateJoin v (-s)),by
    rw [Metric.mem_sphere,dist_zero_right,norm_normalize hn]⟩
  refine ⟨w,?_⟩
  rw [Measure.map_apply (gnomonicChart_continuous n).measurable
    (measurableSet_le (by fun_prop) measurable_const)]
  apply measure_mono
  intro p hp
  exact (normalized_affine_chart_inner_le v p s hv).trans hp

theorem gnomonicCoordinates_map_affine_plate (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ (w : Sphere (n+1)) ∂ν, 0 < (w:Space (n+1)) 0)
    (v : Space n) (s r : ℝ) (hv : ‖v‖ = 1) :
    ∃ w : Sphere (n+1),
      (Measure.map gnomonicCoordinates ν) {p | |inner ℝ v p-s| ≤ r} ≤
        ν {u : Sphere (n+1) | |inner ℝ (w:Space (n+1)) (u:Space (n+1))| ≤ r} := by
  obtain ⟨w,hw⟩ := gnomonic_affine_plate_transport
    (Measure.map gnomonicCoordinates ν) v s r hv
  rw [gnomonicCoordinates_map_recover ν hν] at hw
  exact ⟨w,hw⟩

end Falconer

end OAI
