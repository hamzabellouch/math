import OAI.MathematicalPhysics.Boltzmann.Branching.RadialReflectionChangeVariables
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityFourierMultiplier

namespace OAI

section

/-! # A measurable direction map with an arbitrary value at zero -/

noncomputable section
open MeasureTheory Set

namespace BoltzmannNonuniqueness

def sphereDirection (e : Sphere) (x : Velocity) : Sphere :=
  if hx : x = 0 then e else
    ⟨NormedSpace.normalize x,mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx)⟩

theorem sphereDirection_measurable (e : Sphere) : Measurable (sphereDirection e) := by
  apply Measurable.subtype_mk
  change Measurable (fun x => (sphereDirection e x).1)
  have he : (fun x => (sphereDirection e x).1) =
      fun x : Velocity => if x = 0 then e.1 else ‖x‖⁻¹ • x := by
    funext x
    simp only [sphereDirection,NormedSpace.normalize]
    split <;> rfl
  rw [he]
  exact measurable_const.ite (measurableSet_singleton 0) (measurable_norm.inv.smul measurable_id)

theorem sphereDirection_smul (e n : Sphere) {r : ℝ} (hr : 0 < r) :
    sphereDirection e (r • n.1) = n := by
  have hn : n.1 ≠ 0 := by
    intro h
    have := mem_sphere_zero_iff_norm.mp n.property
    rw [h,norm_zero] at this
    norm_num at this
  have h : r • n.1 ≠ 0 := smul_ne_zero hr.ne' hn
  apply Subtype.ext
  simp only [sphereDirection,dite_eq_right h,NormedSpace.normalize,norm_smul,
    Real.norm_eq_abs,abs_of_pos hr,mem_sphere_zero_iff_norm.mp n.property,mul_one,smul_smul,
    inv_mul_cancel₀ hr.ne',one_smul]

theorem sphereDirection_radialReflection (e n : Sphere) {r : ℝ} (hr : 0 < r) :
    sphereDirection e (radialReflection e (r • n.1)) = normalReflection e n := by
  rw [radialReflection_sphere]
  exact sphereDirection_smul e _ (sq_pos_of_pos hr)

end BoltzmannNonuniqueness

end

end

section

/-! # Lifting sphere tests to the unit velocity ball -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

def sphereBallLift (e : Sphere) (f : Sphere → ℝ≥0∞) (x : Velocity) : ℝ≥0∞ :=
  if ‖x‖ < 1 then f (sphereDirection e x) else 0

theorem sphereBallLift_measurable (e : Sphere) {f : Sphere → ℝ≥0∞} (hf : Measurable f) :
    Measurable (sphereBallLift e f) := by
  exact (hf.comp (sphereDirection_measurable e)).ite
    (measurableSet_lt measurable_norm measurable_const) measurable_const

theorem sphereBallLift_radial (e n : Sphere) (f : Sphere → ℝ≥0∞)
    (r : Ioi (0:ℝ)) :
    sphereBallLift e f ((r:ℝ) • n.1) = if (r:ℝ) < 1 then f n else 0 := by
  rw [sphereBallLift,sphereDirection_smul e n r.property,norm_smul,
    Real.norm_eq_abs,abs_of_pos r.property,mem_sphere_zero_iff_norm.mp n.property,mul_one]

theorem sphereBallLift_integral (e : Sphere) {f : Sphere → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, sphereBallLift e f x) = (3:ℝ≥0∞)⁻¹ * ∫⁻ n, f n ∂sphereArea := by
  rw [lintegral_velocity_polar (sphereBallLift_measurable e hf)]
  simp_rw [sphereBallLift_radial]
  have hi (n : Sphere) :
      (∫⁻ r : Ioi (0:ℝ), if (r:ℝ) < 1 then f n else 0 ∂Measure.volumeIoiPow 2) =
        (3:ℝ≥0∞)⁻¹*f n := by
    change (∫⁻ r, (Iio (⟨1,by norm_num⟩ : Ioi (0:ℝ))).indicator (fun _ => f n) r
      ∂Measure.volumeIoiPow 2) = _
    rw [lintegral_indicator measurableSet_Iio,setLIntegral_const,Measure.volumeIoiPow_apply_Iio]
    norm_num only [Nat.reduceAdd,one_pow]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3)]
    norm_num [mul_comm]
  simp_rw [hi]
  exact lintegral_const_mul _ hf

theorem radial_cubic_factor {A : Sphere → ℝ≥0∞} (hA : Measurable A) :
    (∫⁻ n : Sphere, ∫⁻ r : Ioi (0:ℝ),
      (if (r:ℝ) < 1 then ENNReal.ofReal ((r:ℝ)^3) else 0)*A n
        ∂Measure.volumeIoiPow 2 ∂sphereArea) = (6:ℝ≥0∞)⁻¹*∫⁻ n, A n ∂sphereArea := by
  have hm : Measurable (fun r : Ioi (0:ℝ) =>
      if (r:ℝ) < 1 then ENNReal.ofReal ((r:ℝ)^3) else 0) := by
    exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (by fun_prop) measurable_const
  simp_rw [lintegral_mul_const _ hm,radial_cubic_unit_integral]
  exact lintegral_const_mul _ hA

end BoltzmannNonuniqueness

end

end

section

/-! # Surface measure is dominated by directions of Lebesgue points in the unit ball -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness

theorem sphereArea_absolutelyContinuous_directions (e : Sphere) :
    sphereArea ≪ Measure.map (sphereDirection e)
      ((volume : Measure Velocity).restrict (Metric.ball 0 1)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply (sphereDirection_measurable e) hN] at hN0
  have hn : ∀ᵐ x : Velocity ∂volume.restrict (Metric.ball 0 1), sphereDirection e x ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not,Set.preimage] using hN0
  have hall := (ae_restrict_iff' measurableSet_ball).mp hn
  have hz : (∫⁻ x : Velocity, sphereBallLift e (N.indicator (fun _ => (1:ℝ≥0∞))) x) = 0 := by
    calc
      _ = ∫⁻ _x : Velocity, (0:ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [hall] with x hx
        by_cases hb : ‖x‖ < 1
        · have hxb : x ∈ Metric.ball (0 : Velocity) 1 := by
            simpa only [Metric.mem_ball,dist_zero_right] using hb
          simp only [sphereBallLift,ite_eq_left hb,Set.indicator_of_notMem (hx hxb)]
        · simp only [sphereBallLift,ite_eq_right hb]
      _ = 0 := lintegral_zero
  rw [sphereBallLift_integral e (measurable_const.indicator hN)] at hz
  change (3:ℝ≥0∞)⁻¹ * (∫⁻ n, N.indicator (1 : Sphere → ℝ≥0∞) n ∂sphereArea) = 0 at hz
  rw [lintegral_indicator_one hN] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

end BoltzmannNonuniqueness

end

end

end OAI
