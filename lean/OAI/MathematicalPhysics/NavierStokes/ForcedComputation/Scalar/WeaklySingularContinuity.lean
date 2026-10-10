import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.WeaklySingularIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Continuity of a Volterra integral with an inverse-square-root operator singularity. -/

noncomputable section
namespace ForcedComputation.WeaklySingular

open Real MeasureTheory Set Filter
open scoped Topology Interval

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem scale_inverseSqrt {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    t * inverseSqrt (t * r) = Real.sqrt t * inverseSqrt r := by
  have he : t * (Real.sqrt t)⁻¹ = Real.sqrt t := by
    by_cases hz : t = 0
    · simp [hz]
    · have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne ht (Ne.symm hz)))
      change t / Real.sqrt t = Real.sqrt t
      exact (div_eq_iff hs).mpr (Real.mul_self_sqrt ht).symm
  unfold inverseSqrt
  rw [Real.sqrt_mul ht, mul_inv_rev]
  calc
    _ = (t * (Real.sqrt t)⁻¹) * (Real.sqrt r)⁻¹ := by ring
    _ = _ := by rw [he]

private def scaled (K : ℝ → E →L[ℝ] E) (u : ℝ → E) (t r : ℝ) : E :=
  t • K (t * (1 - r)) (u (t * r))

private theorem volterra_eq_scaled (K : ℝ → E →L[ℝ] E) (u : ℝ → E) (t : ℝ) :
    volterra E K u t = ∫ r in 0..1, scaled E K u t r := by
  have he : (fun r => scaled E K u t r) =
      fun r => t • (fun s => K (t - s) (u s)) (t * r) := by
    funext r
    dsimp only [scaled]
    rw [show t * (1 - r) = t - t * r by ring]
  rw [he, intervalIntegral.integral_smul]
  symm
  simpa only [mul_zero, mul_one, volterra] using
    intervalIntegral.smul_integral_comp_mul_left (fun s => K (t - s) (u s)) t
      (a := (0 : ℝ)) (b := 1)

private theorem norm_scaled_le (K : ℝ → E →L[ℝ] E) (u : ℝ → E)
    (C B : ℝ) (hC : 0 ≤ C)
    (hK : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r)
    (hu : ∀ s, ‖u s‖ ≤ B) {t : ℝ} (ht : 0 ≤ t) {r : ℝ} (hr : r ∈ Icc 0 1) :
    ‖scaled E K u t r‖ ≤ C * B * Real.sqrt t * inverseSqrt (1 - r) := by
  have hp : 0 ≤ t * (1 - r) := mul_nonneg ht (sub_nonneg.mpr hr.2)
  calc
    _ = t * ‖K (t * (1 - r)) (u (t * r))‖ := by
      rw [scaled, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    _ ≤ t * ((C * inverseSqrt (t * (1 - r))) * B) :=
      mul_le_mul_of_nonneg_left
        (((K (t * (1 - r))).le_opNorm (u (t * r))).trans
          (mul_le_mul (hK _ hp) (hu _) (norm_nonneg _)
            (mul_nonneg hC (inverseSqrt_nonneg _)))) ht
    _ = C * B * (t * inverseSqrt (t * (1 - r))) := by ring
    _ = _ := by rw [scale_inverseSqrt ht]; ring

private theorem scaled_continuousAt_parameter (K : ℝ → E →L[ℝ] E) (u : ℝ → E)
    (hK : ContinuousOn K (Ioi 0)) (hu : Continuous u) {t : ℝ} (ht : 0 < t)
    {r : ℝ} (hr : r < 1) : ContinuousAt (fun s => scaled E K u s r) t := by
  have hp : 0 < t * (1 - r) := mul_pos ht (sub_pos.mpr hr)
  have harg : ContinuousAt (fun s : ℝ => s * (1 - r)) t :=
    continuousAt_id.mul continuousAt_const
  have hk : ContinuousAt (fun s : ℝ => K (s * (1 - r))) t :=
    (hK.continuousAt (Ioi_mem_nhds hp)).comp (f := fun s : ℝ => s * (1 - r)) harg
  have hsrc : ContinuousAt (fun s : ℝ => u (s * r)) t :=
    hu.continuousAt.comp (continuousAt_id.mul continuousAt_const)
  exact continuousAt_id.smul (hk.clm_apply hsrc)

private theorem scaled_measurable (K : ℝ → E →L[ℝ] E) (u : ℝ → E)
    (hK : ContinuousOn K (Ioi 0)) (hu : Continuous u) {t : ℝ} (ht : 0 < t) :
    AEStronglyMeasurable (scaled E K u t) (volume.restrict (Ι (0 : ℝ) 1)) := by
  have hc : ContinuousOn (scaled E K u t) (Ioo 0 1) := by
    intro r hr
    have hp : 0 < t * (1 - r) := mul_pos ht (sub_pos.mpr hr.2)
    have harg : ContinuousAt (fun q : ℝ => t * (1 - q)) r :=
      continuousAt_const.mul (continuousAt_const.sub continuousAt_id)
    have hk : ContinuousAt (fun q : ℝ => K (t * (1 - q))) r :=
      (hK.continuousAt (Ioi_mem_nhds hp)).comp (f := fun q : ℝ => t * (1 - q)) harg
    have hsrc : ContinuousAt (fun r : ℝ => u (t * r)) r :=
      hu.continuousAt.comp (continuousAt_const.mul continuousAt_id)
    exact (continuousAt_const.smul (hk.clm_apply hsrc)).continuousWithinAt
  rw [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1), ← restrict_Ioo_eq_restrict_Ioc]
  exact hc.aestronglyMeasurable measurableSet_Ioo

/-- Positive-time continuity follows by moving the integral to a fixed unit interval. -/
theorem continuousAt_volterra (K : ℝ → E →L[ℝ] E) (u : ℝ → E)
    (hK : ContinuousOn K (Ioi 0)) (hu : Continuous u)
    (C B : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r)
    (hub : ∀ s, ‖u s‖ ≤ B) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (volterra E K u) t := by
  have hB : 0 ≤ B := (norm_nonneg (u 0)).trans (hub 0)
  have hI : Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hc : ContinuousAt (fun s => ∫ r in 0..1, scaled E K u s r) t := by
    apply intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun r => (C * B * Real.sqrt (2 * t)) * inverseSqrt (1 - r))
    · filter_upwards [hI] with s hs
      exact scaled_measurable E K u hK hu (by linarith [hs.1])
    · filter_upwards [hI] with s hs
      exact ae_of_all _ fun r hr => by
        rw [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hr
        have hs₀ : 0 ≤ s := by linarith [hs.1]
        apply (norm_scaled_le E K u C B hC hbound hub hs₀ ⟨hr.1.le, hr.2⟩).trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs.2.le) (mul_nonneg hC hB))
          (inverseSqrt_nonneg _)
    · exact (inverseSqrt_sub_intervalIntegrable (zero_le_one : (0 : ℝ) ≤ 1)).const_mul _
    · filter_upwards [(volume.ae_ne (1 : ℝ))] with r hr hrs
      rw [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hrs
      exact scaled_continuousAt_parameter E K u hK hu ht (lt_of_le_of_ne hrs.2 hr)
  have he : volterra E K u = fun s => ∫ r in 0..1, scaled E K u s r :=
    funext (volterra_eq_scaled E K u)
  rw [he]
  exact hc

/-- The O(sqrt(t)) estimate supplies the missing continuity at the initial endpoint. -/
theorem continuousWithinAt_volterra_zero (K : ℝ → E →L[ℝ] E) (u : ℝ → E)
    (C B : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r)
    (hub : ∀ s, ‖u s‖ ≤ B) :
    ContinuousWithinAt (volterra E K u) (Ici 0) 0 := by
  have hzero : volterra E K u 0 = 0 := by simp [volterra]
  rw [ContinuousWithinAt, hzero, tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact norm_volterra_le E ht K u C B hC (fun r hr => hbound r hr.1)
      (fun s _ => hub s)
  · have h : Tendsto Real.sqrt (𝓝[Ici (0 : ℝ)] 0) (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).mono_left inf_le_left
    simpa only [Real.sqrt_zero, mul_zero] using h.const_mul (2 * C * B)

/-- A bounded continuous source produces a continuous Volterra path on every finite time interval. -/
theorem continuousOn_volterra (K : ℝ → E →L[ℝ] E) (u : ℝ → E)
    (hK : ContinuousOn K (Ioi 0)) (hu : Continuous u)
    (C B : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r)
    (hub : ∀ s, ‖u s‖ ≤ B) : ContinuousOn (volterra E K u) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    exact continuousWithinAt_volterra_zero E K u C B hC hbound hub
  · exact (continuousAt_volterra E K u hK hu C B hC hbound hub h).continuousWithinAt

end ForcedComputation.WeaklySingular

end

end OAI
