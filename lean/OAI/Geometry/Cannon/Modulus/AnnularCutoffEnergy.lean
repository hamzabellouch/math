import Mathlib
import OAI.Geometry.Cannon.Conformal.OpenMapMaxSphere
import OAI.Geometry.Cannon.Topology.PlaneBox

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonPlane
open Complex

theorem annularCutoff_energy {r R C : ℝ} (hr : 0 < r) (hrR : 2*r ≤ R)
    (hC0 : 0 ≤ C) (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) :
    (∫ z in closedBall (0:ℂ) R, ‖fderiv ℝ (annularCutoff r R) z‖^2) ≤
      4*Real.pi*C^2/Real.log (R/r) := by
  have hrR' : r < R := by linarith
  let L := Real.log (R/r)
  have hL : 0 < L := Real.log_pos ((one_lt_div hr).mpr hrR')
  let q (z : ℂ) := ‖fderiv ℝ (annularCutoff r R) z‖^2
  have hq : Continuous q := ((annularCutoff_contDiff hr hrR').continuous_fderiv (by simp)).norm.pow 2
  let e (ρ : ℝ) := ρ*(∫ t in (-Real.pi)..Real.pi, q (circleMap 0 ρ t))
  have he : Continuous e := continuous_id.mul (continuous_circle_integral hq 0)
  have hzero (ρ : ℝ) (hρ : ρ ∈ Icc 0 (r/2)) : e ρ=0 := by
    dsimp only [e]
    have heq : (∫ t in (-Real.pi)..Real.pi, q (circleMap 0 ρ t))=0 := by
      apply (intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_).trans intervalIntegral.integral_zero
      intro _ _
      dsimp only [q]
      rw [annularCutoff_fderiv_zero_inner hr hrR']
      · simp
      · rw [norm_circleMap_zero,abs_of_nonneg hρ.1]
        linarith [hρ.2]
    rw [heq,mul_zero]
  have hsmall : (∫ ρ in (0:ℝ)..(r/2), e ρ)=0 := by
    apply (intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_).trans intervalIntegral.integral_zero
    intro ρ hρ
    rw [uIcc_of_le (by positivity)] at hρ
    exact hzero ρ hρ
  have hbound (ρ : ℝ) (hρ : 0 < ρ) :
      e ρ ≤ (2*Real.pi*C^2/L^2)*ρ⁻¹ := by
    have hang : (∫ t in (-Real.pi)..Real.pi, q (circleMap 0 ρ t)) ≤
        (2*Real.pi)*(C/(L*ρ))^2 := by
      calc
        _ ≤ ∫ _t in (-Real.pi)..Real.pi, (C/(L*ρ))^2 := by
          apply intervalIntegral.integral_mono_on (neg_le_self Real.pi_pos.le)
            ((hq.comp (continuous_circleMap 0 ρ)).intervalIntegrable _ _) intervalIntegrable_const
          intro angle _
          have hn : ‖circleMap 0 ρ angle‖=ρ := by rw [norm_circleMap_zero,abs_of_pos hρ]
          have hz : circleMap 0 ρ angle ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact hρ)
          have hh := annularCutoff_fderiv_bound hr hrR' hC hz
          rw [hn] at hh
          exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hC0 (mul_pos hL hρ).le)).mpr hh
        _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
    have hh := mul_le_mul_of_nonneg_left hang hρ.le
    have hid : ρ*((2*Real.pi)*(C/(L*ρ))^2)=(2*Real.pi*C^2/L^2)*ρ⁻¹ := by field_simp
    exact hh.trans_eq hid
  have hInv : IntervalIntegrable (fun ρ : ℝ => ρ⁻¹) volume (r/2) R :=
    ContinuousOn.intervalIntegrable (continuousOn_id.inv₀ (by
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      change x ≠ 0
      intro hx0
      linarith [hx.1]))
  have hi := intervalIntegral.integral_mono_on (show r/2 ≤ R by linarith)
    (he.intervalIntegrable _ _) (hInv.const_mul (2*Real.pi*C^2/L^2))
    (fun ρ hρ => hbound ρ (by linarith [hρ.1]))
  rw [intervalIntegral.integral_const_mul,integral_inv_of_pos (by positivity) (by linarith)] at hi
  have hlog : Real.log (R/(r/2)) ≤ 2*L := by
    have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) ((le_div_iff₀ hr).mpr hrR)
    have hid : R/(r/2)=(R/r)*2 := by ring
    rw [hid,Real.log_mul (div_ne_zero (by linarith) hr.ne') (by norm_num)]
    dsimp only [L] at h2 ⊢
    linarith
  have hi' := hi.trans (mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2*Real.pi*C^2/L^2))
  have hid : (2*Real.pi*C^2/L^2)*(2*L)=4*Real.pi*C^2/L := by field_simp; ring
  rw [hid] at hi'
  rw [disk_polar_integral hq 0 (by linarith)]
  change (∫ ρ in (0:ℝ)..R, e ρ) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (he.intervalIntegrable 0 (r/2))
    (he.intervalIntegrable (r/2) R),hsmall,zero_add]
  exact hi'

end CannonPlane

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
