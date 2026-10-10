import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianCalculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace OAI

/-! Homogeneous derivative estimates for the logarithmic radial coordinate. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radial_iteratedFDeriv_comp_pos_smul (f : E → ℝ) (r : ℝ) (hr : 0 < r)
    (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (fun z => f (r • z)) x =
      r^k • iteratedFDeriv ℝ k f (r • x) := by
  let e : E ≃L[ℝ] E := (Units.mk0 r hr.ne') • ContinuousLinearEquiv.refl ℝ E
  have he := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (x := x) (mem_univ (e x)) k
  simp only [preimage_univ,iteratedFDerivWithin_univ] at he
  change iteratedFDeriv ℝ k (fun z => f (r • z)) x = _ at he
  rw [he]
  ext v
  change (iteratedFDeriv ℝ k f (r • x)) (fun i => r • v i) =
    r^k • (iteratedFDeriv ℝ k f (r • x)) v
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

theorem radialLogNorm_contDiffAt (x : E) (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : E => Real.log ‖y‖) x :=
  (contDiffAt_norm ℝ hx).log (norm_ne_zero_iff.mpr hx)

theorem radialLogNorm_derivative_scaling (r : ℝ) (hr : 0 < r) (x : E) (hx : x ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    r^k • iteratedFDeriv ℝ k (fun y : E => Real.log ‖y‖) (r • x) =
      iteratedFDeriv ℝ k (fun y : E => Real.log ‖y‖) x := by
  have he : (fun y : E => Real.log ‖r • y‖) =ᶠ[nhds x]
      (fun y : E => Real.log r + Real.log ‖y‖) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,Real.log_mul hr.ne'
      (norm_ne_zero_iff.mpr hy)]
  rw [← radial_iteratedFDeriv_comp_pos_smul _ r hr k x,
    (he.iteratedFDeriv ℝ k).eq_of_nhds]
  rw [fun_iteratedFDeriv_add_apply contDiffAt_const
    ((radialLogNorm_contDiffAt x hx).of_le (by simp)),
    iteratedFDeriv_const_of_ne (Nat.ne_of_gt hk)]
  simp only [Pi.zero_apply,zero_add]

theorem radialLogNorm_derivative_bound (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, x ≠ 0 →
      ‖iteratedFDeriv ℝ k (fun y : E => Real.log ‖y‖) x‖ ≤
        C*‖x‖^(-(k : ℝ)) := by
  have hc : ContinuousOn (iteratedFDeriv ℝ k (fun y : E => Real.log ‖y‖))
      (Metric.sphere (0 : E) 1) := by
    intro x hx
    have hn : ‖x‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
    exact ((radialLogNorm_contDiffAt x (by intro hz; simp [hz] at hn)).continuousAt_iteratedFDeriv
      (by simp)).continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u := ‖x‖⁻¹ • x
  have hu : ‖u‖=1 := by
    simp only [u,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),
      inv_mul_cancel₀ hr.ne']
  have hu0 : u ≠ 0 := by intro hz; simp [hz] at hu
  have hxu : ‖x‖ • u=x := by
    simp only [u,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hs := congrArg norm (radialLogNorm_derivative_scaling ‖x‖ hr u hu0 k hk)
  rw [hxu,norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos hr k)] at hs
  have hb := (hC u (by simpa only [Metric.mem_sphere,dist_zero_right] using hu)).trans
    (le_max_left C 0)
  rw [← hs] at hb
  rw [Real.rpow_neg hr.le,Real.rpow_natCast]
  simpa only [div_eq_mul_inv] using
    (le_div_iff₀ (pow_pos hr k)).mpr (by simpa only [mul_comm] using hb)

end DefocusingNLS

end OAI
