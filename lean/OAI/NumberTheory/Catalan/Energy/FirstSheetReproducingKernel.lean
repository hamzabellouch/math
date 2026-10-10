import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI


noncomputable section

namespace InternalCatalan

open Complex Metric
open scoped ComplexConjugate

def firstSheetKernel (x : ℝ) (z : ℂ) : ℂ := (1 - (x : ℂ) * z)⁻¹

theorem firstSheetKernel_denominator_ne_zero {x : ℝ} {z : ℂ}
    (hx : |x| < 1) (hz : ‖z‖ ≤ 1) : 1 - (x : ℂ) * z ≠ 0 := by
  have hm : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |x| * ‖z‖ ≤ |x| * 1 := mul_le_mul_of_nonneg_left hz (abs_nonneg x)
      _ < 1 := by simpa only [mul_one] using hx
  intro h
  have heq : (x : ℂ) * z = 1 := (sub_eq_zero.mp h).symm
  rw [heq, norm_one] at hm
  exact (lt_irrefl 1) hm

theorem conj_firstSheetKernel_on_circle (x : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    conj (firstSheetKernel x z) = z / (z - (x : ℂ)) := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have heq : (1 : ℂ) - (x : ℂ) * z⁻¹ = (z - (x : ℂ)) / z := by
    field_simp [hz0]
  simp only [firstSheetKernel, map_inv₀, map_sub, map_one, map_mul,
    Complex.conj_ofReal, ← Complex.inv_eq_conj hz]
  rw [heq]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]

theorem firstSheetKernel_continuousOn_closedDisk {x : ℝ} (hx : |x| < 1) :
    ContinuousOn (firstSheetKernel x) (closedBall (0 : ℂ) 1) := by
  change ContinuousOn (fun z : ℂ => (1 - (x : ℂ) * z)⁻¹) (closedBall (0 : ℂ) 1)
  have hc : Continuous (fun z : ℂ => 1 - (x : ℂ) * z) := by fun_prop
  apply hc.continuousOn.inv₀
  intro z hz
  apply firstSheetKernel_denominator_ne_zero hx
  simpa only [mem_closedBall, dist_zero_right] using hz

theorem circleIntegrable_mul_conj_firstSheetKernel {u : ℂ → ℂ}
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) 1)) {x : ℝ} (hx : |x| < 1) :
    CircleIntegrable (fun z => u z * conj (firstSheetKernel x z)) 0 1 := by
  have huc : ContinuousOn u (sphere (0 : ℂ) 1) :=
    hu.continuousOn.mono sphere_subset_closedBall
  have hkc : ContinuousOn (firstSheetKernel x) (sphere (0 : ℂ) 1) :=
    (firstSheetKernel_continuousOn_closedDisk hx).mono sphere_subset_closedBall
  have hconj : ContinuousOn (fun z => conj (firstSheetKernel x z))
      (sphere (0 : ℂ) 1) := Complex.continuous_conj.comp_continuousOn hkc
  exact ContinuousOn.circleIntegrable (by norm_num) (huc.mul hconj)

theorem circleAverage_mul_conj_firstSheetKernel {u : ℂ → ℂ}
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) 1)) {x : ℝ} (hx : |x| < 1) :
    Real.circleAverage (fun z => u z * conj (firstSheetKernel x z)) 0 1 = u x := by
  have hd : DiffContOnCl ℂ u (ball (0 : ℂ) 1) :=
    hu.differentiableOn.diffContOnCl_ball Set.Subset.rfl
  have hxball : (x : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hx
  rw [Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
  have hint :
      (∮ z in C((0 : ℂ), 1), (z - 0)⁻¹ • (u z * conj (firstSheetKernel x z))) =
      ∮ z in C((0 : ℂ), 1), (z - (x : ℂ))⁻¹ • u z := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    have hz0 : z ≠ 0 := by
      intro h
      simp [h] at hzn
    simp only [sub_zero, smul_eq_mul, conj_firstSheetKernel_on_circle x hzn,
      div_eq_mul_inv]
    calc
      z⁻¹ * (u z * (z * (z - (x : ℂ))⁻¹)) =
          (z⁻¹ * z) * ((z - (x : ℂ))⁻¹ * u z) := by ring
      _ = (z - (x : ℂ))⁻¹ * u z := by rw [inv_mul_cancel₀ hz0, one_mul]
  rw [hint]
  exact hd.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hxball

theorem intervalIntegral_mul_conj_firstSheetKernel {u : ℂ → ℂ}
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) 1)) {x : ℝ} (hx : |x| < 1) :
    (2 * Real.pi)⁻¹ •
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        u (circleMap 0 1 θ) * conj (firstSheetKernel x (circleMap 0 1 θ))) = u x := by
  simpa only [Real.circleAverage_def] using circleAverage_mul_conj_firstSheetKernel hu hx

end InternalCatalan

end

end OAI
