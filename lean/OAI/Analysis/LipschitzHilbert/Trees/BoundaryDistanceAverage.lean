import OAI.Analysis.LipschitzHilbert.Phase.AngularBoundaryDistance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

/-! A single common translation is uniform at every angular scale.
The folded fractional part has density two on [0,1/2]; no independent
translations at distinct levels are introduced. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem unitBoundaryDistance_integral (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 (1/2:ℝ)) :
    IntervalIntegrable (fun u => f (unitBoundaryDistance u)) volume 0 1 ∧
      (∫ u in (0:ℝ)..1, f (unitBoundaryDistance u)) = 2*(∫ u in (0:ℝ)..(1/2:ℝ), f u) := by
  have hlow : IntervalIntegrable (fun u => f (unitBoundaryDistance u)) volume 0 (1/2:ℝ) := by
    apply hf.congr_uIoo
    intro u hu
    have hu' : 0 < u ∧ u < (1/2:ℝ) := by simpa only [uIoo_of_lt (by norm_num : (0:ℝ)<1/2),mem_Ioo] using hu
    dsimp only
    rw [unitBoundaryDistance_lower hu'.1.le hu'.2.le]
  have href : IntervalIntegrable (fun u => f (1-u)) volume (1/2:ℝ) 1 := by
    convert (hf.comp_sub_left 1).symm using 1 <;> norm_num
  have hhigh : IntervalIntegrable (fun u => f (unitBoundaryDistance u)) volume (1/2:ℝ) 1 := by
    apply href.congr_uIoo
    intro u hu
    have hu' : (1/2:ℝ) < u ∧ u < 1 := by simpa only [uIoo_of_lt (by norm_num : (1/2:ℝ)<1),mem_Ioo] using hu
    dsimp only
    rw [unitBoundaryDistance_upper hu'.1.le hu'.2.le]
  refine ⟨hlow.trans hhigh,?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hlow hhigh]
  have hlo : (∫ u in (0:ℝ)..(1/2:ℝ), f (unitBoundaryDistance u)) =
      ∫ u in (0:ℝ)..(1/2:ℝ), f u := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    dsimp only
    rw [unitBoundaryDistance_lower hu.1.le hu.2.le]
  have hhi : (∫ u in (1/2:ℝ)..1, f (unitBoundaryDistance u)) =
      ∫ u in (0:ℝ)..(1/2:ℝ), f u := by
    calc
      _ = ∫ u in (1/2:ℝ)..1, f (1-u) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro u hu
        dsimp only
        rw [unitBoundaryDistance_upper hu.1.le hu.2.le]
      _ = _ := by rw [intervalIntegral.integral_comp_sub_left]; norm_num
  rw [hlo,hhi]
  ring

theorem unitBoundaryDistance_period_integral (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 (1/2:ℝ)) (n : ℕ) (a : ℝ) :
    (∫ u in a..a+(n:ℝ), f (unitBoundaryDistance u)) =
      (n:ℝ)*2*(∫ u in (0:ℝ)..(1/2:ℝ), f u) := by
  have hper : Function.Periodic (fun u => f (unitBoundaryDistance u)) 1 :=
    fun u => congrArg f (unitBoundaryDistance_periodic u)
  have hu := unitBoundaryDistance_integral f hf
  have hall := hper.intervalIntegrable₀ (by norm_num : (1:ℝ) ≠ 0) hu.1
  have h := hper.intervalIntegral_add_zsmul_eq (n:ℤ) a hall
  have hbase := hper.intervalIntegral_add_eq a 0
  simp only [zero_add] at hbase
  rw [hbase,hu.2] at h
  simpa only [zsmul_eq_mul,Int.cast_natCast,mul_one,mul_assoc] using h

end LipschitzHilbert

end

end OAI
