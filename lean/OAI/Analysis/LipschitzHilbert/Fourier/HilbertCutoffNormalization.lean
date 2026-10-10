import OAI.Analysis.LipschitzHilbert.Fourier.HilbertCutoffDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! The compact derivative profile has integral minus two, fixing the
normalization of the physical telescoping profile at the origin. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertCutoffDerivative_nonneg_arg (x : ℝ) (hx : 0≤x) :
    hilbertCutoffDerivative x=((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
  change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=_
  by_cases h : 1/2≤x
  · rw [hilbertSmoothSign_pos x h,one_mul]
  · have ha : |x|≤1 := by rw [abs_of_nonneg hx]; linarith
    rw [verticalBinPlateauReal_deriv_zero x (Or.inl ha),mul_zero,Complex.ofReal_zero]

theorem hilbertCutoffDerivative_nonpos_arg (x : ℝ) (hx : x≤0) :
    hilbertCutoffDerivative x= -((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
  change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=_
  by_cases h : x≤-(1/2)
  · rw [hilbertSmoothSign_neg x h,neg_one_mul,Complex.ofReal_neg]
  · have ha : |x|≤1 := by rw [abs_of_nonpos hx]; linarith
    rw [verticalBinPlateauReal_deriv_zero x (Or.inl ha),mul_zero,Complex.ofReal_zero,neg_zero]

theorem hilbertCutoffDerivative_integral : (∫ x, hilbertCutoffDerivative x)=(-2:ℂ) := by
  have hc : Continuous (fun x => ((deriv verticalBinPlateauReal x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).2.continuous
  have hd (x : ℝ) : HasDerivAt verticalBinPlateau ((deriv verticalBinPlateauReal x : ℝ) : ℂ) x := by
    exact ((contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).1 x).hasDerivAt.ofReal_comp
  have hpos : (∫ x in (0:ℝ)..3, hilbertCutoffDerivative x)=(-1:ℂ) := by
    calc
      _ = ∫ x in (0:ℝ)..3, ((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (0:ℝ)≤3)] at hx
        exact hilbertCutoffDerivative_nonneg_arg x hx.1
      _ = verticalBinPlateau 3-verticalBinPlateau 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)
      _ = -1 := by
        have h3 : verticalBinPlateau (3:ℝ)=0 := by
          change (verticalBinPlateauReal 3:ℂ)=0
          rw [verticalBinPlateauReal_zero 3 (Or.inr (by norm_num)),Complex.ofReal_zero]
        rw [h3,verticalBinPlateau_one 0 (by norm_num),zero_sub]
  have hneg : (∫ x in (-3:ℝ)..0, hilbertCutoffDerivative x)=(-1:ℂ) := by
    calc
      _ = ∫ x in (-3:ℝ)..0, -((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (-3:ℝ)≤0)] at hx
        exact hilbertCutoffDerivative_nonpos_arg x hx.2
      _ = -(verticalBinPlateau 0-verticalBinPlateau (-3)) := by
        rw [intervalIntegral.integral_neg]
        congr 1
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)
      _ = -1 := by
        have h3 : verticalBinPlateau (-3:ℝ)=0 := by
          change (verticalBinPlateauReal (-3):ℂ)=0
          rw [verticalBinPlateauReal_zero (-3) (Or.inl (by norm_num)),Complex.ofReal_zero]
        rw [h3,verticalBinPlateau_one 0 (by norm_num),sub_zero]
  have hsupport : Function.support hilbertCutoffDerivative ⊆ Ioc (-3:ℝ) 3 := by
    intro x hx
    have ha : |x|<2 := by
      by_contra hn
      have hz := verticalBinPlateauReal_deriv_zero x (Or.inr (le_of_not_gt hn))
      apply hx
      change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=0
      rw [hz,mul_zero,Complex.ofReal_zero]
    have hb := abs_lt.mp ha
    constructor <;> linarith
  rw [←intervalIntegral.integral_eq_integral_of_support_subset hsupport,
    ←intervalIntegral.integral_add_adjacent_intervals
      (hilbertCutoffDerivative.continuous.intervalIntegrable (-3) 0)
      (hilbertCutoffDerivative.continuous.intervalIntegrable 0 3),hneg,hpos]
  norm_num

end LipschitzHilbert.PacketRepresentation

end

end OAI
