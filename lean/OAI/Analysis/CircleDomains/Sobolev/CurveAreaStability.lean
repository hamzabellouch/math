import OAI.Analysis.CircleDomains.Sobolev.SmoothImageArea

namespace OAI

/-! Quantitative signed-area stability for two smooth closed-curve
parametrizations. Values and first derivatives are controlled explicitly. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem signedCurveArea_stability {F G : ℝ → ℂ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    {A B ε η : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (hε : 0 ≤ ε) (_hη : 0 ≤ η)
    (hGval : ∀ t, ‖G t‖ ≤ A) (hGder : ∀ t, ‖deriv G t‖ ≤ B)
    (hval : ∀ t, ‖F t-G t‖ ≤ ε) (hder : ∀ t, ‖deriv F t-deriv G t‖ ≤ η) :
    |signedCurveArea F-signedCurveArea G| ≤ ε*B+(A+ε)*η := by
  have hFi : IntervalIntegrable (fun t => (F t).re*(deriv F t).im) volume 0 1 :=
    ((Complex.continuous_re.comp hF.continuous).mul
      (Complex.continuous_im.comp hF.continuous_deriv_one)).intervalIntegrable _ _
  have hGi : IntervalIntegrable (fun t => (G t).re*(deriv G t).im) volume 0 1 :=
    ((Complex.continuous_re.comp hG.continuous).mul
      (Complex.continuous_im.comp hG.continuous_deriv_one)).intervalIntegrable _ _
  unfold signedCurveArea
  rw [← intervalIntegral.integral_sub hFi hGi]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := ε*B+(A+ε)*η) (fun t _ht => show
      ‖(F t).re*(deriv F t).im-(G t).re*(deriv G t).im‖ ≤ _ from by
      have hFn : ‖F t‖ ≤ A+ε := by
        calc
          _ = ‖(F t-G t)+G t‖ := by rw [sub_add_cancel]
          _ ≤ ‖F t-G t‖+‖G t‖ := norm_add_le _ _
          _ ≤ ε+A := add_le_add (hval t) (hGval t)
          _ = _ := add_comm _ _
      have heq : (F t).re*(deriv F t).im-(G t).re*(deriv G t).im =
          (F t-G t).re*(deriv G t).im+(F t).re*(deriv F t-deriv G t).im := by
        simp only [Complex.sub_re, Complex.sub_im]
        ring
      rw [heq]
      calc
        _ ≤ ‖(F t-G t).re*(deriv G t).im‖+‖(F t).re*(deriv F t-deriv G t).im‖ := norm_add_le _ _
        _ ≤ ‖F t-G t‖*‖deriv G t‖+‖F t‖*‖deriv F t-deriv G t‖ := by
          simp only [norm_mul, Real.norm_eq_abs]
          exact add_le_add
            (mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
              (abs_nonneg _) (norm_nonneg _))
            (mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
              (abs_nonneg _) (norm_nonneg _))
        _ ≤ _ := add_le_add
          (mul_le_mul (hval t) (hGder t) (norm_nonneg _) hε)
          (mul_le_mul hFn (hder t) (norm_nonneg _) (add_nonneg hA hε)))
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hh

end CircleDomainRigidity

end

end OAI
