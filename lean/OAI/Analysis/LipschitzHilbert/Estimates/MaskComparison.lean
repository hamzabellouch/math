import OAI.Analysis.LipschitzHilbert.Estimates.TopMaskApproximation
import Mathlib.Analysis.Normed.Module.Basic

namespace OAI

/-! Quantitative comparison of a finite top synthesis with its actual
sinc-masked version. The near and far estimates use the same fixed
polynomial top envelope. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem norm_sum_sub_mask_le {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ι → E) (mask weight : ι → ℝ) (T ε : ℝ) (_hT : 0 ≤ T) (_hε : 0 ≤ ε)
    (hw : ∀ i, 0 ≤ weight i)
    (hF : ∀ i, ‖F i‖ ≤ T*(weight i)^8)
    (hmask : ∀ i, |1-mask i| *T*(weight i)^7 ≤ ε) :
    ‖(∑ i, F i)-(∑ i, mask i • F i)‖ ≤ ε*∑ i, weight i := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖F i-mask i • F i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ε*weight i := by
      apply Finset.sum_le_sum
      intro i _
      rw [show F i-mask i • F i = (1-mask i) • F i by module,
        norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ |1-mask i| *(T*(weight i)^8) :=
          mul_le_mul_of_nonneg_left (hF i) (abs_nonneg _)
        _ = (|1-mask i| *T*(weight i)^7)*weight i := by ring
        _ ≤ ε*weight i := mul_le_mul_of_nonneg_right (hmask i) (hw i)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem topSincMask_near_far (L A x y h T ε H : ℝ) (hL : 1 ≤ L)
    (hh : 0 ≤ h) (hT : 0 ≤ T) (_hε : 0 ≤ ε) (_hH : 0 ≤ H)
    (hhH : h ≤ H)
    (hnear : (4/3:ℝ)*L^(1-A)*T*H^7 ≤ ε)
    (hfar : (¬ (|x| ≤ L^(A/2) ∧ |y| ≤ L^(A/2))) → T*h^7 ≤ ε) :
    |1-topSincMask L A x y| *T*h^7 ≤ ε := by
  by_cases hxy : |x| ≤ L^(A/2) ∧ |y| ≤ L^(A/2)
  · have hm := topSincMask_near_error L A x y hL hxy.1 hxy.2
    have hp := pow_le_pow_left₀ hh hhH 7
    calc
      _ ≤ ((4/3:ℝ)*L^(1-A))*T*H^7 := by
        gcongr
      _ ≤ ε := hnear
  · calc
      _ ≤ 1*T*h^7 := by
        gcongr
        exact topSincMask_error_le_one L A x y
      _ = T*h^7 := by ring
      _ ≤ ε := hfar hxy

end LipschitzHilbert

end

end OAI
