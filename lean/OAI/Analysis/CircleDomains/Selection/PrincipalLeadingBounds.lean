import OAI.Analysis.CircleDomains.Sobolev.PrincipalCircleArea

namespace OAI

/-! Size, derivative and smoothness bounds for the leading principal
curve. These estimates isolate its contribution from the analytic remainder. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principalLeadingCurve_norm {R : ℝ} (hR : 1 ≤ R) (c : ℂ) (t : ℝ) :
    ‖principalLeadingCurve R c t‖ ≤ (1+‖c‖)*R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hn : ‖unitCircleParam 0 R t‖ = R := by
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
  have hq : ‖c/unitCircleParam 0 R t‖ ≤ ‖c‖*R := by
    rw [norm_div, hn, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left ((inv_le_one_of_one_le₀ hR).trans hR) (norm_nonneg c)
  calc
    _ ≤ ‖unitCircleParam 0 R t‖+‖c/unitCircleParam 0 R t‖ := norm_add_le _ _
    _ ≤ R+‖c‖*R := add_le_add (le_of_eq hn) hq
    _ = _ := by ring

 theorem principalLeadingCurve_deriv_norm {R : ℝ} (hR : 1 ≤ R) (c : ℂ) (t : ℝ) :
    ‖deriv (principalLeadingCurve R c) t‖ ≤ 2*Real.pi*(1+‖c‖)*R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hn : ‖unitCircleParam 0 R t‖ = R := by
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
  have hq : ‖c/unitCircleParam 0 R t‖ ≤ ‖c‖*R := by
    rw [norm_div, hn, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left ((inv_le_one_of_one_le₀ hR).trans hR) (norm_nonneg c)
  rw [(principalLeadingCurve_hasDerivAt R hRp c t).deriv, norm_mul, norm_mul,
    Complex.norm_I, mul_one]
  have hc : ‖(2*Real.pi : ℂ)‖ = 2*Real.pi := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hc]
  calc
    _ ≤ (‖unitCircleParam 0 R t‖+‖c/unitCircleParam 0 R t‖)*(2*Real.pi) :=
      mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
    _ ≤ (R+‖c‖*R)*(2*Real.pi) :=
      mul_le_mul_of_nonneg_right (add_le_add (le_of_eq hn) hq) (by positivity)
    _ = _ := by ring

 theorem principalLeadingCurve_smooth {R : ℝ} (hR : 0 < R) (c : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (principalLeadingCurve R c) := by
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (unitCircleParam 0 R) :=
    (contDiff_circleMap 0 R).comp (contDiff_const.mul contDiff_id)
  have hn (t : ℝ) : unitCircleParam 0 R t ≠ 0 := by
    have hh : ‖unitCircleParam 0 R t‖ = R := by
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
    intro he
    rw [he, norm_zero] at hh
    linarith
  change ContDiff ℝ (⊤ : ℕ∞) (fun t => unitCircleParam 0 R t+c*(unitCircleParam 0 R t)⁻¹)
  exact hγ.add (contDiff_const.mul (hγ.inv hn))

end CircleDomainRigidity

end

end OAI
