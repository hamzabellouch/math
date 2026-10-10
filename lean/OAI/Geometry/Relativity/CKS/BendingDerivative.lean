import OAI.Geometry.Relativity.CKS.CKSCollarCoordinates
import OAI.Geometry.Relativity.CKS.BendingProfiles
import OAI.Geometry.Relativity.CKS.CovariantHeat

namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma phi_deriv_continuous : ContinuousOn (deriv phi) (Ioi 0) :=
  (phi_smooth.deriv_of_isOpen isOpen_Ioi (m := ∞) (by simp)).continuousOn
lemma xi_deriv_continuous : Continuous (deriv xi) :=
  xi_smooth.continuous_deriv (by simp)

lemma phi_deriv_initial {x : ℝ} (hx : 0 < x) (h6 : x ≤ 6) : deriv phi x = 0 := by
  have hm : IsLocalMax phi x := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [phi_one h6]
    exact phi_le_one hy
  exact hm.deriv_eq_zero
lemma xi_deriv_initial {x : ℝ} (hx : x ≤ 1) : deriv xi x = 0 := by
  have hm : IsLocalMax xi x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [xi_one hx]
    exact xi_le_one y
  exact hm.deriv_eq_zero
lemma xi_deriv_tail {x : ℝ} (hx : 2 ≤ x) : deriv xi x = 0 := by
  have hm : IsLocalMin xi x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [xi_zero hx]
    exact xi_nonneg y
  exact hm.deriv_eq_zero

lemma phi_deriv_tail {x : ℝ} (hx : 12 ≤ x) : x * deriv phi x = -3 * phi x := by
  have hxp : 0 < x := by linarith
  let c : ℝ → ℝ := fun y => Real.smoothTransition ((y-6)/6)
  have hc : ContDiff ℝ ∞ c := by dsimp [c]; fun_prop
  have hc1 : c x = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  have hcm : IsLocalMax c x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [hc1]
    exact Real.smoothTransition.le_one _
  have hcd : HasDerivAt c 0 x := by
    simpa only [hcm.deriv_eq_zero] using (hc.differentiable (by simp) x).hasDerivAt
  have hp := ((hasDerivAt_const x (1:ℝ)).sub hcd).add
    (hcd.mul ((hasDerivAt_inv hxp.ne').pow 3))
  have he : deriv phi x = ((0-0) + (0*(x⁻¹)^3 + c x * (3*(x⁻¹)^2*(-x⁻¹^2)))) := by
    convert! hp.deriv using 1
    simp [c]
  rw [he,hc1,phi_tail hx]
  field_simp
  ring

theorem phi_scaled_deriv_bound : ∃ C : ℝ, 3 ≤ C ∧ ∀ x : ℝ, 0 < x → |x * deriv phi x| ≤ C * phi x := by
  have hc : ContinuousOn (fun x : ℝ => (x * deriv phi x) / phi x) (Icc 6 12) :=
    (continuousOn_id.mul (phi_deriv_continuous.mono (by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1))).div
      (phi_smooth.continuousOn.mono (by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1))
      (fun x hx => (phi_pos (lt_of_lt_of_le (by norm_num) hx.1)).ne')
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max 3 C, le_max_left _ _, ?_⟩
  intro x hx
  by_cases h6 : x ≤ 6
  · rw [phi_deriv_initial hx h6,mul_zero,abs_zero]
    exact mul_nonneg (le_trans (by norm_num) (le_max_left _ _)) (phi_pos hx).le
  by_cases h12 : 12 ≤ x
  · rw [phi_deriv_tail h12,abs_mul,abs_of_pos (phi_pos hx)]
    norm_num
    exact mul_le_mul_of_nonneg_right (le_max_left 3 C) (phi_pos hx).le
  · have hb := hC x ⟨le_of_not_ge h6,le_of_not_ge h12⟩
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (phi_pos hx)] at hb
    exact (div_le_iff₀ (phi_pos hx)).mp (hb.trans (le_max_right 3 C))

theorem xi_scaled_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |x * deriv xi x| ≤ C := by
  have hc : Continuous (fun x : ℝ => x * deriv xi x) := continuous_id.mul xi_deriv_continuous
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (1:ℝ) 2) hc.continuousOn
  refine ⟨max 0 C,le_max_left _ _,fun x => ?_⟩
  by_cases h1 : x ≤ 1
  · simp only [xi_deriv_initial h1,mul_zero,abs_zero]
    exact le_max_left _ _
  by_cases h2 : 2 ≤ x
  · simp only [xi_deriv_tail h2,mul_zero,abs_zero]
    exact le_max_left _ _
  · have hb := hC x ⟨le_of_not_ge h1,le_of_not_ge h2⟩
    have hh : |x * deriv xi x| ≤ C := by simpa only [Real.norm_eq_abs] using hb
    exact hh.trans (le_max_right _ _)

end
end CKSBending

end

end OAI
