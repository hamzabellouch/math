import OAI.Analysis.BernoulliCone.HarmonicKernel

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Shape
open HarmonicKernel
variable {d : ℕ}

lemma potential_test : Test (ball (0 : Space d) 2) potential := by
  have he : (potential : Space d → ℝ)=scaledPotential 1 0 := by
    funext x
    simp [potential,scaledPotential]
  rw [he]
  exact scaledPotential_test (by norm_num) 0 (closedBall_subset_ball (by norm_num))

lemma firstTerm_potential (e x : Space d) :
    firstTerm potential e x = -rawKernel x * positiveLinear e x := by
  have hd := radial_directional (contDiff_profile.differentiable (by simp)) x e
  change fderiv ℝ potential x e = 2*deriv profile (‖x‖^2)*inner ℝ x e at hd
  rw [firstTerm,hd]
  by_cases hx : 0 < inner ℝ e x
  · simp only [ite_eq_left hx,positiveLinear,max_eq_left hx.le,rawKernel,kernelProfile]
    rw [real_inner_comm x e]
    ring
  · simp only [ite_eq_right hx,positiveLinear,max_eq_right (not_lt.mp hx),mul_zero]

lemma firstTerm_potential_integral_ne_zero {e : Space d} (he : e ≠ 0) :
    (∫ x in ball (0:Space d) 2, firstTerm potential e x) ≠ 0 := by
  let F := fun x : Space d => rawKernel x*positiveLinear e x
  have hc : Continuous F := contDiff_rawKernel.continuous.mul (positiveLinear_lipschitz e).continuous
  have hs : HasCompactSupport F := rawKernel_compact.mul_right
  have hnonneg : ∀ x, 0 ≤ F x := fun x => mul_nonneg (rawKernel_nonneg x) (le_max_right _ _)
  have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
  let x := (2*‖e‖)⁻¹ • e
  have hxNorm : ‖x‖=(1:ℝ)/2 := by
    dsimp [x]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by positivity))]
    field_simp
  have hxpos : 0 < inner ℝ e x := by
    dsimp [x]
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    positivity
  have hxF : F x ≠ 0 := by
    exact (mul_pos (kernelProfile_pos (by rw [hxNorm]; norm_num))
      (lt_max_of_lt_left hxpos)).ne'
  have hpos : 0 < ∫ y, F y := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs hnonneg hxF
  have hF : (∫ y in ball (0:Space d) 2, F y) = ∫ y, F y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have h1 : y ∉ closedBall (0:Space d) 1 := fun hh => hy (closedBall_subset_ball (by norm_num) hh)
    simp [F,rawKernel_zero h1]
  have hid : (∫ y in ball (0:Space d) 2, firstTerm potential e y) = -(∫ y, F y) := by
    simp_rw [firstTerm_potential]
    rw [show (fun y : Space d => -rawKernel y*positiveLinear e y)=(fun y => -F y) from by funext y; simp [F]]
    rw [integral_neg,hF]
  rw [hid]
  exact neg_ne_zero.mpr hpos.ne'
end Bernoulli.Shape

end
end

end OAI
