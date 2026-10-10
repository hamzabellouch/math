import OAI.Analysis.CircleDomains.Topology.QuarterCircleSubstitution

namespace OAI

/-! Reflected quarter-circle projections, with the positive transverse
Lebesgue orientation. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem integral_quarter_sin_sub (g : ℝ → ℝ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ θ in (0 : ℝ)..(Real.pi/2), g (c-r*Real.sin θ)*(r*Real.cos θ)) =
      ∫ y in (c-r)..c, g y := by
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hd (θ : ℝ) : HasDerivAt (fun t => c-r*Real.sin t) (-(r*Real.cos θ)) θ := by
    simpa only [neg_mul] using ((Real.hasDerivAt_sin θ).const_mul r).const_sub c
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (f := fun θ => c-r*Real.sin θ) (f' := fun θ => -(r*Real.cos θ)) (g := g)
    (by fun_prop) (fun θ _ => hd θ) (by
      intro θ hθ
      rw [min_eq_left hπ,max_eq_right hπ] at hθ
      exact neg_nonpos.mpr (mul_nonneg hr (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1,Real.pi_pos],hθ.2.le⟩)))
  simp only [Function.comp_def,Real.sin_zero,mul_zero,sub_zero,Real.sin_pi_div_two,mul_one,
    mul_neg,intervalIntegral.integral_neg] at h
  rw [intervalIntegral.integral_symm (c-r) c] at h
  exact neg_injective h

 theorem integral_quarter_cos_sub (g : ℝ → ℝ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ θ in (0 : ℝ)..(Real.pi/2), g (c-r*Real.cos θ)*(r*Real.sin θ)) =
      ∫ x in (c-r)..c, g x := by
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hd (θ : ℝ) : HasDerivAt (fun t => c-r*Real.cos t) (r*Real.sin θ) θ := by
    simpa only [mul_neg,neg_neg] using ((Real.hasDerivAt_cos θ).const_mul r).const_sub c
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun θ => c-r*Real.cos θ) (f' := fun θ => r*Real.sin θ) (g := g)
    (by fun_prop) (fun θ _ => hd θ) (by
      intro θ hθ
      rw [min_eq_left hπ,max_eq_right hπ] at hθ
      exact mul_nonneg hr (Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le,by linarith [hθ.2,Real.pi_pos]⟩))
  simpa only [Function.comp_def,Real.cos_zero,mul_one,Real.cos_pi_div_two,mul_zero,sub_zero] using h

end CircleDomainRigidity

end

end OAI
