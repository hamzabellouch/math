import OAI.Analysis.CircleDomains.Rigidity.QuadrantFlux

namespace OAI

/-! Monotone one-dimensional substitutions for quarter-circle projections.
The scalar integrand may be measurable rather than continuous. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem integral_quarter_sin (g : ℝ → ℝ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ θ in (0 : ℝ)..(Real.pi/2), g (c+r*Real.sin θ)*(r*Real.cos θ)) =
      ∫ y in c..(c+r), g y := by
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hd (θ : ℝ) : HasDerivAt (fun t => c+r*Real.sin t) (r*Real.cos θ) θ :=
    (Real.hasDerivAt_sin θ).const_mul r |>.const_add c
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun θ => c+r*Real.sin θ) (f' := fun θ => r*Real.cos θ) (g := g)
    (by fun_prop) (fun θ _ => hd θ) (by
      intro θ hθ
      rw [min_eq_left hπ,max_eq_right hπ] at hθ
      exact mul_nonneg hr (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],hθ.2.le⟩))
  simpa only [Function.comp_def,Real.sin_zero,mul_zero,add_zero,Real.sin_pi_div_two,mul_one] using h

 theorem integral_quarter_cos (g : ℝ → ℝ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ θ in (0 : ℝ)..(Real.pi/2), g (c+r*Real.cos θ)*(r*Real.sin θ)) =
      ∫ x in c..(c+r), g x := by
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hd (θ : ℝ) : HasDerivAt (fun t => c+r*Real.cos t) (-(r*Real.sin θ)) θ := by
    simpa only [mul_neg] using (Real.hasDerivAt_cos θ).const_mul r |>.const_add c
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (f := fun θ => c+r*Real.cos θ) (f' := fun θ => -(r*Real.sin θ)) (g := g)
    (by fun_prop) (fun θ _ => hd θ) (by
      intro θ hθ
      rw [min_eq_left hπ,max_eq_right hπ] at hθ
      exact neg_nonpos.mpr (mul_nonneg hr (Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le,by linarith [hθ.2,Real.pi_pos]⟩)))
  simp only [Function.comp_def,Real.cos_zero,mul_one,Real.cos_pi_div_two,mul_zero,add_zero,
    mul_neg,intervalIntegral.integral_neg] at h
  rw [intervalIntegral.integral_symm c (c+r)] at h
  exact neg_injective h

 theorem quarter_sin_sqrt {r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) :
    Real.sqrt (r^2-(r*Real.sin θ)^2) = r*Real.cos θ := by
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have he : r^2-(r*Real.sin θ)^2 = (r*Real.cos θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [he,Real.sqrt_sq (mul_nonneg hr hc)]

 theorem quarter_cos_sqrt {r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) :
    Real.sqrt (r^2-(r*Real.cos θ)^2) = r*Real.sin θ := by
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1,by linarith [hθ.2,Real.pi_pos]⟩
  have he : r^2-(r*Real.cos θ)^2 = (r*Real.sin θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [he,Real.sqrt_sq (mul_nonneg hr hs)]

end CircleDomainRigidity

end

end OAI
