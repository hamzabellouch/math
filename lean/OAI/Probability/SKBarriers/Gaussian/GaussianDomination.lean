import Mathlib

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

def HasExpGrowth {E F : Type} [Norm E] [Norm F] (f : E → F) : Prop :=
  ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ C*Real.exp (M*‖x‖)

theorem integrable_exp_mul_abs_gaussian (M : ℝ) :
    Integrable (fun y : ℝ => Real.exp (M*|y|)) (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_gaussianReal M).add (integrable_exp_mul_gaussianReal (-M))).mono'
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  filter_upwards [] with y
  change ‖Real.exp (M*|y|)‖ ≤ Real.exp (M*y)+Real.exp (-M*y)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hy]
    have he : M*(-y) = -M*y := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

section GaussianDomination
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem HasExpGrowth.gaussian_section_bound {f : E × ℝ → F} (hg : HasExpGrowth f) (R : ℝ) :
    ∃ b : ℝ → ℝ, Integrable b (gaussianReal 0 1) ∧
      ∀ x y, ‖x‖ ≤ R → ‖f (x,y)‖ ≤ b y := by
  obtain ⟨C,M,hC,hM,hg⟩ := hg
  refine ⟨fun y => C*Real.exp (M*R)*Real.exp (M*|y|),
    (integrable_exp_mul_abs_gaussian M).const_mul _, ?_⟩
  intro x y hx
  apply (hg (x,y)).trans
  change C * Real.exp (M*‖(x,y)‖) ≤ C*Real.exp (M*R)*Real.exp (M*|y|)
  rw [mul_assoc, ← Real.exp_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Prod.norm_def, Real.norm_eq_abs]
  exact max_le (hx.trans (le_add_of_nonneg_right (abs_nonneg _)))
    (le_add_of_nonneg_left ((norm_nonneg x).trans hx))

theorem HasExpGrowth.integrable_gaussian_section {f : E × ℝ → F}
    (hg : HasExpGrowth f) (hf : Continuous f) (x : E) :
    Integrable (fun y => f (x,y)) (gaussianReal 0 1) := by
  obtain ⟨b,hb,hbound⟩ := hg.gaussian_section_bound ‖x‖
  exact hb.mono' (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (ae_of_all _ (fun y => hbound x y le_rfl))

theorem HasExpGrowth.continuous_gaussian_integral {f : E × ℝ → F}
    (hg : HasExpGrowth f) (hf : Continuous f)
    [NormedSpace ℝ F] :
    Continuous (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  obtain ⟨b,hb,hbound⟩ := hg.gaussian_section_bound (‖x₀‖+1)
  apply continuousAt_of_dominated (bound := b)
  · exact Eventually.of_forall (fun x => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ)<1)] with x hx
    exact ae_of_all _ (fun y => hbound x y (by
      have hnorm : ‖x‖ ≤ ‖x-x₀‖+‖x₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x-x₀) x₀
      rw [← dist_eq_norm] at hnorm
      have hdist : dist x x₀ < 1 := hx
      linarith))
  · exact hb
  · exact ae_of_all _ (fun y => (hf.comp (continuous_id.prodMk continuous_const)).continuousAt)

end GaussianDomination

section GaussianDifferentiation
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem hasFDerivAt_gaussian_integral (f : E × ℝ → F) (f₁ : E × ℝ → E →L[ℝ] F)
    (hf : Continuous f) (hf₁ : Continuous f₁)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth f₁)
    (hd : ∀ x y, HasFDerivAt (fun z => f (z,y)) (f₁ (x,y)) x) (x₀ : E) :
    HasFDerivAt (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)
      (∫ y, f₁ (x₀,y) ∂gaussianReal 0 1) x₀ := by
  obtain ⟨b,hb,hbound⟩ := hg₁.gaussian_section_bound (‖x₀‖+1)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball x₀ 1)
    (Metric.ball_mem_nhds x₀ (by norm_num))
  · exact Eventually.of_forall (fun x => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact hg.integrable_gaussian_section hf x₀
  · exact (hf₁.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun y x hx => hbound x y (by
      have hnorm : ‖x‖ ≤ ‖x-x₀‖+‖x₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x-x₀) x₀
      rw [← dist_eq_norm] at hnorm
      have hdist : dist x x₀ < 1 := hx
      linarith))
  · exact hb
  · exact ae_of_all _ (fun y x _ => hd x y)

end GaussianDifferentiation
end SK.Analytic

end
end
end
end
end
end

end OAI
