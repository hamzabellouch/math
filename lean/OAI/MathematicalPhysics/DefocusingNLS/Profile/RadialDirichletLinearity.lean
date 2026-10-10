import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDirichletEquation

namespace OAI

/-! Positivity and linearity of the radial Dirichlet inverse. -/

open MeasureTheory Set
namespace DefocusingNLS

theorem radialDirichletKernel_nonneg (R r : ℝ) (f : ℝ → ℝ)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hf : ∀ t ∈ Icc 0 R, 0 ≤ f t) :
    0 ≤ radialDirichletKernel R f r := by
  apply intervalIntegral.integral_nonneg hrR
  intro t ht
  have ht0 : 0 ≤ t := hr.trans ht.1
  apply mul_nonneg ht0 (radialAverage_nonneg f t ?_)
  intro s hs
  exact hf _ ⟨mul_nonneg ht0 hs.1,(mul_le_of_le_one_right ht0 hs.2).trans ht.2⟩

theorem radialAverage_add (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (r : ℝ) :
    radialAverage (f+g) r=radialAverage f r+radialAverage g r := by
  unfold radialAverage
  simp only [Pi.add_apply,add_mul]
  apply intervalIntegral.integral_add
  · exact ((hf.comp (continuous_const.mul continuous_id)).mul
      (continuous_id.pow 11)).intervalIntegrable 0 1
  · exact ((hg.comp (continuous_const.mul continuous_id)).mul
      (continuous_id.pow 11)).intervalIntegrable 0 1

theorem radialAverage_smul (c : ℝ) (f : ℝ → ℝ) (r : ℝ) :
    radialAverage (c • f) r=c*radialAverage f r := by
  unfold radialAverage
  simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,intervalIntegral.integral_const_mul]

theorem radialDirichletKernel_add (R r : ℝ) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    radialDirichletKernel R (f+g) r=
      radialDirichletKernel R f r+radialDirichletKernel R g r := by
  unfold radialDirichletKernel
  simp_rw [radialAverage_add f g hf hg,mul_add]
  apply intervalIntegral.integral_add
  · exact (continuous_id.mul (continuous_radialAverage f hf)).intervalIntegrable r R
  · exact (continuous_id.mul (continuous_radialAverage g hg)).intervalIntegrable r R

theorem radialDirichletKernel_smul (R r c : ℝ) (f : ℝ → ℝ) :
    radialDirichletKernel R (c • f) r=c*radialDirichletKernel R f r := by
  unfold radialDirichletKernel
  simp_rw [radialAverage_smul]
  have he : (fun t => t*(c*radialAverage f t)) = fun t => c*(t*radialAverage f t) := by
    funext t
    ring
  rw [he,intervalIntegral.integral_const_mul]

theorem continuous_radialDirichletKernel (R : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (radialDirichletKernel R f) :=
  (show Differentiable ℝ (radialDirichletKernel R f) from
    fun r => (hasDerivAt_radialDirichletKernel R f hf r).differentiableAt).continuous

theorem radialDirichletKernel_one (R r : ℝ) :
    radialDirichletKernel R (fun _ => 1) r=(R^2-r^2)/24 := by
  unfold radialDirichletKernel radialAverage
  simp only [one_mul,integral_pow]
  norm_num
  ring

end DefocusingNLS

end OAI
