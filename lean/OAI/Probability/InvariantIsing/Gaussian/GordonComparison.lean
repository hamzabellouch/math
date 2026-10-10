import OAI.Probability.InvariantIsing.Gaussian.GordonCurveMean

namespace OAI

/-! Finite Gaussian minimum--maximum comparison for matching row covariances. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

theorem finite_gaussian_gordon_comparison {d : ℕ} (C A : U × V → Fin (d+1) → ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hrow : ∀ x u, gaussianCross A A x (u,x.2) = gaussianCross C C x (u,x.2))
    (hoff : ∀ x y, gaussianCross A A x y ≤ gaussianCross C C x y) :
    (∫ g, gordonValue (fun x => linearGaussian A g x)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) ≤
    ∫ g, gordonValue (fun x => linearGaussian C g x)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  have hd (s : ℝ) := gordonCurveMean_hasDerivAt C A s
  have hs (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi/2)) :
      gordonCurveSlope C A s ≤ 0 := by
    have hsc : 0 ≤ Real.sin s*Real.cos s := mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2,Real.pi_pos]))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1,Real.pi_pos],hs.2⟩)
    apply gordon_gaussian_mean_nonpos
    · intro x u
      rw [cavityGaussianCurve_cross C A s x (u,x.2) hCA,hrow x u,sub_self,mul_zero]
    · intro x y
      rw [cavityGaussianCurve_cross C A s x y hCA]
      exact mul_nonpos_of_nonneg_of_nonpos hsc (sub_nonpos.mpr (hoff x y))
  have hm : AntitoneOn (gordonCurveMean C A) (Set.Icc (0 : ℝ) (Real.pi/2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn
      (fun s _ => (hd s).hasDerivWithinAt)
    intro s hs'
    exact hs s (interior_subset hs')
  have hp : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have he := hm ⟨le_rfl,hp⟩ ⟨hp,le_rfl⟩ hp
  simpa only [gordonCurveMean,linearGaussian,cavityGaussianCurve,
    Real.cos_zero,Real.sin_zero,Real.cos_pi_div_two,Real.sin_pi_div_two,
    one_mul,zero_mul,mul_zero,zero_add,add_zero] using he

end InvariantIsing

end

end OAI
