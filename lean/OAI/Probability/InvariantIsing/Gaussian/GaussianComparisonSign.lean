import OAI.Probability.InvariantIsing.Cavity.CavityGaussianCurveMean

namespace OAI

/-! Covariance order gives the finite Gaussian log-partition comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {X : Type*} [Fintype X]

lemma gaussian_gibbs_linear_mean_nonneg {d : ℕ} {w : X → ℝ} (hw : GibbsReference w)
    (H : X → ℝ) (A C : X → Fin (d+1) → ℝ)
    (hK : ∀ x y, gaussianCross A C x y ≤ gaussianCross A C x x) :
    0 ≤ ∫ g, ∑ x, gaussianGibbs w H C g x * linearGaussian A g x
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  have hi x : Integrable (fun g => gaussianGibbs w H C g x * linearGaussian A g x)
      (Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) := by
    simpa only [mul_comm] using integrable_linearGaussian_mul_gibbs hw H A C x x
  rw [integral_finsetSum _ (fun x _ => hi x)]
  apply Finset.sum_nonneg
  intro x _
  have he := gaussian_gibbs_insertion hw H A C x
  simp only [mul_comm (gaussianGibbs w H C _ x)]
  rw [he]
  apply integral_nonneg
  intro g
  apply mul_nonneg (finiteGibbs_nonneg hw _ x)
  apply sub_nonneg.mpr
  calc
    _ ≤ ∑ y, gaussianGibbs w H C g y * gaussianCross A C x x := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hK x y) (finiteGibbs_nonneg hw _ y)
    _ = gaussianCross A C x x := by
      rw [← Finset.sum_mul]
      change (∑ y, finiteGibbs w _ y) * _ = _
      rw [finiteGibbs_sum hw,one_mul]

theorem finite_gaussian_log_comparison {d : ℕ} {w : X → ℝ} (hw : GibbsReference w)
    (H : X → ℝ) (C A : X → Fin (d+1) → ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hdiag : ∀ x, gaussianCross A A x x = gaussianCross C C x x)
    (hoff : ∀ x y, gaussianCross A A x y ≤ gaussianCross C C x y) :
    (∫ g, Real.log (finitePartition w (fun x => H x+linearGaussian C g x))
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) ≤
    ∫ g, Real.log (finitePartition w (fun x => H x+linearGaussian A g x))
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  have hd (s : ℝ) := cavityGaussianCurveMean_hasDerivAt hw H (fun _ => 0) 0 C A s
  have hs (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi/2)) :
      0 ≤ cavityGaussianCurveSlope w H (fun _ => 0) 0 C A s := by
    have hsc : 0 ≤ Real.sin s * Real.cos s := mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2,Real.pi_pos]))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1,Real.pi_pos],hs.2⟩)
    have hcross : ∀ x y,
        gaussianCross (cavityGaussianCurveDerivative C A s) (cavityGaussianCurve C A s) x y ≤
        gaussianCross (cavityGaussianCurveDerivative C A s) (cavityGaussianCurve C A s) x x := by
      intro x y
      rw [cavityGaussianCurve_cross C A s x y hCA,cavityGaussianCurve_cross C A s x x hCA,
        hdiag x,sub_self,mul_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hsc (sub_nonpos.mpr (hoff x y))
    have h := gaussian_gibbs_linear_mean_nonneg hw H (cavityGaussianCurveDerivative C A s)
      (cavityGaussianCurve C A s) hcross
    have hp : cavityPenaltyCurve H (fun _ => 0) 0 s = H := by
      funext x
      simp only [cavityPenaltyCurve,mul_zero,zero_mul,sub_zero]
    simpa only [cavityGaussianCurveSlope,hp,zero_mul,mul_zero,zero_add] using h
  have hm : MonotoneOn (cavityGaussianCurveMean w H (fun _ => 0) 0 C A)
      (Set.Icc (0 : ℝ) (Real.pi/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn
      (fun s _ => (hd s).hasDerivWithinAt)
    intro s hs'
    exact hs s (interior_subset hs')
  have hp : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have he := hm ⟨le_rfl,hp⟩ ⟨hp,le_rfl⟩ hp
  simpa only [cavityGaussianCurveMean,cavityPenaltyCurve,linearGaussian,cavityGaussianCurve,
    Real.cos_zero,Real.sin_zero,Real.cos_pi_div_two,Real.sin_pi_div_two,
    one_mul,zero_mul,mul_zero,sub_zero,zero_add,add_zero] using he

end InvariantIsing

end

end OAI
