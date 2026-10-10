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
namespace SK.Analytic

theorem hasFDerivAt_intervalIntegral
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → ℝ → F) (f₁ : E → ℝ → E →L[ℝ] F)
    (hf : Continuous (Function.uncurry f)) (hf₁ : Continuous (Function.uncurry f₁))
    (hd : ∀ x y, HasFDerivAt (fun z => f z y) (f₁ x y) x)
    (a b : ℝ) (x : E) :
    HasFDerivAt (fun z => ∫ y in a..b, f z y) (∫ y in a..b, f₁ x y) x := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod (show IsCompact (uIcc a b) from isCompact_uIcc)).exists_bound_of_continuousOn
    hf₁.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := f₁) (bound := fun _ => C) (s := Metric.closedBall x 1)
    (Metric.closedBall_mem_nhds x (by norm_num))
  · exact Filter.Eventually.of_forall fun z => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hf₁.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y hy z hz => hC (z, y) ⟨hz, uIoc_subset_uIcc hy⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun y _ z _ => hd z y

theorem contDiff_intervalIntegral
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (f : E × ℝ → F) (hf : ContDiff ℝ n f) (a b : ℝ) :
    ContDiff ℝ n (fun x => ∫ y in a..b, f (x, y)) := by
  induction n generalizing F with
  | zero =>
    apply contDiff_zero.mpr
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x y => f (x,y)) (by convert! hf.continuous using 1) a b
  | succ n ih =>
    let f₁ : E × ℝ → E →L[ℝ] F := fun p =>
      (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hf₁ : ContDiff ℝ n f₁ := by
      apply ContDiff.clm_comp _ contDiff_const
      exact hf.fderiv_right (by simp)
    have hdiff : ∀ x y, HasFDerivAt (fun z => f (z, y)) (f₁ (x,y)) x := by
      intro x y
      have hd := (hf.differentiable (by simp) (x, y)).hasFDerivAt
      exact hd.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
    have hI : ∀ x, HasFDerivAt (fun z => ∫ y in a..b, f (z,y))
        (∫ y in a..b, f₁ (x,y)) x := by
      intro x
      exact hasFDerivAt_intervalIntegral (fun x y => f (x,y))
        (fun x y => f₁ (x,y)) hf.continuous hf₁.continuous hdiff a b x
    rw [show (↑(n + 1) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
      contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hI x).differentiableAt, ?_, ?_⟩
    · simp
    · have heq : fderiv ℝ (fun z => ∫ y in a..b, f (z,y)) =
          (fun x => ∫ y in a..b, f₁ (x,y)) := funext fun x => (hI x).fderiv
      rw [heq]
      exact ih f₁ hf₁

theorem hasDerivAt_intervalIntegral
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f f₁ : ℝ → ℝ → F)
    (hf : Continuous (Function.uncurry f)) (hf₁ : Continuous (Function.uncurry f₁))
    (hd : ∀ x y, HasDerivAt (fun z => f z y) (f₁ x y) x)
    (a b x : ℝ) :
    HasDerivAt (fun z => ∫ y in a..b, f z y) (∫ y in a..b, f₁ x y) x := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod
    (show IsCompact (uIcc a b) from isCompact_uIcc)).exists_bound_of_continuousOn hf₁.continuousOn
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := f₁) (bound := fun _ => C) (s := Metric.closedBall x 1)
    (Metric.closedBall_mem_nhds x (by norm_num)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun z => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hf₁.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y hy z hz => hC (z, y) ⟨hz, uIoc_subset_uIcc hy⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun y _ z _ => hd z y

end SK.Analytic

noncomputable section
open MeasureTheory Set
open scoped Interval

end
end
end
end
end

end OAI
