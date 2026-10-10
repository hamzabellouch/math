import OAI.Probability.InvariantIsing.Gaussian.GaussianGramTransformError
import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternAspect

namespace OAI

/-! Convergence of the actual positive Gram transforms at every positive real argument. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

lemma gaussianGramTransform_error_bound_tendsto {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) :
    Tendsto (fun k : ℕ =>
      (((gaussianPatternCount α (k+1) : ℝ)/(k+1))*(Real.sqrt (2/((k+1 : ℝ)*t^2))+
        1/((k+1 : ℝ)*t))+|(gaussianPatternCount α (k+1) : ℝ)/(k+1)-α|)/t)
      atTop (𝓝 0) := by
  have hn : Tendsto (fun k : ℕ => (k+1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hq : Tendsto (fun k : ℕ => (2 : ℝ)/((k+1 : ℝ)*t^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hn.atTop_mul_const (sq_pos_of_pos ht))
  have hr : Tendsto (fun k : ℕ => (1 : ℝ)/((k+1 : ℝ)*t)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hn.atTop_mul_const ht)
  have hs := (Real.continuous_sqrt.tendsto 0).comp hq
  have ha := gaussianPatternCount_ratio_tendsto hα
  simpa only [Function.comp_def,Real.sqrt_zero,mul_zero,add_zero,zero_add,sub_self,abs_zero,zero_div] using
    ((ha.mul (hs.add hr)).add ((ha.sub (tendsto_const_nhds (x := α))).abs)).div_const t

theorem gaussianGramTransform_mean_tendsto {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) :
    Tendsto (fun k : ℕ => ∫ z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))),
      |gaussianGramStieltjes t z-marchenkoPasturTransform t α| ∂stdGaussian _) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _))
    (fun k => ?_) (gaussianGramTransform_error_bound_tendsto hα ht)
  simpa only [Nat.cast_add,Nat.cast_one] using gaussianGramTransform_mean_error
    (N := k+1) (m := gaussianPatternCount α (k+1)) (Nat.succ_pos k) ht hα

theorem gaussianPatternStieltjes_L1 {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    Tendsto (fun k : ℕ => ∫ ω, |gaussianGramStieltjes t (Z (k+1) ω)-marchenkoPasturTransform t α| ∂P)
      atTop (𝓝 0) := by
  have he (k : ℕ) : (∫ ω, |gaussianGramStieltjes t (Z (k+1) ω)-marchenkoPasturTransform t α| ∂P) =
      ∫ z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))),
        |gaussianGramStieltjes t z-marchenkoPasturTransform t α| ∂stdGaussian _ := by
    simpa only [Function.comp_def,Pi.sub_apply] using (hZ (k+1)).integral_comp
      (((continuous_gaussianGramStieltjes ht).sub continuous_const).abs.aestronglyMeasurable)
  simp_rw [he]
  exact gaussianGramTransform_mean_tendsto hα ht

end InvariantIsing

end

end OAI
