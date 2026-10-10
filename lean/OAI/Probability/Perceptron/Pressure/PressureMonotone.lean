import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityTelescoping

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma normalizedPatternLog_mono (n M : ℕ) (f g : ℝ→ᵇℝ)
    (hfg : ∀ x : ℝ, f x≤g x) (a : Fin M→Fin (n+1)→ℝ) :
    normalizedPatternLog n M f a≤normalizedPatternLog n M g a := by
  have hm (f : ℝ→ᵇℝ) : Measurable (normalizedPatternEnergy (n+1) M f a) :=
    ((normalizedPatternEnergy_continuous (n+1) M f).comp
      (show Continuous (fun x : NormalizedSpin (n+1)=>(a,x)) from continuous_const.prodMk continuous_id)).measurable
  have hi (f : ℝ→ᵇℝ) : Integrable
      (fun x=>Real.exp (normalizedPatternEnergy (n+1) M f a x)) (unitSphereLaw (n+1)) := by
    apply Integrable.of_bound (hm f).exp.aestronglyMeasurable (Real.exp (M*‖f‖))
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (normalizedPatternEnergy_bound _ _ _ a x))
  apply Real.log_le_log
  · simpa only [tiltPartition,one_mul] using tilt_partition_pos (unitSphereLaw (n+1))
      (hm f) (by positivity : 0≤M*‖f‖) (normalizedPatternEnergy_bound _ _ _ a) 1
  · apply integral_mono (hi f) (hi g)
    intro x
    apply Real.exp_le_exp.mpr
    unfold normalizedPatternEnergy
    exact Finset.sum_le_sum (fun j _=>hfg _)

lemma expectedPressure_mono_terminal (α : ℝ) (f g : ℝ→ᵇℝ)
    (hfg : ∀ x : ℝ,f x≤g x) (n : ℕ) :
    expectedPressure α 1 f (n+1)≤expectedPressure α 1 g (n+1) := by
  unfold expectedPressure
  simp_rw [←normalizedPatternLog_source α 1 _ n,one_smul]
  rw [integral_const_mul,integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact integral_mono (normalizedPatternLog_integrable n _ f)
    (normalizedPatternLog_integrable n _ g) (normalizedPatternLog_mono n _ f g hfg)
end SphericalPerceptronFreeEnergy

end

end OAI
