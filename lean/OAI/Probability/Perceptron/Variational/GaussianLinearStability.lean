import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianMarkRecursion

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy
section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussianLinearBackward_bounded_difference {f g : E → ℝ} {L L' : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith L' g) {C : ℝ}
    (hC : ∀ x, |f x-g x| ≤ C)
    (l : List (ℝ×(E →L[ℝ] E))) (hl : ∀ c ∈ l, 0 ≤ c.1) (x : E) :
    |gaussianLinearBackward μ l f x-gaussianLinearBackward μ l g x| ≤ C := by
  induction l generalizing x with
  | nil => exact hC x
  | cons c l ih =>
    have hl' : ∀ d ∈ l, 0 ≤ d.1 := fun d hd => hl d (List.mem_cons_of_mem c hd)
    have hF := gaussianLinearBackward_lipschitz μ hf l hl'
    have hG := gaussianLinearBackward_lipschitz μ hg l hl'
    exact entropicMean_bounded_difference μ
      (fun a => gaussian_integrable_exp_linear_shift μ hF c.2 a x)
      (fun a => gaussian_integrable_exp_linear_shift μ hG c.2 a x)
      (hl c List.mem_cons_self) (ae_of_all _ fun y => ih hl' (x+c.2 y))
end

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussianLinearCascadeLog_mean_difference (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    {f g : E → ℝ} {L L' : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith L' g)
    {C : ℝ} (hC : ∀ x, |f x-g x| ≤ C)
    (k : ℕ) (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    let μ := (stdGaussian E).prod
      (decoratedCascadeLaw (gaussianMarkLaw : ProbabilityMeasure E) k z)
    |(∫ a, gaussianLinearCascadeLog A R f k a ∂μ)-
      (∫ a, gaussianLinearCascadeLog A R g k a ∂μ)| ≤ C := by
  dsimp only
  rw [(gaussianLinearCascadeLog_mean A R hf k z hz hz0 hz1).2,
    (gaussianLinearCascadeLog_mean A R hg k z hz hz0 hz1).2]
  have hi {h : E → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) :
      Integrable (fun a => gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) h (R a))
        (stdGaussian E) :=
    (lipschitz_memLp_stdGaussian ((gaussianLinearBackward_lipschitz (stdGaussian E) hh _
      (linearCascadeWord_nonneg A k z (fun i => (hz0 i).le))).comp R.lipschitzWith)).integrable (by norm_num)
  rw [← integral_sub (hi hf) (hi hg)]
  simpa using norm_integral_le_of_norm_le_const (μ := stdGaussian E)
    (f := fun a => gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) f (R a)-
      gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) g (R a))
    (C := C) (ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs] using
        gaussianLinearBackward_bounded_difference (stdGaussian E) hf hg hC _
          (linearCascadeWord_nonneg A k z (fun i => (hz0 i).le)) (R a))
end SphericalPerceptronFreeEnergy
end

end OAI
