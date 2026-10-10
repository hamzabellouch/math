import OAI.Probability.InvariantIsing.Gaussian.GaussianGramResidualMean

namespace OAI

/-! Quantitative mean convergence of the actual Gram resolvent to the MP equation's root. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma gaussianGramTransform_error_integrable {N m : ℕ} {t : ℝ} (ht : 0 < t) (α : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
      |gaussianGramStieltjes t z-marchenkoPasturTransform t α|) (stdGaussian _) := by
  apply (integrable_const (1/t+|marchenkoPasturTransform t α|)).mono'
    ((continuous_gaussianGramStieltjes ht).sub continuous_const).abs.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs,abs_abs]
  exact (abs_sub _ _).trans (add_le_add (by
    rw [abs_of_nonneg (gaussianGramStieltjes_nonneg ht z)]
    exact gaussianGramStieltjes_le ht z) le_rfl)

theorem gaussianGramTransform_mean_error {N m : ℕ} (hN : 0 < N) {t α : ℝ}
    (ht : 0 < t) (hα : 0 ≤ α) :
    (∫ z : EuclideanSpace ℝ (Fin N × Fin m),
      |gaussianGramStieltjes t z-marchenkoPasturTransform t α| ∂stdGaussian _) ≤
      (((m : ℝ)/N)*(Real.sqrt (2/((N : ℝ)*t^2))+1/((N : ℝ)*t))+|(m : ℝ)/N-α|)/t := by
  have hi := gaussianGramResidual_abs_integrable (N := N) (m := m) ht
    (show 0 ≤ (m : ℝ)/N by positivity)
  calc
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin N × Fin m),
        (|marchenkoPasturResidual t ((m : ℝ)/N) (gaussianGramStieltjes t z)|+|(m : ℝ)/N-α|)/t
        ∂stdGaussian _ := by
      apply integral_mono (gaussianGramTransform_error_integrable ht α)
        ((hi.add (integrable_const _)).div_const t)
      intro z
      apply (marchenkoPasturTransform_error ht hα (gaussianGramStieltjes_nonneg ht z)).trans
      apply div_le_div_of_nonneg_right _ ht.le
      dsimp only [Pi.add_apply]
      simpa only [abs_sub_comm α ((m : ℝ)/N)] using
        marchenkoPasturResidual_coefficient (t := t) (α := α) (β := (m : ℝ)/N)
          (gaussianGramStieltjes_nonneg ht z)
    _ = ((∫ z : EuclideanSpace ℝ (Fin N × Fin m),
        |marchenkoPasturResidual t ((m : ℝ)/N) (gaussianGramStieltjes t z)| ∂stdGaussian _)+
        |(m : ℝ)/N-α|)/t := by
      rw [integral_div,integral_add hi (integrable_const _)]
      simp
    _ ≤ _ := div_le_div_of_nonneg_right (add_le_add (gaussianGramResidual_mean_le hN ht) le_rfl) ht.le

end InvariantIsing

end

end OAI
