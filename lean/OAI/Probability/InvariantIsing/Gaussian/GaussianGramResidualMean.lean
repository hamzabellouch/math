import OAI.Probability.InvariantIsing.Gaussian.GaussianColumnDeviationMean
import OAI.Probability.InvariantIsing.Gaussian.GaussianGramResidualIntegrability

namespace OAI

/-! An explicit mean error bound for the actual Gaussian Gram transform equation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing

lemma gaussianGramColumnDeviation_mean_le_all {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (j : Fin m) :
    (∫ g : Fin m → Fin N → ℝ, gaussianGramColumnDeviation t (gaussianColumnArray g) j
      ∂Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1))) ≤
      Real.sqrt (2/((N : ℝ)*t^2)) := by
  cases m with
  | zero => exact Fin.elim0 j
  | succ m => exact gaussianGramColumnDeviation_mean_le hN ht j

theorem gaussianGramResidual_mean_le {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    (∫ z : EuclideanSpace ℝ (Fin N × Fin m),
      |marchenkoPasturResidual t ((m : ℝ)/N) (gaussianGramStieltjes t z)| ∂stdGaussian _) ≤
      ((m : ℝ)/N)*(Real.sqrt (2/((N : ℝ)*t^2))+1/((N : ℝ)*t)) := by
  let μ := Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1))
  have hi (j : Fin m) : Integrable (fun g : Fin m → Fin N → ℝ =>
      gaussianGramColumnDeviation t (gaussianColumnArray g) j+1/((N : ℝ)*t)) μ :=
    (gaussianGramColumnDeviation_integrable hN ht j).add (integrable_const _)
  have hf := (gaussianColumnArray_hasLaw N m).integrable_comp
    (gaussianGramResidual_abs_integrable ht (show 0 ≤ (m : ℝ)/N by positivity))
  have hμ : IsProbabilityMeasure μ := inferInstance
  rw [← (gaussianColumnArray_hasLaw N m).integral_comp
    (continuous_gaussianGramResidual ht ((m : ℝ)/N)).abs.aestronglyMeasurable]
  calc
    _ ≤ ∫ g, (1/(N : ℝ))*∑ j : Fin m,
        (gaussianGramColumnDeviation t (gaussianColumnArray g) j+1/((N : ℝ)*t)) ∂μ := by
      apply integral_mono hf ((integrable_finsetSum Finset.univ (fun j _ => hi j)).const_mul _)
      intro g
      exact gaussianGramResidual_bound hN ht (gaussianColumnArray g)
    _ = (1/(N : ℝ))*∑ j : Fin m, ∫ g,
        (gaussianGramColumnDeviation t (gaussianColumnArray g) j+1/((N : ℝ)*t)) ∂μ := by
      rw [integral_const_mul,integral_finsetSum _ (fun j _ => hi j)]
    _ ≤ (1/(N : ℝ))*∑ _ : Fin m, (Real.sqrt (2/((N : ℝ)*t^2))+1/((N : ℝ)*t)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      rw [integral_add (gaussianGramColumnDeviation_integrable hN ht j) (integrable_const _)]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
      exact add_le_add (gaussianGramColumnDeviation_mean_le_all hN ht j) le_rfl
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end InvariantIsing

end

end OAI
