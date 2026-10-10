import OAI.Probability.InvariantIsing.Gaussian.GaussianGramResidualBound

namespace OAI

/-! Boundedness and integrability of the finite transform-equation residual. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma continuous_gaussianGramResidual {N m : ℕ} {t : ℝ} (ht : 0 < t) (α : ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
      marchenkoPasturResidual t α (gaussianGramStieltjes t z)) := by
  have hu := continuous_gaussianGramStieltjes (N := N) (m := m) ht
  apply (continuous_const.sub (continuous_const.mul hu)).sub
  apply continuous_const.mul
  exact hu.div (continuous_const.add hu) (fun z => ne_of_gt (by
    have h := gaussianGramStieltjes_nonneg ht z
    linarith))

lemma gaussianGramResidual_abs_le {N m : ℕ} {t α : ℝ} (ht : 0 < t) (hα : 0 ≤ α)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    |marchenkoPasturResidual t α (gaussianGramStieltjes t z)| ≤ 1+α := by
  let u := gaussianGramStieltjes t z
  have hu : 0 ≤ u := gaussianGramStieltjes_nonneg ht z
  have hu1 : t*u ≤ 1 := by
    have h := (le_div_iff₀ ht).mp (gaussianGramStieltjes_le ht z)
    nlinarith
  have hf : 0 ≤ u/(1+u) := div_nonneg hu (by linarith)
  have hf1 : u/(1+u) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  change |1-t*u-α*(u/(1+u))| ≤ 1+α
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hf1 hα]
  · nlinarith [mul_nonneg ht.le hu,mul_nonneg hα hf]

lemma gaussianGramResidual_abs_integrable {N m : ℕ} {t α : ℝ} (ht : 0 < t) (hα : 0 ≤ α) :
    Integrable (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
      |marchenkoPasturResidual t α (gaussianGramStieltjes t z)|) (stdGaussian _) := by
  apply (integrable_const (1+α)).mono'
    (continuous_gaussianGramResidual ht α).abs.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_abs]
    exact gaussianGramResidual_abs_le ht hα z)

end InvariantIsing

end

end OAI
