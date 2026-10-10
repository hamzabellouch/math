import OAI.Probability.InvariantIsing.Fields.VectorGaussianTransition
import OAI.Probability.InvariantIsing.Pressure.EntropyBudget

namespace OAI

/-! Entropy and future loss at one actual vector Gaussian transition. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

lemma vectorGaussianTransition_entropy_budget {N : ℕ} (hN : 0 < N)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (v : ℝ≥0)
    (F G : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hLF : HasLinearGrowth F) (hLG : HasLinearGrowth G)
    (hGF : ∀ z, G z ≤ F z) (z : Fin N → ℝ) :
    klDiv (vectorGaussianTransition N a v G hG z) (vectorGaussianTransition N a v F hF z) +
      (∫⁻ y, ENNReal.ofReal (F y - G y) ∂vectorGaussianTransition N a v G hG z) ≤
      ENNReal.ofReal (logMean a (vectorGaussianLaw N v : Measure (Fin N → ℝ))
        (fun w => F (z + w)) -
          logMean a (vectorGaussianLaw N v : Measure (Fin N → ℝ)) (fun w => G (z + w))) := by
  let μ := (vectorGaussianLaw N v : Measure (Fin N → ℝ))
  let f := fun w : Fin N → ℝ => z + w
  have hf : Measurable f := measurable_const.add measurable_id
  have heF := integrable_exp_of_linearGrowth μ (vectorGaussianLaw_moments hN v)
    (hF.comp hf) (hLF.add_left z) a
  have heG := integrable_exp_of_linearGrowth μ (vectorGaussianLaw_moments hN v)
    (hG.comp hf) (hLG.add_left z) a
  have hiF := integrable_linearGrowth_tilted μ (vectorGaussianLaw_moments hN v)
    (fun w => G (f w)) (fun w => F (f w)) (hG.comp hf) (hLG.add_left z)
    (hF.comp hf) (hLF.add_left z) a
  have hiG := integrable_linearGrowth_tilted μ (vectorGaussianLaw_moments hN v)
    (fun w => G (f w)) (fun w => G (f w)) (hG.comp hf) (hLG.add_left z)
    (hG.comp hf) (hLG.add_left z) a
  let _ : IsProbabilityMeasure (μ.tilted (fun w => a * F (f w))) :=
    isProbabilityMeasure_tilted heF
  let _ : IsProbabilityMeasure (μ.tilted (fun w => a * G (f w))) :=
    isProbabilityMeasure_tilted heG
  rw [vectorGaussianTransition_eq_map hN a v G hG hLG z,
    vectorGaussianTransition_eq_map hN a v F hF hLF z]
  exact (entropy_budget_map (μ.tilted (fun w => a * G (f w)))
    (μ.tilted (fun w => a * F (f w))) f hf
    (fun y => ENNReal.ofReal (F y - G y)) (hF.sub hG).ennreal_ofReal).trans
      (tilted_pair_entropy_budget_ennreal μ (fun w => F (f w)) (fun w => G (f w))
        ha ha1 heF heG (hiF.sub hiG) (fun w => hGF (f w)))

end InvariantIsing

end

end OAI
