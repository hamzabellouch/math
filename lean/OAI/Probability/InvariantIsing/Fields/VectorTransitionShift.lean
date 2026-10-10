import OAI.Probability.InvariantIsing.Fields.VectorGaussianTransition

namespace OAI

/-! Translation covariance of the actual Gaussian transition when the
backward potential changes by a constant. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma tilted_add_constant {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Integrable (fun x => Real.exp (f x)) μ)
    (c : ℝ) : μ.tilted (fun x => f x + c) = μ.tilted f := by
  let _ := isProbabilityMeasure_tilted hf
  exact (tilted_tilted hf (fun _ => c)).symm.trans (tilted_const _ c)

lemma vectorGaussianTransition_shift {N : ℕ} (hN : 0 < N) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (d : Fin N → ℝ) (c : ℝ) (hshift : ∀ z, F (z + d) = F z + c) (z : Fin N → ℝ) :
    vectorGaussianTransition N a v F hF (z + d) =
      (vectorGaussianTransition N a v F hF z).map (fun y => y + d) := by
  rw [vectorGaussianTransition_eq_map hN a v F hF hG (z + d),
    vectorGaussianTransition_eq_map hN a v F hF hG z,
    Measure.map_map (f := fun w : Fin N → ℝ => z + w) (g := fun y => y + d)
      (measurable_id.add_const d) (measurable_const.add measurable_id)]
  have he : (fun w => a * F (z + d + w)) = fun w => a * F (z + w) + a * c := by
    funext w
    rw [show z + d + w = (z + w) + d by abel, hshift, mul_add]
  rw [he, tilted_add_constant (vectorGaussianLaw N v : Measure (Fin N → ℝ))
    (fun w => a * F (z + w))
    (integrable_exp_of_linearGrowth (vectorGaussianLaw N v : Measure (Fin N → ℝ))
      (vectorGaussianLaw_moments hN v) (hF.comp (measurable_const.add measurable_id))
      (hG.add_left z) a) (a * c)]
  congr 1
  funext w
  dsimp only [Function.comp_apply]
  abel

end InvariantIsing

end

end OAI
