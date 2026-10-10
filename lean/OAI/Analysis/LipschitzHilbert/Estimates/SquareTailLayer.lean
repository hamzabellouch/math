import OAI.Analysis.LipschitzHilbert.Estimates.WeightedDilationLayer

namespace OAI

/-! The weighted layer-cake estimate in the product form produced by
the covering inequality. All weights are the actual top areas. -/

noncomputable section
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

theorem weighted_layer_from_square_tail {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (K : ℝ) (hK : 0 < K) (hS : 0 < ∑ i, (w i : ℝ))
    (htail : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t^2)*(∑ i, if t<a i then (w i:ℝ≥0∞) else 0) ≤
        ENNReal.ofReal (K^2)) :
    (∑ i, (w i:ℝ≥0∞)*ENNReal.ofReal (a i)) ≤
      ENNReal.ofReal (2*K*Real.sqrt (∑ i, (w i:ℝ))) := by
  apply weighted_layer_from_weak_tail w a ha K hK hS
  intro t ht
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos ht)]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  simpa only [mul_comm] using htail t ht

end LipschitzHilbert

end

end OAI
