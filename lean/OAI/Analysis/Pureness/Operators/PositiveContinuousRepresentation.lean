import OAI.Analysis.Pureness.Operators.ContinuousPositiveEmbedding
import OAI.Analysis.Pureness.Operators.StarHomOrderReflection

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem continuousNNRealPositive_surjective : Function.Surjective (continuousNNRealPositive (X := X)) := by
  intro F
  let f : C(X, ℝ≥0) := ⟨fun x => (F.1 x).re.toNNReal,
    continuous_real_toNNReal.comp (Complex.continuous_re.comp F.1.continuous)⟩
  refine ⟨f,?_⟩
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  have h : 0 ≤ (F.1 x).re ∧ 0 = (F.1 x).im := Complex.nonneg_iff.mp (F.2 x)
  change Complex.ofReal ((F.1 x).re.toNNReal : ℝ) = F.1 x
  rw [Real.coe_toNNReal _ h.1]
  apply Complex.ext
  · rfl
  · exact h.2
end CuntzPureness

end

end OAI
