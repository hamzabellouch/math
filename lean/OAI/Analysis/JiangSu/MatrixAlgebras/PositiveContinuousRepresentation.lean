import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.ContinuousPositiveEmbedding

namespace OAI


noncomputable section
namespace Pureness
open TraceCone
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
  obtain ⟨realNonneg, imaginaryZero⟩ := Complex.nonneg_iff.mp (F.2 x)
  change Complex.ofReal ((F.1 x).re.toNNReal : ℝ) = F.1 x
  rw [Real.coe_toNNReal (F.1 x).re realNonneg]
  apply Complex.ext
  · rfl
  · exact imaginaryZero

end Pureness
end

end OAI
