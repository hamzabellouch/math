import OAI.Analysis.Pureness.Completion.CompletedTraceTracial

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completedTraceValue_smul (τ : TracialState A) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) (a : CornerCompletion A) :
    completedTraceValue τ k (s • a) = ENNReal.ofReal s * completedTraceValue τ k a := by
  change ENNReal.ofReal (matrixTrace τ (completedCompressLinear k (s • a))).re = _
  rw [(completedCompressLinear (A := A) k).map_smul_of_tower, (matrixTrace τ).map_smul_of_tower,
    Complex.smul_re, smul_eq_mul, ENNReal.ofReal_mul hs]
  rfl

lemma completedDiagonalWeight_smul (τ : TracialState A) (s : ℝ) (hs : 0 ≤ s) (a : CornerCompletion A) :
    completedDiagonalWeight τ (s • a) = ENNReal.ofReal s * completedDiagonalWeight τ a := by
  simp only [completedDiagonalWeight, completedTraceValue_smul τ _ s hs, ENNReal.mul_iSup]

@[simp] lemma completedDiagonalWeight_zero (τ : TracialState A) : completedDiagonalWeight τ 0 = 0 := by
  have h := completedDiagonalWeight_smul τ 0 le_rfl (0 : CornerCompletion A)
  simpa only [zero_smul, ENNReal.ofReal_zero, zero_mul] using h
end CuntzPureness

end

end OAI
