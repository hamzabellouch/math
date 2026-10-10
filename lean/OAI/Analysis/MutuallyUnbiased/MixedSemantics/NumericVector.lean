import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.KeyMap
import OAI.Analysis.MutuallyUnbiased.PairMoments.PairAverage

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

/-- The actual 3237 coordinates used by the mixed numerical certificate. -/
def numericVector (B : Fin 7 → Basis) : Fin 3237 → ℝ := mixedVector B ∘ keyMap

theorem numericVector_abs_le_one (B : Fin 7 → Basis) (hB : IsMUBFamily B) (i : Fin 3237) :
    |numericVector B i| ≤ 1 := mixedVector_abs_le_one B hB (keyMap i)

theorem numericVector_zero (B : Fin 7 → Basis) : numericVector B 0 = 1 := by
  change familyPairVector B 0 = 1
  have h (H : CMatrix) : PairSemantics.momentVector H 0 = 1 := by
    change injectiveMoment H (0 : Matrix (Fin 0) (Fin 0) ℤ) = 1
    exact injectiveMoment_empty H
  unfold familyPairVector familyAverage
  simp only [h, average_const]

theorem eval_numericVector (B : Fin 7 → Basis) (v : Sparse (Fin 3237)) :
    Sparse.eval v (numericVector B) = Sparse.eval (Sparse.reindex keyMap v) (mixedVector B) := by
  rw [Sparse.eval_reindex]
  rfl

theorem integer_eval_numericVector (B : Fin 7 → Basis) (v : Integer.Sparse (Fin 3237)) :
    Integer.Sparse.eval v (numericVector B) =
      Integer.Sparse.eval (Integer.Sparse.reindex keyMap v) (mixedVector B) := by
  rw [Integer.Sparse.eval_reindex]
  rfl

end MUB6.Certificate.MixedSemantics

end

end OAI
