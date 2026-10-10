import Mathlib
import OAI.Analysis.LaughlinGap.IntegerFourRows

namespace OAI

/-! Cached Integer Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators

def integerTableEval (D : ℕ) (S : Fin ((D+1)/2) → Fin 8 → Fin 9 → Fin 9 → ℤ)
    (u v : Fin ((D+1)/2)) : ℚ :=
  ((-(∑ a : Fin 8, ∑ i : Fin 9, ∑ k : Fin 9, fourRowWeight D a i k *
    S u a i k * S v a k i):ℤ):ℚ) / fourMatrixDenominator D

lemma exactFourEval_table (D : ℕ) (S : Fin ((D+1)/2) → Fin 8 → Fin 9 → Fin 9 → ℤ)
    (hS : ∀ u a i k, fourSumInteger a D (2*u.val+1) i k = S u a i k)
    (u v : Fin ((D+1)/2)) :
    exactFourEval D (2*u.val+1) (2*v.val+1) = integerTableEval D S u v := by
  simp only [exactFourEval,exactFourInteger,integerTableEval,hS]

end LaughlinGap.RealOccupation

end

end OAI
