import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceHalfMean
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationGuards

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template Construction Preliminaries
attribute [local instance] Classical.propDecidable

def sourceWordExpression (m nc : ℕ) : Expr (Fin ((m+1)+nc)) :=
  finiteProductExpression (fun i : Fin (m+1) => Expr.atom (i.castAdd nc))

theorem sourceWordExpression_eval {Q m nc : ℕ}
    (w : Fin ((m+1)+nc) → PrimeUpTo Q) :
    (sourceWordExpression m nc).integerEval (fun i => ((w i).val:ℤ)) =
      ∏ i : Fin (m+1), ((w (i.castAdd nc)).val:ℤ) := by
  rw [sourceWordExpression,finiteProductExpression_eval]
  rfl

theorem sourceWordExpression_pos {Q m nc : ℕ}
    (w : Fin ((m+1)+nc) → PrimeUpTo Q) :
    0 < ((sourceWordExpression m nc).integerEval (fun i => ((w i).val:ℤ)):ℝ) := by
  rw [sourceWordExpression_eval,Int.cast_prod]
  exact Finset.prod_pos (fun i _ => by exact_mod_cast (primeUpTo_prime (w (i.castAdd nc))).pos)

theorem sourceWordExpression_log {Q m nc : ℕ}
    (w : Fin ((m+1)+nc) → PrimeUpTo Q) :
    Real.log ((sourceWordExpression m nc).integerEval (fun i => ((w i).val:ℤ)):ℝ) =
      HigherBiasSourceWord.wordLog (HigherBiasSourceRoleBounds.originalWord w) := by
  rw [sourceWordExpression_eval,Int.cast_prod,Real.log_prod]
  · rfl
  · intro i hi
    exact (show (0:ℝ) < ((w (i.castAdd nc)).val:ℤ) by
      exact_mod_cast (primeUpTo_prime (w (i.castAdd nc))).pos).ne'

theorem sourceHalfMask_eq_guards {Q m nc : ℕ} (J : ℤ)
    (w : Fin ((m+1)+nc) → PrimeUpTo Q) :
    HigherBiasSource.sourceHalfMask J w =
      if ∀ b, (binGuards (sourceWordExpression m nc) J b).holds (fun i => ((w i).val:ℤ))
      then 1 else 0 := by
  unfold HigherBiasSource.sourceHalfMask HigherBiasSourceWord.binIndicator
  simp only [binGuards_holds_iff _ _ _ (sourceWordExpression_pos w),sourceWordExpression_log]

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
