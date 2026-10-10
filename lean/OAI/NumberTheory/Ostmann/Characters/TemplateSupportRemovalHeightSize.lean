import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalHeightBasic

namespace OAI

namespace Ostmann.Characters.SymbolicHistory.Expr
variable {ι : Type*}

theorem degreeBudget_le_syntaxSize (e : Expr ι) : e.degreeBudget≤e.syntaxSize := by
  induction e with
  | atom i => simp [degreeBudget,syntaxSize]
  | fixed c => simp [degreeBudget,syntaxSize]
  | add a b ia ib => simp only [degreeBudget,syntaxSize]; omega
  | sub a b ia ib => simp only [degreeBudget,syntaxSize]; omega
  | mul a b ia ib => simp only [degreeBudget,syntaxSize]; omega
  | divide a d ia => simp only [degreeBudget,syntaxSize]; omega

end Ostmann.Characters.SymbolicHistory.Expr

end OAI
