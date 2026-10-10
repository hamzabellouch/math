import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationDegree
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationRatioData

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory TemplateSupportRemoval
variable {ι : Type*} [DecidableEq ι]

theorem ratioExpressionData_degreeCost (i : ι) (x : Other i → ℤ) (e : Expr ι)
    (T A B : ℝ) :
    (ratioExpressionData i x e T A B).degreeCost ≤ 6*e.syntaxSize+1 := by
  have hg (b : Bool) :
      ((ratioExpressionData i x e T A B).supports b).natDegree ≤ e.degreeBudget := by
    change (-((windowGuards e (Real.exp T*Real.exp (-B))
      (Real.exp T*Real.exp (-A)) false b).polynomial i x)).natDegree ≤ _
    rw [Polynomial.natDegree_neg]
    have hh := guard_degree_le (windowGuards e (Real.exp T*Real.exp (-B))
      (Real.exp T*Real.exp (-A)) false b) i x
    cases b <;> exact hh
  have ha := argument_degree_le i x e
  have hb := e.degreeBudget_le_syntaxSize
  simp only [HistoryPolynomialData.degreeCost,Fintype.sum_bool,Fintype.sum_unique]
  have h0 := hg false
  have h1 := hg true
  change 2*(((ratioExpressionData i x e T A B).supports true).natDegree +
    ((ratioExpressionData i x e T A B).supports false).natDegree+
    ((argument i x e).natDegree-1))+1 ≤ _
  omega

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
