import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceBins
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalHeightSize
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalHeightTemplate

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template Preliminaries
variable {ι κ : Type*}

def sampledExpressions (k j : ℕ) (width : Role → ℕ) :
    Expressions (ι:=(schedule k j).Constituent width) k j := fun i=>
  finiteProductExpression (fun a : Fin (width ((schedule k j).role i))=>Expr.atom ⟨i,a⟩)

theorem sampledExpressions_eval (k j : ℕ) (width : Role → ℕ)
    (a : (schedule k j).Constituent width → ℤ) :
    evalExpressions a (sampledExpressions k j width) =
      fun i=>∏b : Fin (width ((schedule k j).role i)),a ⟨i,b⟩ := by
  funext i
  exact finiteProductExpression_eval _ a

theorem sampledExpressions_prime_eval (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (a : (schedule k j).Constituent width → PrimeUpTo Q) :
    evalExpressions (fun i=>(a i).val) (sampledExpressions k j width) =
      constituentSampleState (schedule k j) width a := sampledExpressions_eval k j width _

theorem sampledExpressions_good (k j : ℕ) (width : Role → ℕ)
    (a : (schedule k j).Constituent width → ℤ) (i : (schedule k j).Slot) :
    HistoryReconstruction.Good a (sampledExpressions k j width i) := by
  exact finiteProductExpression_good _ a (fun _=>⟨trivial,trivial⟩)

theorem expressionProduct_fixedBound (es : List (Expr ι)) {B : ℝ} (hB : 1 ≤ B)
    (he : ∀e∈es,e.FixedBound B) : (HistoryReconstruction.expressionProduct es).FixedBound B := by
  induction es with
  | nil => simpa only [HistoryReconstruction.expressionProduct,Expr.FixedBound,Int.cast_one,abs_one] using hB
  | cons e es ih => exact ⟨he e List.mem_cons_self,ih (fun q hq=>he q (List.mem_cons_of_mem _ hq))⟩

theorem finiteProductExpression_fixedBound {α : Type*} [Fintype α]
    (e : α → Expr ι) {B : ℝ} (hB : 1 ≤ B) (he : ∀i,(e i).FixedBound B) :
    (finiteProductExpression e).FixedBound B := by
  apply expressionProduct_fixedBound _ hB
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact he _

theorem sampledExpressions_fixedBound (k j : ℕ) (width : Role → ℕ) {B : ℝ}
    (hB : 1 ≤ B) (i : (schedule k j).Slot) :
    (sampledExpressions k j width i).FixedBound B :=
  finiteProductExpression_fixedBound _ hB (fun _=>trivial)

theorem sampledExpressions_syntaxSize (k j : ℕ) (width : Role → ℕ)
    (i : (schedule k j).Slot) :
    (sampledExpressions k j width i).syntaxSize ≤ 2*(width ((schedule k j).role i)+1) := by
  have hh := finiteProductExpression_syntaxSize
    (fun a : Fin (width ((schedule k j).role i))=>Expr.atom (ι:=(schedule k j).Constituent width) ⟨i,a⟩)
    1 (fun _=>le_rfl)
  simpa only [sampledExpressions,Fintype.card_fin,show 1+1=2 by rfl,Nat.mul_comm] using hh

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
