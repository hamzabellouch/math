import OAI.NumberTheory.Ostmann.Characters.SymbolicHistoryResidues
import OAI.NumberTheory.Ostmann.Characters.TemplateActualPivotFactors
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetSampled

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template Preliminaries
attribute [local instance] Classical.propDecidable

def survivingPairedExpressions (k j : ℕ) (width : Role → ℕ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) :
    Expressions (ι:=SurvivingPrimeIndex k j width) k (j+1)
  | .inl (i,_) => finiteProductExpression
      (fun a : Fin (width ((schedule k j).role i.val)) => Expr.atom (.inl (e ⟨i,a⟩)))
  | .inr i => finiteProductExpression
      (fun a : Fin (width ((schedule k j).role i.val)) => Expr.atom (.inr ⟨i,a⟩))

def survivingSampledExpressions (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) :
    Expressions (ι:=SurvivingPrimeIndex k j width) k j :=
  childExpressions k j true (survivingPairedExpressions k j width e) (.fixed P)

theorem survivingPairedExpressions_eval (k j : ℕ) (width : Role → ℕ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (x : SurvivingPrimeIndex k j width → ℤ) :
    evalExpressions x (survivingPairedExpressions k j width e) =
      pairedState k j
        (fun i => ∏ a : Fin (width ((schedule k j).role i.val)),x (.inl (e ⟨i,a⟩)))
        (fun i => ∏ a : Fin (width ((schedule k j).role i.val)),x (.inl (e ⟨i,a⟩)))
        (fun i => ∏ a : Fin (width ((schedule k j).role i.val)),x (.inr ⟨i,a⟩)) := by
  funext i
  cases i with
  | inl z =>
    rcases z with ⟨i,b⟩
    cases b <;> simp only [evalExpressions,survivingPairedExpressions,pairedState,
      finiteProductExpression_eval,Expr.integerEval,ite_true,ite_false,Bool.false_eq_true]
  | inr i => simp only [evalExpressions,survivingPairedExpressions,pairedState,
      finiteProductExpression_eval,Expr.integerEval]

theorem survivingSampledExpressions_eval (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (x : SurvivingPrimeIndex k j width → ℤ) :
    evalExpressions x (survivingSampledExpressions k j width P e) =
      sourceState k j P
        (fun i => ∏ a : Fin (width ((schedule k j).role i.val)),x (.inl (e ⟨i,a⟩)))
        (fun i => ∏ a : Fin (width ((schedule k j).role i.val)),x (.inr ⟨i,a⟩)) := by
  rw [survivingSampledExpressions,childExpressions_eval,survivingPairedExpressions_eval]
  rfl

theorem survivingSampledExpressions_prime_eval (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) {Q : ℕ}
    (f : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) :
    evalExpressions (fun i => ((Sum.elim f y i).val:ℤ))
      (survivingSampledExpressions k j width P e) =
      sourceState k j P (copiedSampleState (schedule k j) j width (f ∘ e))
        (outsideSampleState (schedule k j) j width y) :=
  survivingSampledExpressions_eval k j width P e _

theorem survivingSampledExpressions_good (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (x : SurvivingPrimeIndex k j width → ℤ) (i : (schedule k j).Slot) :
    HistoryReconstruction.Good x (survivingSampledExpressions k j width P e i) := by
  apply childExpressions_preserves k j true _ (.fixed P) (HistoryReconstruction.Good x)
  · intro z
    cases z with
    | inl z =>
      exact finiteProductExpression_good
        (fun a : Fin (width ((schedule k j).role z.1.val)) =>
          Expr.atom (.inl (e ⟨z.1,a⟩))) x (fun _ => ⟨trivial,trivial⟩)
    | inr z =>
      exact finiteProductExpression_good
        (fun a : Fin (width ((schedule k j).role z.val)) =>
          Expr.atom (.inr ⟨z,a⟩)) x (fun _ => ⟨trivial,trivial⟩)
  · exact ⟨trivial,trivial⟩

def survivingCopiedProductExpression (k j : ℕ) (width : Role → ℕ) :
    Expr (SurvivingPrimeIndex k j width) :=
  finiteProductExpression
    (fun i : CopiedConstituent (schedule k j) j width => Expr.atom (.inl i))

theorem survivingCopiedProductExpression_eval (k j : ℕ) (width : Role → ℕ)
    (x : SurvivingPrimeIndex k j width → ℤ) :
    (survivingCopiedProductExpression k j width).integerEval x =
      ∏ i : CopiedConstituent (schedule k j) j width,x (.inl i) :=
  finiteProductExpression_eval _ x

theorem survivingCopiedProductExpression_prime_eval (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (f : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) :
    (survivingCopiedProductExpression k j width).integerEval
      (fun i => ((Sum.elim f y i).val:ℤ)) = ∏ i,(f i).val := by
  simpa only [Sum.elim_inl,Nat.cast_prod] using
    survivingCopiedProductExpression_eval k j width (fun i => ((Sum.elim f y i).val:ℤ))

theorem survivingCopiedProductExpression_good (k j : ℕ) (width : Role → ℕ)
    (x : SurvivingPrimeIndex k j width → ℤ) :
    HistoryReconstruction.Good x (survivingCopiedProductExpression k j width) :=
  finiteProductExpression_good _ x (fun _ => ⟨trivial,trivial⟩)

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
