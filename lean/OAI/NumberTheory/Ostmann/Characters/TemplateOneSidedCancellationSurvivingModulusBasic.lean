import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceRowsPair
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingExpressions

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template TemplateOneSidedCancellation
attribute [local instance] Classical.propDecidable
variable {ι κ α : Type*}

def SameResidueModuli (e : Expr ι) (f : Expr κ) : Prop :=
  e.denominator = f.denominator ∧ e.supportModulus = f.supportModulus

theorem sameResidueModuli_refl (e : Expr ι) : SameResidueModuli e e := ⟨rfl,rfl⟩

theorem expressionProduct_sameResidueModuli (xs : List α)
    (e : α → Expr ι) (f : α → Expr κ)
    (he : ∀i∈xs,SameResidueModuli (e i) (f i)) :
    SameResidueModuli (HistoryReconstruction.expressionProduct (xs.map e))
      (HistoryReconstruction.expressionProduct (xs.map f)) := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    have hx := he x List.mem_cons_self
    have ht := ih (fun i hi => he i (List.mem_cons_of_mem _ hi))
    constructor <;>
      simp only [List.map_cons,HistoryReconstruction.expressionProduct,
        Expr.denominator,Expr.supportModulus,hx.1,hx.2,ht.1,ht.2]

theorem finiteProductExpression_sameResidueModuli [Fintype α]
    (e : α → Expr ι) (f : α → Expr κ)
    (he : ∀i,SameResidueModuli (e i) (f i)) :
    SameResidueModuli (finiteProductExpression e) (finiteProductExpression f) := by
  have hh := expressionProduct_sameResidueModuli
    (List.ofFn (fun i : Fin (Fintype.card α) => (Fintype.equivFin α).symm i)) e f
    (fun i _ => he i)
  simpa only [finiteProductExpression,List.map_ofFn,Function.comp_def] using hh

theorem copiedExpression_sameResidueModuli (k j : ℕ) (b : Bool)
    (e : Expressions (ι:=ι) k (j+1)) (f : Expressions (ι:=κ) k (j+1))
    (he : ∀i,SameResidueModuli (e i) (f i)) :
    SameResidueModuli (copiedExpression k j b e) (copiedExpression k j b f) :=
  finiteProductExpression_sameResidueModuli _ _ (fun _ => he _)

theorem pivotExpression_sameResidueModuli (k j : ℕ)
    (e : Expressions (ι:=ι) k (j+1)) (f : Expressions (ι:=κ) k (j+1))
    (he : ∀i,SameResidueModuli (e i) (f i)) (s v w : ℤ) :
    SameResidueModuli (pivotExpression k j e s v w) (pivotExpression k j f s v w) := by
  have hl := copiedExpression_sameResidueModuli k j true e f he
  have hr := copiedExpression_sameResidueModuli k j false e f he
  constructor <;> simp only [pivotExpression,Expr.denominator,Expr.supportModulus,
    hl.1,hl.2,hr.1,hr.2]

theorem childExpressions_sameResidueModuli (k j : ℕ) (b : Bool)
    (e : Expressions (ι:=ι) k (j+1)) (f : Expressions (ι:=κ) k (j+1))
    (P : Expr ι) (Q : Expr κ) (he : ∀i,SameResidueModuli (e i) (f i))
    (hP : SameResidueModuli P Q) (i : (schedule k j).Slot) :
    SameResidueModuli (childExpressions k j b e P i) (childExpressions k j b f Q i) := by
  unfold childExpressions
  split
  · exact hP
  · split <;> exact he _

theorem residueGuard_modulus_congr (e : Expr ι) (f : Expr κ)
    (he : SameResidueModuli e f) (s : ℕ) :
    (ResidueGuard.mk e s).modulus = (ResidueGuard.mk f s).modulus := by
  simp only [ResidueGuard.modulus,he.1,he.2]

theorem rootResidueGuards_moduli_congr (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (f : Expressions (ι:=κ) k j)
    (he : ∀i,SameResidueModuli (e i) (f i)) :
    (rootResidueGuards k j s e).map ResidueGuard.modulus =
      (rootResidueGuards k j s f).map ResidueGuard.modulus := by
  simp only [rootResidueGuards,List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  exact residueGuard_modulus_congr _ _ (he _) _

theorem nodeResidueGuards_moduli_congr (k j : ℕ) (s v w : ℤ)
    (e : Expressions (ι:=ι) k (j+1)) (f : Expressions (ι:=κ) k (j+1))
    (he : ∀i,SameResidueModuli (e i) (f i)) :
    (nodeResidueGuards k j e s v w).map ResidueGuard.modulus =
      (nodeResidueGuards k j f s v w).map ResidueGuard.modulus := by
  simp only [nodeResidueGuards,List.map_cons,List.map_nil,
    residueGuard_modulus_congr _ _ (pivotExpression_sameResidueModuli k j e f he s v w),
    residueGuard_modulus_congr _ _ (copiedExpression_sameResidueModuli k j true e f he),
    residueGuard_modulus_congr _ _ (copiedExpression_sameResidueModuli k j false e f he)]

theorem historyResidueGuards_moduli_congr (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (f : Expressions (ι:=κ) k j)
    (he : ∀i,SameResidueModuli (e i) (f i)) (t : HistoryReconstruction.Tree j) :
    (historyResidueGuards k j s e t).map ResidueGuard.modulus =
      (historyResidueGuards k j s f t).map ResidueGuard.modulus := by
  induction j generalizing s with
  | zero => exact rootResidueGuards_moduli_congr k 0 s e f he
  | succ j ih =>
    have hp := pivotExpression_sameResidueModuli k j e f he s t.1.1 t.1.2
    simp only [historyResidueGuards,List.map_append]
    rw [rootResidueGuards_moduli_congr k (j+1) s e f he,
      nodeResidueGuards_moduli_congr k j s t.1.1 t.1.2 e f he,
      ih t.1.1 _ _ (childExpressions_sameResidueModuli k j true e f _ _ he hp),
      ih t.1.2 _ _ (childExpressions_sameResidueModuli k j false e f _ _ he hp)]

theorem historyResidueModulus_congr (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (f : Expressions (ι:=κ) k j)
    (he : ∀i,SameResidueModuli (e i) (f i)) (t : HistoryReconstruction.Tree j) :
    residueModulus (historyResidueGuards k j s e t) =
      residueModulus (historyResidueGuards k j s f t) :=
  congrArg List.prod (historyResidueGuards_moduli_congr k j s e f he t)

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
