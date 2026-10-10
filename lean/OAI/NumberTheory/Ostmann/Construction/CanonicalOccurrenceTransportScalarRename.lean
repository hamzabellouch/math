import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightTree
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportRename

namespace OAI

noncomputable section

namespace Ostmann.Characters.RationalHistory.Expr
variable {ι κ : Type*}

@[simp] theorem realEval_rename (e : Expr ι) (f : ι → κ) (x : κ → ℝ) :
    (e.rename f).realEval x = e.realEval (x ∘ f) := by
  induction e <;> simp_all only [rename,realEval,Function.comp_apply]

@[simp] theorem realRegularAt_rename (e : Expr ι) (f : ι → κ) (x : κ → ℝ) :
    (e.rename f).RealRegularAt x ↔ e.RealRegularAt (x ∘ f) := by
  induction e <;> simp_all only [rename,RealRegularAt,realEval_rename]

end Ostmann.Characters.RationalHistory.Expr

namespace Ostmann.Arithmetic.HistorySymbolicState
open Construction Characters.RationalHistory
variable {ι κ : Type*}

def StateExpr.rename {a : State} (f : ι → κ) (e : StateExpr a ι) : StateExpr a κ :=
  ⟨e.plus.rename f,e.minus.rename f,fun i => (e.small i).rename f⟩

@[simp] theorem StateExpr.realPeriod_rename {a : State} (e : StateExpr a ι)
    (f : ι → κ) (outside : List ℕ) (x : κ → ℝ) :
    (e.rename f).realPeriod outside x = e.realPeriod outside (x ∘ f) := by
  simp only [realPeriod,rename,HistorySymbolicStep.product_realEval,List.map_ofFn,
    Function.comp_def,Expr.realEval_rename]

@[simp] theorem StateExpr.realScalar_rename {a : State} (e : StateExpr a ι)
    (f : ι → κ) (b s : ℕ) (X tb td : ℝ) (outside : List ℕ) (x : κ → ℝ) :
    (e.rename f).realScalar b s X tb td outside x =
      e.realScalar b s X tb td outside (x ∘ f) := by
  simp only [realScalar,realPeriod_rename]
  simp only [rename,Expr.realEval_rename]

end Ostmann.Arithmetic.HistorySymbolicState

namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState
variable {ι κ : Type*}

def renameTreeExpr (f : ι → κ) :
    {l : ℕ} → (h : History l) → TreeExpr ι h → TreeExpr κ h
  | _,.leaf _,e => e.rename f
  | _,.node _ _ _ _ _ left right,e =>
    (e.1.rename f,renameTreeExpr f left e.2.1,renameTreeExpr f right e.2.2)

@[simp] theorem treeRoot_renameTreeExpr (f : ι → κ) {l : ℕ} (h : History l)
    (e : TreeExpr ι h) :
    treeRoot h (renameTreeExpr f h e) = (treeRoot h e).rename f := by
  cases h <;> rfl

@[simp] theorem realHistoryScalar_renameTreeExpr (f : ι → κ)
    (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ) (x : κ → ℝ)
    {l : ℕ} (h : History l) (e : TreeExpr ι h) :
    realHistoryScalar b s X tb td G outside x h (renameTreeExpr f h e) =
      realHistoryScalar b s X tb td G outside (x ∘ f) h e := by
  induction h with
  | leaf a => exact e.realScalar_rename f b s X tb td outside x
  | node a p u hp hm left right ihl ihr =>
    simp only [realHistoryScalar,renameTreeExpr,treeRoot_renameTreeExpr,
      StateExpr.rename,Expr.realEval_rename,ihl,ihr]

end Ostmann.Arithmetic.HistorySymbolicEncoding

namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistorySymbolicState Arithmetic.HistorySymbolicEncoding
open Characters.RationalHistory
variable {ι κ : Type}

@[simp] theorem stateCode_rename {a : State} (f : ι → κ) (e : StateExpr a ι) :
    stateCode (e.rename f) = (stateCode e).rename f := by
  simp only [stateCode,StateExpr.rename,StateCode.rename,List.map_ofFn,Function.comp_def]

@[simp] theorem treeCode_renameTreeExpr (f : ι → κ) {l : ℕ} (h : History l)
    (e : TreeExpr ι h) :
    treeCode h (renameTreeExpr f h e) = renameTree f (treeCode h e) := by
  induction h with
  | leaf a => exact stateCode_rename f e
  | node a p u hp hm left right ihl ihr =>
    simp only [treeCode,renameTreeExpr,renameTree,stateCode_rename,ihl,ihr]

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
