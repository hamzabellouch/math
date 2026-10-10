import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.TargetLC
import OAI.Combinatorics.IndependentSets.Reduction.TargetRead

namespace OAI

namespace LargeIndependentSets.TargetLC
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame UniformLC
open TargetRead TargetRepair
open scoped Classical BigOperators
noncomputable section
variable (u : ℕ)

def eventExpr (x : Expr) (k : Fin u) : Expr :=
  Expr.remainder (Expr.quotient x (Expr.power (.mul clausesExpr (.const 3)) k.val))
    (.mul clausesExpr (.const 3))
def clauseExpr (x : Expr) (k : Fin u) : Expr := Expr.quotient (eventExpr u x k) (.const 3)
def slotExpr (x : Expr) (k : Fin u) : Expr := Expr.remainder (eventExpr u x k) (.const 3)

lemma clauseExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) (k : Fin u) :
    (clauseExpr u x k).eval (Complexity.formulaBits F.val) a=
      (((eventEquiv u F.val).symm i k).1).val := by
  simp only [clauseExpr,eventExpr,Expr.remainder_eval,Expr.quotient_eval,Expr.power_eval,
    Expr.eval,clausesExpr_eval,hi]
  rfl

lemma slotExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) (k : Fin u) :
    (slotExpr u x k).eval (Complexity.formulaBits F.val) a=
      (RawInitialTables.slotOrder (((eventEquiv u F.val).symm i k).2)).val := by
  simp only [slotExpr,eventExpr,Expr.remainder_eval,Expr.quotient_eval,Expr.power_eval,
    Expr.eval,clausesExpr_eval,hi]
  change _=(RawInitialTables.slotOrder (RawInitialTables.slotOrder.symm _)).val
  rw [Equiv.apply_symm_apply]
  rfl

def sampledNameExpr (x : Expr) (k : Fin u) : Expr :=
  selectSlot (slotExpr u x k) (nameExpr (clauseExpr u x k))
def projectedBitExpr (x : Expr) (j : J u) (k : Fin u) : Expr :=
  selectSlot (slotExpr u x k) (repairExpr (clauseExpr u x k) (j k))

lemma sampledNameExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) (k : Fin u) :
    (sampledNameExpr u x k).eval (Complexity.formulaBits F.val) a=
      (nameAt (clauseAt F.val (((eventEquiv u F.val).symm i k).1))
        (((eventEquiv u F.val).symm i k).2)).val := by
  rw [sampledNameExpr,selectSlot_eval _ _ _ _ _ (slotExpr_eval u F x a i hi k)]
  exact nameExpr_eval F.val _ a _ (clauseExpr_eval u F x a i hi k) _

lemma projectedBitExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) (j : J u) (k : Fin u) :
    (projectedBitExpr u x j k).eval (Complexity.formulaBits F.val) a=
      bit ((table u F).project i j k) := by
  rw [projectedBitExpr,selectSlot_eval _ _ _ _ _ (slotExpr_eval u F x a i hi k)]
  rw [repairExpr_eval _ _ _ _ (clauseExpr_eval u F x a i hi k)]
  congr 1
  exact (project_apply u F.val _ j k).symm

def rankExpr (base : Expr) (f : Fin u → Expr) : Expr :=
  Expr.listSum (List.finRange u) (fun k => .mul (f k) (Expr.power base k.val))
lemma rankExpr_eval (s : List Bool) (a : ℕ → ℕ) (base : Expr) (f : Fin u → Expr)
    {m : ℕ} (v : Fin u → Fin m) (hb : base.eval s a=m) (hf : ∀ k, (f k).eval s a=(v k).val) :
    (rankExpr u base f).eval s a=(finFunctionFinEquiv v).val := by
  simp only [rankExpr,Expr.listSum_eval,Expr.eval,Expr.power_eval,hb,hf,finFunctionFinEquiv_apply]
  rw [← List.ofFn_eq_map,List.sum_ofFn]

def leftExpr (x : Expr) : Expr := rankExpr u clausesExpr (clauseExpr u x)
def rightExpr (x : Expr) : Expr := rankExpr u varsExpr (sampledNameExpr u x)
lemma leftExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) :
    (leftExpr u x).eval (Complexity.formulaBits F.val) a=((table u F).left i).val := by
  exact rankExpr_eval u _ _ _ _ _ (clausesExpr_eval F.val a) (clauseExpr_eval u F x a i hi)
lemma rightExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) :
    (rightExpr u x).eval (Complexity.formulaBits F.val) a=((table u F).right i).val := by
  exact rankExpr_eval u _ _ _ _ _ (varsExpr_eval F.val a) (sampledNameExpr_eval u F x a i hi)

def projectionTest (x : Expr) (f : J u → I u) : Expr :=
  Expr.listAll (List.finRange (Fintype.card (J u))) fun i =>
    Expr.listAll (List.finRange u) fun k =>
      Expr.equal (projectedBitExpr u x ((Fintype.equivFin (J u)).symm i) k)
        (.const (bit (f ((Fintype.equivFin (J u)).symm i) k)))
lemma projectionTest_nonzero (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) (f : J u → I u) :
    (projectionTest u x f).eval (Complexity.formulaBits F.val) a≠0 ↔ f=(table u F).project i := by
  simp only [projectionTest,Expr.listAll_eval,List.mem_finRange,forall_true_left,
    Expr.equal_eval,projectedBitExpr_eval u F x a i hi,Expr.eval,indicator_ne,bit_eq]
  constructor
  · intro h
    funext j k
    simpa using (h (Fintype.equivFin (J u) j) k).symm
  · rintro rfl
    exact fun _ _ => rfl

def projectExpr (x : Expr) : Expr := Expr.pick projectCode (projectionTest u x)
lemma projectExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) :
    (projectExpr u x).eval (Complexity.formulaBits F.val) a=projectCode ((table u F).project i) := by
  apply Expr.pick_eval
  exact projectionTest_nonzero u F x a i hi

end
end LargeIndependentSets.TargetLC

end OAI
