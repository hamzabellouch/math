import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.ExprTables

namespace OAI

noncomputable section

namespace LargeIndependentSets.TargetRead
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame
open scoped Classical BigOperators

lemma encodeWords_eq (xs : List ℕ) : encodeWords xs=Expr.unaryWords xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords,encodeWord,Expr.unaryWords,ih]

lemma read (F : Target.Formula) (w : ℕ) :
    Expr.wordValue (Complexity.formulaBits F) w=((formulaWords F)[w]?).getD 0 := by
  rw [Complexity.formulaBits,encodeWords_eq,Expr.wordValue_encoded]

lemma block_get {α β : Type} (d : β) (f : α → List β) (k : ℕ) (hl : ∀ x, (f x).length=k)
    (xs : List α) (c : Fin xs.length) (j : ℕ) (hj : j<k) :
    ((xs.flatMap f)[k*c.val+j]?).getD d=((f xs[c])[j]?).getD d := by
  induction xs with
  | nil => exact Fin.elim0 c
  | cons x xs ih =>
    rcases c with ⟨c,hc⟩
    cases c with
    | zero =>
      simp only [List.flatMap_cons,Nat.mul_zero,Nat.zero_add]
      rw [List.getElem?_append_left (by simpa [hl] using hj)]
      rfl
    | succ c =>
      have hc' : c<xs.length := by simpa using hc
      simp only [List.flatMap_cons,Nat.mul_succ]
      rw [List.getElem?_append_right (by rw [hl]; omega),hl]
      have he : k*c+k+j-k=k*c+j := by omega
      rw [he]
      exact ih ⟨c,hc'⟩

lemma read_vars (F : Target.Formula) : Expr.wordValue (Complexity.formulaBits F) 0=F.«variables» := by
  rw [read]; simp [formulaWords]
lemma read_clauses (F : Target.Formula) : Expr.wordValue (Complexity.formulaBits F) 1=F.clauses.length := by
  rw [read]; simp [formulaWords]

lemma read_clause (F : Target.Formula) (c : Fin F.clauses.length) (j : Fin 6) :
    Expr.wordValue (Complexity.formulaBits F) (2+6*c.val+j.val)=
      ((clauseWords (clauseAt F c))[j.val]?).getD 0 := by
  rw [read,formulaWords,List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [show 2+6*c.val+j.val-2=6*c.val+j.val by omega]
  exact block_get 0 clauseWords 6 clauseWords_length F.clauses c j.val j.isLt

lemma read_name (F : Target.Formula) (c : Fin F.clauses.length) (s : Slot) :
    Expr.wordValue (Complexity.formulaBits F) (2+6*c.val+2*(RawInitialTables.slotOrder s).val)=
      (nameAt (clauseAt F c) s).val := by
  have h := read_clause F c ⟨2*(RawInitialTables.slotOrder s).val,by have := (RawInitialTables.slotOrder s).isLt; omega⟩
  cases s <;> simpa [RawInitialTables.slotOrder,clauseWords,literalWords,nameAt] using h

def signAt {n : ℕ} (cl : Target.Clause n) : Slot → Bool
  | .first => cl[0].positive
  | .second => cl[1].positive
  | .third => cl[2].positive

lemma read_sign (F : Target.Formula) (c : Fin F.clauses.length) (s : Slot) :
    Expr.wordValue (Complexity.formulaBits F) (2+6*c.val+(2*(RawInitialTables.slotOrder s).val+1))=
      (if signAt (clauseAt F c) s then 1 else 0) := by
  have h := read_clause F c ⟨2*(RawInitialTables.slotOrder s).val+1,by have := (RawInitialTables.slotOrder s).isLt; omega⟩
  cases s <;> convert h using 1 <;> simp [RawInitialTables.slotOrder,clauseWords,literalWords,signAt] <;> rfl

def varsExpr : Expr := Expr.word (.const 0)
def clausesExpr : Expr := Expr.word (.const 1)
def nameExpr (c : Expr) (s : Slot) : Expr :=
  Expr.word (.add (.add (.const 2) (.mul (.const 6) c)) (.const (2*(RawInitialTables.slotOrder s).val)))
def signExpr (c : Expr) (s : Slot) : Expr :=
  Expr.word (.add (.add (.const 2) (.mul (.const 6) c)) (.const (2*(RawInitialTables.slotOrder s).val+1)))

@[simp] lemma varsExpr_eval (F : Target.Formula) (a : ℕ → ℕ) :
    varsExpr.eval (Complexity.formulaBits F) a=F.«variables» := by simp [varsExpr,Expr.eval,read_vars]
@[simp] lemma clausesExpr_eval (F : Target.Formula) (a : ℕ → ℕ) :
    clausesExpr.eval (Complexity.formulaBits F) a=F.clauses.length := by simp [clausesExpr,Expr.eval,read_clauses]
lemma nameExpr_eval (F : Target.Formula) (c : Expr) (a : ℕ → ℕ) (i : Fin F.clauses.length)
    (hi : c.eval (Complexity.formulaBits F) a=i.val) (s : Slot) :
    (nameExpr c s).eval (Complexity.formulaBits F) a=(nameAt (clauseAt F i) s).val := by
  simp only [nameExpr,Expr.word_eval,Expr.eval,hi,read_name]
lemma signExpr_eval (F : Target.Formula) (c : Expr) (a : ℕ → ℕ) (i : Fin F.clauses.length)
    (hi : c.eval (Complexity.formulaBits F) a=i.val) (s : Slot) :
    (signExpr c s).eval (Complexity.formulaBits F) a=if signAt (clauseAt F i) s then 1 else 0 := by
  simp only [signExpr,Expr.word_eval,Expr.eval,hi,read_sign]

end LargeIndependentSets.TargetRead
namespace LargeIndependentSets.TargetRepair
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame
open TargetRead
open scoped Classical BigOperators

def bit (b : Bool) : ℕ := if b then 1 else 0
@[simp] lemma bit_eq (b c : Bool) : bit b=bit c ↔ b=c := by cases b <;> cases c <;> decide
lemma bit_decide (p : Prop) [Decidable p] : bit (decide p)=(if p then 1 else 0) := by
  by_cases h : p <;> simp [bit,h]
@[simp] lemma bit_ne_zero (b : Bool) : bit b≠0 ↔ b=true := by cases b <;> decide

abbrev Shape := (Slot → Bool) × (Slot → Slot → Bool)
def shape {n : ℕ} (cl : Target.Clause n) : Shape :=
  (signAt cl,fun s t => decide (nameAt cl s=nameAt cl t))
def shapeSat (sh : Shape) (j : ClauseAnswer) : Bool :=
  (literalValue (sh.1 .first) j.first || literalValue (sh.1 .second) j.second) ||
    literalValue (sh.1 .third) j.third
def shapeCons (sh : Shape) (j : ClauseAnswer) : Bool :=
  decide (∀ s t, sh.2 s t=true → answerAt j s=answerAt j t)
def repairedBit (sh : Shape) (j : ClauseAnswer) (s : Slot) : Bool :=
  if shapeSat sh j=true ∧ shapeCons sh j=true then answerAt j s
  else if sh.2 s .first then sh.1 .first else false

lemma shapeSat_exact {n : ℕ} (cl : Target.Clause n) (j : ClauseAnswer) :
    shapeSat (shape cl) j=localSatisfies cl j := rfl
lemma shapeCons_exact {n : ℕ} (cl : Target.Clause n) (j : ClauseAnswer) :
    shapeCons (shape cl) j=localConsistent cl j := by
  simp only [shapeCons,shape,localConsistent,decide_eq_true_eq]
lemma repairedBit_exact {n : ℕ} (cl : Target.Clause n) (j : ClauseAnswer) (s : Slot) :
    repairedBit (shape cl) j s=answerAt (LCInput.repair cl j) s := by
  simp only [repairedBit,shapeSat_exact,shapeCons_exact,LCInput.repair]
  by_cases h : localSatisfies cl j=true ∧ localConsistent cl j=true
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]
    rw [LCInput.fallback,honest_answerAt]
    change (if decide (nameAt cl s=cl[0].variableIndex) then cl[0].positive else false)=_
    by_cases hn : nameAt cl s=cl[0].variableIndex
    · rw [ite_eq_left (by simpa only [decide_eq_true_eq] using hn),ite_eq_left hn]
    · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hn),ite_eq_right hn]

lemma indicator_ne (p : Prop) [Decidable p] : (if p then (1:ℕ) else 0)≠0 ↔ p := by
  by_cases h : p <;> simp [h]

def shapeTest (c : Expr) (sh : Shape) : Expr :=
  .mul
    (Expr.listAll (List.finRange 3) fun i =>
      Expr.equal (signExpr c (RawInitialTables.slotOrder.symm i))
        (.const (bit (sh.1 (RawInitialTables.slotOrder.symm i)))))
    (Expr.listAll (List.finRange 3) fun i =>
      Expr.listAll (List.finRange 3) fun j =>
        Expr.equal
          (Expr.equal (nameExpr c (RawInitialTables.slotOrder.symm i))
            (nameExpr c (RawInitialTables.slotOrder.symm j)))
          (.const (bit (sh.2 (RawInitialTables.slotOrder.symm i) (RawInitialTables.slotOrder.symm j)))))

lemma shapeTest_nonzero (F : Target.Formula) (c : Expr) (a : ℕ → ℕ) (i : Fin F.clauses.length)
    (hi : c.eval (Complexity.formulaBits F) a=i.val) (sh : Shape) :
    (shapeTest c sh).eval (Complexity.formulaBits F) a≠0 ↔ sh=shape (clauseAt F i) := by
  have hs (s : Slot) := signExpr_eval F c a i hi s
  have hn (s : Slot) := nameExpr_eval F c a i hi s
  simp only [shapeTest,Expr.eval,Expr.listAll_eval,Expr.equal_eval,hs,hn,List.mem_finRange,
    forall_true_left,Nat.mul_ne_zero_iff,indicator_ne,Fin.val_inj]
  simp only [← bit_decide,bit_eq,Bool.decide_coe]
  constructor
  · rintro ⟨hs,hn⟩
    apply Prod.ext
    · funext s
      change sh.1 s=signAt (clauseAt F i) s
      simpa using (hs (RawInitialTables.slotOrder s)).symm
    · funext s t
      simpa [shape] using (hn (RawInitialTables.slotOrder s) (RawInitialTables.slotOrder t)).symm
  · rintro rfl
    exact ⟨fun _ => rfl,fun _ _ => rfl⟩

def shapeExpr (c : Expr) : Expr :=
  Expr.pick (fun sh : Shape => (Fintype.equivFin Shape sh).val) (shapeTest c)
lemma shapeExpr_eval (F : Target.Formula) (c : Expr) (a : ℕ → ℕ) (i : Fin F.clauses.length)
    (hi : c.eval (Complexity.formulaBits F) a=i.val) :
    (shapeExpr c).eval (Complexity.formulaBits F) a=(Fintype.equivFin Shape (shape (clauseAt F i))).val := by
  apply Expr.pick_eval
  exact shapeTest_nonzero F c a i hi

def repairExpr (c : Expr) (j : ClauseAnswer) (s : Slot) : Expr :=
  Expr.staticLookup (fun sh : Shape => bit (repairedBit sh j s)) (shapeExpr c)
lemma repairExpr_eval (F : Target.Formula) (c : Expr) (a : ℕ → ℕ) (i : Fin F.clauses.length)
    (hi : c.eval (Complexity.formulaBits F) a=i.val) (j : ClauseAnswer) (s : Slot) :
    (repairExpr c j s).eval (Complexity.formulaBits F) a=bit (answerAt (LCInput.repair (clauseAt F i) j) s) := by
  rw [repairExpr,Expr.staticLookup_eval _ _ _ _ _ (shapeExpr_eval F c a i hi),repairedBit_exact]

def selectSlot (x : Expr) (f : Slot → Expr) : Expr :=
  Expr.listSum (List.finRange 3) fun i =>
    .mul (Expr.equal x (.const i.val)) (f (RawInitialTables.slotOrder.symm i))
lemma selectSlot_eval (x : Expr) (f : Slot → Expr) (str : List Bool) (a : ℕ → ℕ) (s : Slot)
    (hs : x.eval str a=(RawInitialTables.slotOrder s).val) :
    (selectSlot x f).eval str a=(f s).eval str a := by
  simp only [selectSlot,Expr.listSum_eval,Expr.eval,Expr.equal_eval,hs,ite_mul,one_mul,zero_mul]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  simp [Fin.val_inj]

end LargeIndependentSets.TargetRepair

end

end OAI
