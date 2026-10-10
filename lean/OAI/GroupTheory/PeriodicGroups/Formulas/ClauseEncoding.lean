import Mathlib
import OAI.GroupTheory.PeriodicGroups.Formulas.BooleanCircuits
import OAI.GroupTheory.PeriodicGroups.Formulas.Addressable

namespace OAI

universe u v w
namespace SourceBurnside.Addressable

lemma tripleEquiv_symm_values (a b c : ℕ) (i : Fin (c*b*a)) :
    ((tripleEquiv a b c).symm i).1.1.val=(i.val/c)/b ∧
    ((tripleEquiv a b c).symm i).1.2.val=(i.val/c)%b ∧
    ((tripleEquiv a b c).symm i).2.val=i.val%c := by
  simp [tripleEquiv,finProdFinEquiv]

namespace Layout
variable {β g T W : ℕ}

def family : ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W) → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inl (.inl (.inr _)) => 1
  | .inl (.inr _) => 2
  | .inr _ => 3

def coordinates : ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W) → ℕ × ℕ × ℕ
  | .inl (.inl (.inl ((j,r),k))) => (j.val,r.val,k.val)
  | .inl (.inl (.inr ((t,k),r))) => (t.val,k.val,r.val)
  | .inl (.inr ((t,j),v)) => (t.val,j.val,v.val)
  | .inr r => (0,0,r.val)

def directIndex (β g T W i : ℕ) : ℕ × (ℕ × ℕ × ℕ) :=
  let A := 2*β*W
  let B := 2*β*(T-1)
  let C := (3*g+2*β)*(W-2)*(T-1)
  if i<A then (0,((i/2)/β,(i/2)%β,i%2))
  else if i<A+B then
    let p := i-A
    (1,((p/β)/2,(p/β)%2,p%β))
  else if i<A+B+C then
    let p := i-A-B
    (2,((p/(3*g+2*β))/(W-2),(p/(3*g+2*β))%(W-2),p%(3*g+2*β)))
  else (3,(0,0,i-A-B-C))

lemma natural_unpair (a b k l : ℕ) (hk : k<a) (hl : l<b) :
    (b*k+l)/b=k ∧ (b*k+l)%b=l ∧ b*k+l<b*a := by
  have hb : 0<b := by omega
  constructor
  · rw [Nat.add_comm,Nat.add_mul_div_left _ _ hb]
    simp [Nat.div_eq_of_lt hl]
  constructor
  · simp [Nat.add_mod,Nat.mod_eq_of_lt hl]
  · nlinarith

lemma clause_index_direct (j : ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W)) :
    directIndex β g T W (clauseEquiv j).val=(family j,coordinates j) := by
  cases j with
  | inl j => cases j with
    | inl j => cases j with
      | inl j =>
        rcases j with ⟨⟨a,b⟩,c⟩
        have h1 := natural_unpair W β a.val b.val a.isLt b.isLt
        have h2 := natural_unpair (β*W) 2 (β*a.val+b.val) c.val h1.2.2 c.isLt
        have hc : (clauseEquiv (β:=β) (g:=g) (T:=T) (W:=W) (Sum.inl (Sum.inl (Sum.inl ((a,b),c))))).val=2*(β*a.val+b.val)+c.val := by
          change (tripleEquiv W β 2 ((a,b),c)).val=_
          exact tripleEquiv_val W β 2 ((a,b),c)
        rw [hc]
        have hb : 2*(β*a.val+b.val)+c.val<2*β*W := by nlinarith [h2.2.2]
        simp [directIndex,hb,h2.1,h2.2.1,h1.1,h1.2.1,family,coordinates]
      | inr j =>
        rcases j with ⟨⟨a,b⟩,c⟩
        have h1 := natural_unpair (T-1) 2 a.val b.val a.isLt b.isLt
        have h2 := natural_unpair (2*(T-1)) β (2*a.val+b.val) c.val h1.2.2 c.isLt
        have hc : (clauseEquiv (β:=β) (g:=g) (T:=T) (W:=W) (Sum.inl (Sum.inl (Sum.inr ((a,b),c))))).val=2*β*W+(β*(2*a.val+b.val)+c.val) := by
          change 2*β*W+(tripleEquiv (T-1) 2 β ((a,b),c)).val=_
          rw [tripleEquiv_val]
        rw [hc]
        have hb : β*(2*a.val+b.val)+c.val<2*β*(T-1) := by nlinarith [h2.2.2]
        simp [directIndex,show ¬2*β*W+(β*(2*a.val+b.val)+c.val)<2*β*W by omega,
          show 2*β*W+(β*(2*a.val+b.val)+c.val)<2*β*W+2*β*(T-1) by omega,
          h2.1,h2.2.1,h1.1,h1.2.1,family,coordinates]
    | inr j =>
      rcases j with ⟨⟨a,b⟩,c⟩
      have h1 := natural_unpair (T-1) (W-2) a.val b.val a.isLt b.isLt
      have h2 := natural_unpair ((W-2)*(T-1)) (3*g+2*β) ((W-2)*a.val+b.val) c.val h1.2.2 c.isLt
      have hc : (clauseEquiv (β:=β) (g:=g) (T:=T) (W:=W) (Sum.inl (Sum.inr ((a,b),c)))).val=2*β*W+2*β*(T-1)+((3*g+2*β)*((W-2)*a.val+b.val)+c.val) := by
        change 2*β*W+2*β*(T-1)+(tripleEquiv (T-1) (W-2) (3*g+2*β) ((a,b),c)).val=_
        rw [tripleEquiv_val]
      rw [hc]
      have hb : (3*g+2*β)*((W-2)*a.val+b.val)+c.val<(3*g+2*β)*(W-2)*(T-1) := by nlinarith [h2.2.2]
      have hsub : 2*β*W+2*β*(T-1)+((3*g+2*β)*((W-2)*a.val+b.val)+c.val)-2*β*W-2*β*(T-1)=
          (3*g+2*β)*((W-2)*a.val+b.val)+c.val := by omega
      simp [directIndex,show ¬2*β*W+2*β*(T-1)+((3*g+2*β)*((W-2)*a.val+b.val)+c.val)<2*β*W by omega,
        show ¬2*β*W+2*β*(T-1)+((3*g+2*β)*((W-2)*a.val+b.val)+c.val)<2*β*W+2*β*(T-1) by omega,
        show 2*β*W+2*β*(T-1)+((3*g+2*β)*((W-2)*a.val+b.val)+c.val)<2*β*W+2*β*(T-1)+(3*g+2*β)*(W-2)*(T-1) by omega,
        hsub,h2.1,h2.2.1,h1.1,h1.2.1,family,coordinates]
  | inr r =>
    have hc : (clauseEquiv (β:=β) (g:=g) (T:=T) (W:=W) (Sum.inr r)).val=2*β*W+2*β*(T-1)+(3*g+2*β)*(W-2)*(T-1)+r.val := by rfl
    rw [hc]
    simp only [directIndex,family,coordinates]
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega)]
    congr 3; omega

theorem clause_index_lookup (i : Fin (Tableau.Layout.clauseCount β g T W)) :
    directIndex β g T W i.val=(family (clauseEquiv.symm i),coordinates (clauseEquiv.symm i)) := by
  simpa only [Equiv.apply_symm_apply] using clause_index_direct (clauseEquiv.symm i)

end Layout
end SourceBurnside.Addressable

namespace SourceBurnside.AddressFormula
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
abbrev Expr := Fin 4 → Formula ι
def record {q : ℕ} : Address q → Fin 4 → ℕ
  | .data s b p => ![0,boolean s,b.val,p.val]
  | .certificate p => ![1,0,0,p.val]
def evaluate (a : Expr (ι:=ι)) (v : ι → ℕ) : Fin 4 → ℕ := fun i => (a i).eval v

def data (s b p : Formula ι) : Expr (ι:=ι) := ![.constant 0,s,b,p]
def certificate (p : Formula ι) : Expr (ι:=ι) := ![.constant 1,.constant 0,.constant 0,p]
omit [DecidableEq ι] in
lemma data_exact {q : ℕ} (s b p : Formula ι) (v : ι → ℕ) (S : Bool) (B : Fin 10) (P : Fin q)
    (hs : s.eval v=boolean S) (hb : b.eval v=B.val) (hp : p.eval v=P.val) :
    evaluate (data s b p) v=record (.data S B P) := by
  funext i;fin_cases i <;> simp [evaluate,data,record,hs,hb,hp]
omit [DecidableEq ι] in
lemma certificate_exact {q : ℕ} (p : Formula ι) (v : ι → ℕ) (P : Fin q) (hp : p.eval v=P.val) :
    evaluate (certificate p) v=record (.certificate P) := by
  funext i;fin_cases i <;> simp [evaluate,certificate,record,hp]

def readAt (a : Expr (ι:=ι)) (c : CellFormula.Expr (ι:=ι)) : Formula ι :=
  .branch (all [CellFormula.isCore c,equal (c.1 1) (a 3),equal (c.1 4) (a 2)])
    (.branch (a 0) (c.2 4) (.branch (a 1) (c.2 3) (c.2 2))) (.constant 0)

lemma readAt_exact {q : ℕ} [NeZero q] {a : Expr (ι:=ι)} {c : CellFormula.Expr (ι:=ι)}
    {v : ι → ℕ} {A : Address q} {C : Cell q}
    (ha : evaluate a v=record A) (hc : CellFormula.evaluate c v=cellRecord C) :
    (readAt a c).eval v=boolean (bit (C.read A)) := by
  have ha' (i : Fin 4) : (a i).eval v=record A i := congrFun ha i
  have hzero : (all [CellFormula.isCore c,equal (c.1 1) (a 3),equal (c.1 4) (a 2)]).eval v=0 ↔
      ¬(C.isCore ∧ (cellRecord C).1 1=record A 3 ∧ (cellRecord C).1 4=record A 2) := by
    rw [←not_iff_not];simp only [not_not,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq,CellFormula.core_exact hc,Formula.equal_ne_zero,CellFormula.represent_int hc,ha']
  simp only [readAt,Formula.eval,hzero,ha',CellFormula.represent_flag hc]
  cases A <;> cases hp : C.pos <;>
    simp [Cell.read,hp,record,cellRecord,integers,flags,Cell.isCore,positionIndex,boolean]
  all_goals simp only [Fin.ext_iff]
  all_goals split_ifs <;> simp_all
end SourceBurnside.AddressFormula

namespace SourceBurnside.ClauseFormula
section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
structure Expr where
  address : Fin 3 → AddressFormula.Expr (ι:=ι)
  truth : Reg → Formula ι

def Represents {q : ℕ} (e : Expr (ι:=ι)) (v : ι → ℕ) (C : Clause q) : Prop :=
  (∀i,AddressFormula.evaluate (e.address i) v=AddressFormula.record (C.address i)) ∧
  (∀r,(e.truth r).eval v=boolean (C.truth r))

def matchReg (r : Fin 3 → Formula ι) (R : Reg) : Formula ι :=
  all (List.ofFn (fun i : Fin 3 => equal (r i) (.constant (boolean (bit (R i))))))
def regs : List Reg := [![0,0,0],![0,0,1],![0,1,0],![0,1,1],![1,0,0],![1,0,1],![1,1,0],![1,1,1]]
lemma mem_regs (R : Reg) : R∈regs := by
  have H (z : ZMod 2) : z=0 ∨ z=1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases H (R 0) with h0|h0 <;> rcases H (R 1) with h1|h1 <;> rcases H (R 2) with h2|h2 <;>
    simp [regs,funext_iff,Fin.forall_fin_succ,h0,h1,h2]
def truth (e : Expr (ι:=ι)) (r : Fin 3 → Formula ι) : Formula ι :=
  any (regs.map (fun R => and (matchReg r R) (e.truth R)))

lemma bit_injective : Function.Injective Codec.bit := by
  intro a b h;simpa only [unbit_bit] using congrArg unbit h
lemma matchReg_exact {r : Fin 3 → Formula ι} {v : ι → ℕ} {R : Reg}
    (hr : ∀i,(r i).eval v=boolean (bit (R i))) (T : Reg) :
    (matchReg r T).eval v≠0 ↔ R=T := by
  simp [matchReg,hr,boolean_injective.eq_iff,bit_injective.eq_iff,funext_iff,Fin.forall_fin_succ]
lemma truth_exact {q : ℕ} {e : Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (he : Represents e v C) {r : Fin 3 → Formula ι} {R : Reg}
    (hr : ∀i,(r i).eval v=boolean (bit (R i))) :
    (truth e r).eval v≠0 ↔ C.truth R=true := by
  simp [truth,Formula.and_ne_zero,matchReg_exact hr,he.2,mem_regs]
lemma truth_bool (e : Expr (ι:=ι)) (r : Fin 3 → Formula ι) (v : ι → ℕ) :
    (truth e r).eval v≤1 := bool_any _ _
lemma truth_value {q : ℕ} {e : Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (he : Represents e v C) {r : Fin 3 → Formula ι} {R : Reg}
    (hr : ∀i,(r i).eval v=boolean (bit (R i))) :
    (truth e r).eval v=boolean (C.truth R) := by
  have hb := truth_bool e r v
  cases hc : C.truth R with
  | false =>
    have ht := truth_exact he hr
    simp only [hc,Bool.false_eq_true,iff_false,not_ne_iff] at ht
    simpa only [hc,boolean_false] using ht
  | true =>
    have ht := (truth_exact he hr).mpr hc
    have h1 : (truth e r).eval v=1 := by omega
    simpa only [hc,boolean_true] using h1

def delta (e : Expr (ι:=ι)) (a : CellFormula.Expr (ι:=ι)) : Fin 3 → Formula ι :=
  fun i => AddressFormula.readAt (e.address i) a
lemma delta_exact {q : ℕ} [NeZero q] {e : Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (he : Represents e v C) {a : CellFormula.Expr (ι:=ι)} {A : Cell q}
    (ha : CellFormula.evaluate a v=cellRecord A) (i : Fin 3) :
    (delta e a i).eval v=boolean (bit (A.delta C i)) := AddressFormula.readAt_exact (he.1 i) ha

def choose (b : Formula ι) (x y : Expr (ι:=ι)) : Expr (ι:=ι) where
  address i j := .branch b (x.address i j) (y.address i j)
  truth r := .branch b (x.truth r) (y.truth r)
omit [DecidableEq ι] in
lemma choose_true {q : ℕ} {b : Formula ι} {x y : Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (hb : b.eval v≠0) (hx : Represents x v C) : Represents (choose b x y) v C := by
  constructor
  · intro i;funext j
    simpa [choose,AddressFormula.evaluate,Formula.eval,hb] using congrFun (hx.1 i) j
  · intro r;simpa [choose,Formula.eval,hb] using hx.2 r
omit [DecidableEq ι] in
lemma choose_false {q : ℕ} {b : Formula ι} {x y : Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (hb : b.eval v=0) (hy : Represents y v C) : Represents (choose b x y) v C := by
  constructor
  · intro i;funext j
    simpa [choose,AddressFormula.evaluate,Formula.eval,hb] using congrFun (hy.1 i) j
  · intro r;simpa [choose,Formula.eval,hb] using hy.2 r

def lookup (index : Formula ι) (fallback : Expr (ι:=ι)) : ℕ → List (Expr (ι:=ι)) → Expr (ι:=ι)
  | _,[] => fallback
  | n,x::xs => choose (equal index (.constant n)) x (lookup index fallback (n+1) xs)
omit [DecidableEq ι] in
lemma lookup_exact {q : ℕ} (index : Formula ι) (fallback : Expr (ι:=ι)) (n : ℕ)
    (xs : List (Expr (ι:=ι))) (j : Fin xs.length) (v : ι → ℕ) (C : Clause q)
    (hj : index.eval v=n+j.val) (hr : Represents (xs.get j) v C) :
    Represents (lookup index fallback n xs) v C := by
  induction xs generalizing n with
  | nil => exact Fin.elim0 j
  | cons x xs ih =>
    by_cases h0 : j.val=0
    · have jj : j=0 := Fin.ext h0
      subst jj
      apply choose_true
      · simp [hj]
      · exact hr
    · let k : Fin xs.length := ⟨j.val-1,by have := j.isLt; simp only [List.length_cons] at this;omega⟩
      apply choose_false
      · simp [hj,h0]
      · apply ih (n+1) k
        · dsimp [k];omega
        · have hjk : j=k.succ := Fin.ext (by dsimp [k];omega)
          simpa only [hjk,List.get_cons_succ'] using hr
end

section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]

def truthTable (f : Reg → Bool) (r : Fin 3 → Formula ι) : Formula ι :=
  truth ⟨(fun _ => AddressFormula.certificate (.constant 0)),
    (fun R => .constant (boolean (f R)))⟩ r
lemma truthTable_value (f : Reg → Bool) {r : Fin 3 → Formula ι} {v : ι → ℕ} {R : Reg}
    (hr : ∀i,(r i).eval v=boolean (bit (R i))) :
    (truthTable f r).eval v=boolean (f R) := by
  let C : Clause 1 := ⟨fun _ => .certificate 0,f⟩
  apply truth_value (C:=C) _ hr
  constructor
  · intro i;exact AddressFormula.certificate_exact (.constant 0) v (0:Fin 1) rfl
  · intro R;rfl

structure ReadingExpr where
  address : AddressFormula.Expr (ι:=ι)
  value : Bool → Formula ι

def readValue {q : ℕ} : Addressable.Reading q → Bool → Bool
  | .inl a,_ => a
  | .inr _,b => b

def RepresentsReading {q : ℕ} [NeZero q] (e : ReadingExpr (ι:=ι)) (v : ι → ℕ) (w : Addressable.Reading q) : Prop :=
  AddressFormula.evaluate e.address v=AddressFormula.record (match w with | .inl _ => .certificate 0 | .inr a => a) ∧
  ∀b,(e.value b).eval v=boolean (readValue w b)

def fixedReading (b : Formula ι) : ReadingExpr (ι:=ι) :=
  ⟨AddressFormula.certificate (.constant 0),fun _ => b⟩
def addressReading (a : AddressFormula.Expr (ι:=ι)) : ReadingExpr (ι:=ι) := ⟨a,fun b => .constant (boolean b)⟩
omit [DecidableEq ι] in
lemma fixedReading_exact {q : ℕ} [NeZero q] {b : Formula ι} {v : ι → ℕ} {B : Bool}
    (hb : b.eval v=boolean B) : RepresentsReading (q:=q) (fixedReading b) v (.inl B) :=
  ⟨AddressFormula.certificate_exact (.constant 0) v 0 rfl,fun _ => hb⟩
omit [DecidableEq ι] in
lemma addressReading_exact {q : ℕ} [NeZero q] {a : AddressFormula.Expr (ι:=ι)} {v : ι → ℕ} {A : Address q}
    (ha : AddressFormula.evaluate a v=AddressFormula.record A) : RepresentsReading (addressReading a) v (.inr A) := ⟨ha,fun _ => rfl⟩

def make (w : Fin 3 → ReadingExpr (ι:=ι)) (f : (Fin 3 → Bool) → Bool) : Expr (ι:=ι) :=
  ⟨fun i => (w i).address,fun r => truthTable (fun R => f (fun i => bit (R i)))
    (fun i => (w i).value (bit (r i)))⟩
lemma make_exact {q : ℕ} [NeZero q] {w : Fin 3 → ReadingExpr (ι:=ι)} {v : ι → ℕ}
    {W : Fin 3 → Addressable.Reading q} (hw : ∀i,RepresentsReading (w i) v (W i))
    (f : (Fin 3 → Bool) → Bool) : Represents (make w f) v (Addressable.Clause.compile ⟨W,f⟩) := by
  constructor
  · intro i;exact (hw i).1
  · intro R
    let V : Reg := fun i => unbit (readValue (W i) (bit (R i)))
    have hV (i : Fin 3) : ((w i).value (bit (R i))).eval v=boolean (bit (V i)) := by
      simp only [V,bit_unbit];exact (hw i).2 _
    have E := truthTable_value (fun R => f (fun i => bit (R i))) hV
    change _=boolean (f _) at E
    change _=boolean (f _)
    rw [show (make w f).truth R=truthTable (fun R => f (fun i => bit (R i))) _ from rfl,E]
    congr 2;funext i
    cases h : W i <;> simp [V,readValue,h]
    rfl

end

open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def unit (a : ReadingExpr (ι:=ι)) (b : Formula ι) : Expr (ι:=ι) :=
  choose b (make ![a,a,a] (fun v => decide (v 0=true))) (make ![a,a,a] (fun v => decide (v 0=false)))
lemma unit_exact {q : ℕ} [NeZero q] {a : ReadingExpr (ι:=ι)} {b : Formula ι} {v : ι → ℕ}
    {A : Addressable.Reading q} {B : Bool} (ha : RepresentsReading a v A) (hb : b.eval v=boolean B) :
    Represents (unit a b) v (Addressable.unit A B).compile := by
  have hw (i : Fin 3) : RepresentsReading (![a,a,a] i) v (![A,A,A] i) := by fin_cases i <;> exact ha
  cases B with
  | false => exact choose_false (by simpa using hb) (make_exact hw _)
  | true => exact choose_true (by rw [hb];decide) (make_exact hw _)

def equalReading (a b : ReadingExpr (ι:=ι)) (k : Formula ι) : Expr (ι:=ι) :=
  choose (equal k (.constant 0)) (make ![a,b,a] (fun v => !v 0 || v 1))
    (make ![a,b,a] (fun v => v 0 || !v 1))
lemma equalReading_exact {q : ℕ} [NeZero q] {a b : ReadingExpr (ι:=ι)} {k : Formula ι} {v : ι → ℕ}
    {A B : Addressable.Reading q} (K : Fin 2) (ha : RepresentsReading a v A) (hb : RepresentsReading b v B)
    (hk : k.eval v=K.val) : Represents (equalReading a b k) v (Addressable.equal A B K).compile := by
  have hw (i : Fin 3) : RepresentsReading (![a,b,a] i) v (![A,B,A] i) := by
    fin_cases i
    · exact ha
    · exact hb
    · exact ha
  fin_cases K
  · apply choose_true
    · simp [hk]
    · exact make_exact hw _
  · apply choose_false
    · simp [hk,equal_eval]
    · exact make_exact hw _

def initialData (a : ReadingExpr (ι:=ι)) (p : AddressFormula.Expr (ι:=ι)) (negated k : Formula ι) : Expr (ι:=ι) :=
  let b := addressReading p
  let u := make ![a,b,a] (fun v => !v 0 || !v 1)
  let v := make ![a,b,a] (fun v => v 0 || !!v 1)
  choose negated (choose (equal k (.constant 0)) u v) (equalReading a b k)
lemma initialData_exact {q : ℕ} [NeZero q] {a : ReadingExpr (ι:=ι)} {p : AddressFormula.Expr (ι:=ι)}
    {negated k : Formula ι} {v : ι → ℕ} {A : Addressable.Reading q} {P : Addressable.DataAddress q}
    (N : Bool) (K : Fin 2) (ha : RepresentsReading a v A)
    (hp : AddressFormula.evaluate p v=AddressFormula.record (Addressable.dataAddress P))
    (hn : negated.eval v=boolean N) (hk : k.eval v=K.val) :
    Represents (initialData a p negated k) v (Addressable.initial A (.input P N) K).compile := by
  have hb := addressReading_exact hp
  have hw (i : Fin 3) : RepresentsReading (![a,addressReading p,a] i) v (![A,.inr (Addressable.dataAddress P),A] i) := by
    fin_cases i
    · exact ha
    · exact hb
    · exact ha
  cases N with
  | false =>
    apply choose_false (by simpa using hn)
    exact equalReading_exact K ha hb hk
  | true =>
    apply choose_true (by rw [hn];decide)
    fin_cases K
    · exact choose_true (by simp [hk]) (make_exact hw _)
    · exact choose_false (by simp [hk,equal_eval]) (make_exact hw _)

def wire {n : ℕ} (a : Fin n → AddressFormula.Expr (ι:=ι)) : Tableau.Wire n → ReadingExpr (ι:=ι)
  | .inl b => fixedReading (.constant (boolean b))
  | .inr i => addressReading (a i)
omit [DecidableEq ι] in
lemma wire_exact {n q : ℕ} [NeZero q] {a : Fin n → AddressFormula.Expr (ι:=ι)} {v : ι → ℕ}
    {A : Fin n → Address q} (ha : ∀i,AddressFormula.evaluate (a i) v=AddressFormula.record (A i)) (w : Tableau.Wire n) :
    RepresentsReading (wire a w) v (w.map id A) := by
  cases w with
  | inl b => exact fixedReading_exact rfl
  | inr i => exact addressReading_exact (ha i)
def circuitClause {n : ℕ} (a : Fin n → AddressFormula.Expr (ι:=ι)) (C : Tableau.Circuit.Clause n) : Expr (ι:=ι) :=
  make (fun i => wire a (C.wires i)) C.truth
lemma circuitClause_exact {n q : ℕ} [NeZero q] {a : Fin n → AddressFormula.Expr (ι:=ι)} {v : ι → ℕ}
    {A : Fin n → Address q} (ha : ∀i,AddressFormula.evaluate (a i) v=AddressFormula.record (A i)) (C : Tableau.Circuit.Clause n) :
    Represents (circuitClause a C) v (Addressable.ofCircuitClause A C).compile :=
  make_exact (fun i => wire_exact ha (C.wires i)) _
end SourceBurnside.ClauseFormula

namespace SourceBurnside.InitialFormula
section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
structure Expr where
  tag : Formula ι
  address : AddressFormula.Expr (ι:=ι)
  polarity : Formula ι

def Represents {q : ℕ} (e : Expr (ι:=ι)) (v : ι → ℕ) : Addressable.InputBit q → Prop
  | .fixed b => e.tag.eval v=0 ∧ e.polarity.eval v=boolean b
  | .input p n => e.tag.eval v≠0 ∧ AddressFormula.evaluate e.address v=AddressFormula.record (Addressable.dataAddress p) ∧
      e.polarity.eval v=boolean n

def fixed (b : Formula ι) : Expr (ι:=ι) := ⟨.constant 0,AddressFormula.certificate (.constant 0),b⟩
def data (p : AddressFormula.Expr (ι:=ι)) (n : Formula ι) : Expr (ι:=ι) := ⟨.constant 1,p,n⟩
def choose (b : Formula ι) (x y : Expr (ι:=ι)) : Expr (ι:=ι) where
  tag := .branch b x.tag y.tag
  address i := .branch b (x.address i) (y.address i)
  polarity := .branch b x.polarity y.polarity
omit [DecidableEq ι] in
lemma fixed_exact {q : ℕ} {b : Formula ι} {v : ι → ℕ} {B : Bool} (hb : b.eval v=boolean B) :
    Represents (fixed b) v (.fixed (q:=q) B) := ⟨rfl,hb⟩
omit [DecidableEq ι] in
lemma data_exact {q : ℕ} {p : AddressFormula.Expr (ι:=ι)} {n : Formula ι} {v : ι → ℕ}
    (P : Addressable.DataAddress q) (N : Bool) (hp : AddressFormula.evaluate p v=AddressFormula.record (Addressable.dataAddress P))
    (hn : n.eval v=boolean N) : Represents (data p n) v (.input P N) := ⟨by simp [data],hp,hn⟩
omit [DecidableEq ι] in
lemma choose_true {q : ℕ} {b : Formula ι} {x y : Expr (ι:=ι)} {v : ι → ℕ} {I : Addressable.InputBit q}
    (hb : b.eval v≠0) (hx : Represents x v I) : Represents (choose b x y) v I := by
  have haddress : AddressFormula.evaluate (choose b x y).address v=AddressFormula.evaluate x.address v := by
    funext i;simp [choose,AddressFormula.evaluate,eval,hb]
  cases I with
  | fixed B => exact ⟨by simpa [choose,eval,hb] using hx.1,by simpa [choose,eval,hb] using hx.2⟩
  | input P N => exact ⟨by simpa [choose,eval,hb] using hx.1,haddress.trans hx.2.1,
      by simpa [choose,eval,hb] using hx.2.2⟩
omit [DecidableEq ι] in
lemma choose_false {q : ℕ} {b : Formula ι} {x y : Expr (ι:=ι)} {v : ι → ℕ} {I : Addressable.InputBit q}
    (hb : b.eval v=0) (hy : Represents y v I) : Represents (choose b x y) v I := by
  have haddress : AddressFormula.evaluate (choose b x y).address v=AddressFormula.evaluate y.address v := by
    funext i;simp [choose,AddressFormula.evaluate,eval,hb]
  cases I with
  | fixed B => exact ⟨by simpa [choose,eval,hb] using hy.1,by simpa [choose,eval,hb] using hy.2⟩
  | input P N => exact ⟨by simpa [choose,eval,hb] using hy.1,haddress.trans hy.2.1,
      by simpa [choose,eval,hb] using hy.2.2⟩

def clauses (a : ClauseFormula.ReadingExpr (ι:=ι)) (b : Expr (ι:=ι)) (k : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  ClauseFormula.choose b.tag (ClauseFormula.initialData a b.address b.polarity k) (ClauseFormula.unit a b.polarity)
lemma clauses_exact {q : ℕ} [NeZero q] {a : ClauseFormula.ReadingExpr (ι:=ι)} {b : Expr (ι:=ι)} {k : Formula ι} {v : ι → ℕ}
    {A : Addressable.Reading q} {B : Addressable.InputBit q} (K : Fin 2)
    (ha : ClauseFormula.RepresentsReading a v A) (hb : Represents b v B) (hk : k.eval v=K.val) :
    ClauseFormula.Represents (clauses a b k) v (Addressable.initial A B K).compile := by
  cases B with
  | fixed B => exact ClauseFormula.choose_false hb.1 (ClauseFormula.unit_exact ha hb.2)
  | input P N => exact ClauseFormula.choose_true hb.1 (ClauseFormula.initialData_exact N K ha hb.2.1 hb.2.2 hk)

def mapBit (f : Bool → Bool) {q : ℕ} : Addressable.InputBit q → Addressable.InputBit q
  | .fixed b => .fixed (f b)
  | .input p n => if f false=f true then .fixed (f false) else .input p (xor n (f false))
def symbol (f : Bool → Bool) (b : Expr (ι:=ι)) : Expr (ι:=ι) :=
  if f false=f true then fixed (.constant (boolean (f false)))
  else { b with polarity := if f false then neg b.polarity else b.polarity }
omit [DecidableEq ι] in
lemma symbol_exact {q : ℕ} {b : Expr (ι:=ι)} {v : ι → ℕ} {B : Addressable.InputBit q}
    (hb : Represents b v B) (f : Bool → Bool) : Represents (symbol f b) v (mapBit f B) := by
  have hus : (f false=false ∧ f true=false) ∨ (f false=false ∧ f true=true) ∨
      (f false=true ∧ f true=false) ∨ (f false=true ∧ f true=true) := by
    cases f false <;> cases f true <;> simp
  rcases hus with h|h|h|h
  all_goals cases B with
    | fixed B => cases B <;> simp_all [Represents,symbol,mapBit,fixed,neg_eval,boolean]
    | input P N => cases N <;> simp_all [Represents,symbol,mapBit,fixed,neg_eval,boolean]

structure Piece where
  length : Formula ι
  read : Formula ι → Expr (ι:=ι)
def Piece.Represents {q : ℕ} (p : Piece (ι:=ι)) (v : ι → ℕ) (bits : List (Addressable.InputBit q)) : Prop :=
  p.length.eval v=bits.length ∧ ∀ (j : Formula ι) (k : Fin bits.length), j.eval v=k.val →
    InitialFormula.Represents (p.read j) v (bits.get k)
def Piece.append (a b : Piece (ι:=ι)) : Piece (ι:=ι) where
  length := .add a.length b.length
  read i := choose (less i a.length) (a.read i) (b.read (.sub i a.length))
omit [DecidableEq ι] in
lemma Piece.append_exact {q : ℕ} {a b : Piece (ι:=ι)} {v : ι → ℕ} {as bs : List (Addressable.InputBit q)}
    (ha : a.Represents v as) (hb : b.Represents v bs) : (a.append b).Represents v (as++bs) := by
  refine ⟨by simp [Piece.append,ha.1,hb.1],?_⟩
  intro j k hj
  by_cases hk : k.val<as.length
  · apply choose_true
    · simp [hj,ha.1,hk]
    · have H := ha.2 j ⟨k.val,hk⟩ hj
      simpa only [List.get_eq_getElem,List.getElem_append_left hk] using H
  · apply choose_false
    · simp [less_eval,hj,ha.1,hk]
    · have hk' : k.val-as.length<bs.length := by have := k.isLt;simp only [List.length_append] at this;omega
      have H := hb.2 (.sub j a.length) ⟨k.val-as.length,hk'⟩ (by simp [eval,hj,ha.1])
      simpa only [List.get_eq_getElem,List.getElem_append_right (by omega : as.length≤k.val)] using H

omit [DecidableEq ι] in
lemma bitAt_value (x i : Formula ι) (v : ι → ℕ) :
    (bitAt x i).eval v=boolean ((x.eval v).testBit (i.eval v)) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change (x.eval v/2^(i.eval v))%2=(if decide ((x.eval v/2^(i.eval v))%2=1) then 1 else 0)
  have h := Nat.mod_lt (x.eval v/2^(i.eval v)) (by omega : 0<2)
  split_ifs <;> simp_all

def fixedBits (bits : List Bool) : Piece (ι:=ι) where
  length := .constant bits.length
  read i := fixed (bitAt (.constant (Codec.binaryValue bits)) i)
omit [DecidableEq ι] in
lemma fixedBits_exact {q : ℕ} (bits : List Bool) (v : ι → ℕ) :
    (fixedBits (ι:=ι) bits).Represents v (bits.map (Addressable.InputBit.fixed (q:=q))) := by
  refine ⟨by simp [fixedBits],?_⟩
  intro j k hj
  simp only [List.get_eq_getElem,List.getElem_map]
  apply fixed_exact
  rw [bitAt_value]
  simp [Codec.binaryValue_bit,eval,hj,show k.val<bits.length by simpa using k.isLt]

def binSize (n : ℕ) := if n=0 then 1 else n.size
def bin (n : ℕ) : List Bool := List.ofFn (fun i : Fin (binSize n) => n.testBit (binSize n-1-i.val))
def enc (n : ℕ) : List Bool := List.replicate (binSize n) true ++ false::bin n
@[simp] lemma bin_length (n : ℕ) : (bin n).length=binSize n := by simp [bin]
@[simp] lemma enc_length (n : ℕ) : (enc n).length=2*binSize n+1 := by simp [enc];omega
@[simp] lemma bin_zero : bin 0=[false] := by decide

def number (n : Formula ι) : Piece (ι:=ι) where
  length := .bitLength n
  read i := fixed (bitAt n (.sub (.sub (.bitLength n) (.constant 1)) i))
omit [DecidableEq ι] in
lemma number_exact {q : ℕ} (n : Formula ι) (v : ι → ℕ) :
    (number n).Represents v ((bin (n.eval v)).map (Addressable.InputBit.fixed (q:=q))) := by
  refine ⟨by simp [number,eval,binSize],?_⟩
  intro j k hj
  simp only [List.get_eq_getElem,List.getElem_map]
  apply fixed_exact
  rw [bitAt_value]
  simp [bin,eval,binSize,hj]

def ones (n : Formula ι) : Piece (ι:=ι) where
  length := n
  read _ := fixed (.constant 1)
omit [DecidableEq ι] in
lemma ones_exact {q : ℕ} (n : Formula ι) (v : ι → ℕ) :
    (ones n).Represents v ((List.replicate (n.eval v) true).map (Addressable.InputBit.fixed (q:=q))) := by
  refine ⟨by simp [ones],?_⟩
  intro j k hj
  simp only [List.get_eq_getElem,List.getElem_map]
  apply fixed_exact
  simp [eval]

def header (n : Formula ι) : Piece (ι:=ι) :=
  ((ones (.bitLength n)).append (fixedBits [false])).append (number n)
omit [DecidableEq ι] in
lemma header_exact {q : ℕ} (n : Formula ι) (v : ι → ℕ) :
    (header n).Represents v ((enc (n.eval v)).map (Addressable.InputBit.fixed (q:=q))) := by
  have H := Piece.append_exact (Piece.append_exact (ones_exact (q:=q) (.bitLength n) v) (fixedBits_exact [false] v))
    (number_exact n v)
  simpa [header,enc,eval,binSize,List.map_append,List.append_assoc] using H
end

section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]

def bits (value length : Formula ι) : Piece (ι:=ι) where
  length := length
  read i := fixed (bitAt value i)
omit [DecidableEq ι] in
lemma bits_exact {q : ℕ} {value length : Formula ι} {v : ι → ℕ} (bs : List Bool)
    (hv : value.eval v=binaryValue bs) (hl : length.eval v=bs.length) :
    (bits value length).Represents v (bs.map (Addressable.InputBit.fixed (q:=q))) := by
  refine ⟨by simp [bits,hl],?_⟩
  intro j k hj
  simp only [List.get_eq_getElem,List.getElem_map]
  apply fixed_exact
  rw [bitAt_value,hv,binaryValue_bit]
  simp [hj,show k.val<bs.length by simpa using k.isLt]

def single (b : Formula ι) : Piece (ι:=ι) where
  length := .constant 1
  read _ := fixed b
omit [DecidableEq ι] in
lemma single_exact {q : ℕ} {b : Formula ι} {v : ι → ℕ} {B : Bool} (hb : b.eval v=boolean B) :
    (single b).Represents v [Addressable.InputBit.fixed (q:=q) B] := by
  refine ⟨rfl,?_⟩
  intro j k hj
  fin_cases k
  exact fixed_exact hb

def inputData {q : ℕ} (d l : ℕ) (Z : Bool) (hd : 0<d) (hdq : d≤q) (hl : 0<l) (hl10 : l≤10) :
    List (Addressable.InputBit q) :=
  List.ofFn (fun i : Fin (if Z then l*d else 2*(l*d)) =>
    Addressable.InputBit.input
      (decide (l*d ≤ i.val),⟨(i.val/d)%l,(Nat.mod_lt _ hl).trans_le hl10⟩,
        ⟨i.val%d,(Nat.mod_lt _ hd).trans_le hdq⟩) false)
def dataPiece (d l zeroTask : Formula ι) : Piece (ι:=ι) where
  length := .branch zeroTask (.mul l d) (.mul (.constant 2) (.mul l d))
  read i := data (AddressFormula.data (.le (.mul l d) i) (.mod (.div i d) l) (.mod i d)) (.constant 0)
omit [DecidableEq ι] in
lemma dataPiece_exact {q d l : ℕ} (Z : Bool) (hd : 0<d) (hdq : d≤q) (hl : 0<l) (hl10 : l≤10)
    {d' l' z : Formula ι} {v : ι → ℕ} (hD : d'.eval v=d) (hL : l'.eval v=l) (hZ : z.eval v=boolean Z) :
    (dataPiece d' l' z).Represents v (inputData d l Z hd hdq hl hl10) := by
  refine ⟨?_,?_⟩
  · cases Z <;> simp [dataPiece,inputData,eval,hD,hL,hZ,boolean]
  · intro j k hj
    simp only [inputData] at k ⊢
    rw [List.get_ofFn]
    apply data_exact _ false
    · apply AddressFormula.data_exact
      · simp [eval,hD,hL,hj,boolean]
      · simp [eval,hD,hL,hj]
      · simp [eval,hD,hj]
    · rfl

def sourceInput {q : ℕ} (a : List Bool) (H l : ℕ) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) : List (Addressable.InputBit q) :=
  ((enc a.length++a++enc H++enc l++[Z]).map Addressable.InputBit.fixed) ++
    inputData (10000*H) l Z hd hdq hl hl10

def inputPiece (code codeLength H l zeroTask : Formula ι) : Piece (ι:=ι) :=
  (((((header codeLength).append (bits code codeLength)).append (header H)).append (header l)).append (single zeroTask)).append
    (dataPiece (.mul (.constant 10000) H) l zeroTask)
omit [DecidableEq ι] in
lemma inputPiece_exact {q H l : ℕ} (a : List Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10)
    {code codeLength H' l' z : Formula ι} {v : ι → ℕ}
    (hcode : code.eval v=binaryValue a) (hlen : codeLength.eval v=a.length)
    (hH : H'.eval v=H) (hL : l'.eval v=l) (hz : z.eval v=boolean Z) :
    (inputPiece code codeLength H' l' z).Represents v (sourceInput a H l Z hd hdq hl hl10) := by
  have hh := header_exact (q:=q) codeLength v
  rw [hlen] at hh
  have hc := bits_exact (q:=q) a hcode hlen
  have hH' := header_exact (q:=q) H' v
  rw [hH] at hH'
  have hl' := header_exact (q:=q) l' v
  rw [hL] at hl'
  have h := Piece.append_exact (Piece.append_exact (Piece.append_exact (Piece.append_exact hh hc) hH') hl') (single_exact hz)
  have hd' := dataPiece_exact Z hd hdq hl hl10 (d':=.mul (.constant 10000) H') (by simp [eval,hH]) hL hz
  simpa [inputPiece,sourceInput,List.map_append,List.append_assoc] using Piece.append_exact h hd'
end

open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]

def row {q β W : ℕ} (blank origin : Fin β → Bool) (symbol : Bool → Fin β → Bool) (o : ℕ)
    (input : List (Addressable.InputBit q)) (j : Fin W) (r : Fin β) : Addressable.InputBit q :=
  if j.val=o then .fixed (origin r)
  else if hj : o<j.val ∧ j.val-(o+1) < input.length then
    mapBit (fun b => symbol b r) (input[j.val-(o+1)]'hj.2)
  else .fixed (blank r)

def cell {β : ℕ} (blank origin : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    (o : Formula ι) (input : Piece (ι:=ι)) (j : Formula ι) (r : Fin β) : Expr (ι:=ι) :=
  let k := .sub j (.add o (.constant 1))
  choose (equal j o) (fixed (.constant (boolean (origin r))))
    (choose (and (less o j) (less k input.length))
      (symbol (fun b => encoding b r) (input.read k)) (fixed (.constant (boolean (blank r)))))
omit [DecidableEq ι] in
lemma cell_exact {q β W : ℕ} (blank origin : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    {o j : Formula ι} {input : Piece (ι:=ι)} {v : ι → ℕ} {O : ℕ} {Input : List (Addressable.InputBit q)}
    (J : Fin W) (R : Fin β) (ho : o.eval v=O) (hj : j.eval v=J.val) (hinput : input.Represents v Input) :
    Represents (cell blank origin encoding o input j R) v (row blank origin encoding O Input J R) := by
  by_cases h0 : J.val=O
  · rw [row,ite_eq_left h0]
    apply choose_true
    · simp [hj,ho,h0]
    · exact fixed_exact rfl
  · rw [row,ite_eq_right h0]
    apply choose_false
    · simp [equal_eval,hj,ho,h0]
    · by_cases h1 : O<J.val ∧ J.val-(O+1)<Input.length
      · rw [dite_eq_left h1]
        apply choose_true
        · simp [Formula.and_ne_zero,ho,hj,eval,hinput.1,h1]
        · exact symbol_exact (hinput.2 _ ⟨J.val-(O+1),h1.2⟩ (by simp [eval,hj,ho])) _
      · rw [dite_eq_right h1]
        apply choose_false
        · rw [←not_ne_iff]
          simpa [Formula.and_ne_zero,ho,hj,eval,hinput.1] using h1
        · exact fixed_exact rfl
end SourceBurnside.InitialFormula

end OAI
