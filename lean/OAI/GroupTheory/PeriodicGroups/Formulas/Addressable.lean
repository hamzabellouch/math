import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.WordComponents
import OAI.GroupTheory.PeriodicGroups.Formulas.Tableaux

namespace OAI

section
universe u v w
namespace SourceBurnside.Addressable
open FiniteTable Tableau

variable {q : ℕ} [NeZero q]
abbrev Reading (q : ℕ) := Bool ⊕ FiniteTable.Address q

def Reading.eval (w : Reading q) (v : FiniteTable.Address q → Bool) : Bool :=
  match w with
  | .inl b => b
  | .inr a => v a

omit [NeZero q] in
lemma Reading.eval_map {n : ℕ} (m : Fin n → FiniteTable.Address q)
    (w : Wire n) (v : FiniteTable.Address q → Bool) :
    Reading.eval (w.map id m) v=w.eval (v ∘ m) := by cases w <;> rfl

def bit (b : Bool) : ZMod 2 := if b then 1 else 0
def unbit (z : ZMod 2) : Bool := decide (z=1)
@[simp] lemma unbit_bit (b : Bool) : unbit (bit b)=b := by cases b <;> decide
@[simp] lemma bit_unbit (z : ZMod 2) : bit (unbit z)=z := by
  have hz : z=0 ∨ z=1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hz with rfl|rfl <;> norm_num [bit,unbit]

structure Clause (q : ℕ) where
  wires : Fin 3 → Reading q
  truth : (Fin 3 → Bool) → Bool

def Clause.Holds (C : Clause q) (v : FiniteTable.Address q → Bool) : Prop :=
  C.truth (fun i => (C.wires i).eval v)=true

def Clause.compile (C : Clause q) : FiniteTable.Clause q where
  address i := match C.wires i with
    | .inl _ => .certificate 0
    | .inr a => a
  truth r := C.truth (fun i => match C.wires i with
    | .inl b => b
    | .inr _ => unbit (r i))

lemma Clause.compile_holds (C : Clause q) (v : FiniteTable.Address q → Bool) :
    (C.compile.truth fun i => bit (v (C.compile.address i)))=true ↔ C.Holds v := by
  have he : (fun i => match C.wires i with
      | .inl b => b
      | .inr _ => unbit (bit (v (C.compile.address i)))) = fun i => (C.wires i).eval v := by
    funext i
    cases hi : C.wires i <;> simp [compile,Reading.eval,hi]
  change (C.truth (fun i => match C.wires i with
      | .inl b => b
      | .inr _ => unbit (bit (v (C.compile.address i)))))=true ↔ C.Holds v
  rw [he]
  rfl

def unit (a : Reading q) (b : Bool) : Clause q :=
  ⟨![a,a,a],fun v => decide (v 0=b)⟩
omit [NeZero q] in
@[simp] lemma unit_holds (a : Reading q) (b : Bool) (v : FiniteTable.Address q → Bool) :
    (unit a b).Holds v ↔ a.eval v=b := by
  change decide (a.eval v=b)=true ↔ a.eval v=b
  constructor
  · exact of_decide_eq_true
  · intro h; exact decide_eq_true h

def equal (a b : Reading q) (i : Fin 2) : Clause q :=
  ⟨![a,b,a],fun v => if i.val=0 then !v 0 || v 1 else v 0 || !v 1⟩
omit [NeZero q] in
lemma equal_holds (a b : Reading q) (v : FiniteTable.Address q → Bool) :
    (∀ i, (equal a b i).Holds v) ↔ a.eval v=b.eval v := by
  simp only [Clause.Holds,equal,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [Fin.forall_fin_two]
  cases a.eval v <;> cases b.eval v <;> decide

abbrev DataAddress (q : ℕ) := Bool × Fin 10 × Fin q

def dataAddress (p : DataAddress q) : FiniteTable.Address q := .data p.1 p.2.1 p.2.2

inductive InputBit (q : ℕ)
  | fixed (value : Bool)
  | input (address : DataAddress q) (negated : Bool)

def InputBit.eval (a : InputBit q) (v : FiniteTable.Address q → Bool) : Bool :=
  match a with
  | .fixed b => b
  | .input p neg => if neg then !(v (dataAddress p)) else v (dataAddress p)

def initial (a : Reading q) : InputBit q → Fin 2 → Clause q
  | .fixed b,_ => unit a b
  | .input p neg,i =>
      ⟨![a,.inr (dataAddress p),a], fun v =>
        let x := if neg then !v 1 else v 1
        if i.val=0 then !v 0 || x else v 0 || !x⟩

omit [NeZero q] in
lemma initial_holds (a : Reading q) (b : InputBit q) (v : FiniteTable.Address q → Bool) :
    (∀ i, (initial a b i).Holds v) ↔ a.eval v=b.eval v := by
  cases b with
  | fixed b => simp [initial,InputBit.eval]
  | input p neg =>
    change (∀ i : Fin 2, (if i.val=0 then
        !a.eval v || (if neg then !(v (dataAddress p)) else v (dataAddress p))
        else a.eval v || !(if neg then !(v (dataAddress p)) else v (dataAddress p)))=true) ↔
      a.eval v=(if neg then !(v (dataAddress p)) else v (dataAddress p))
    rw [Fin.forall_fin_two]
    cases a.eval v <;> cases v (dataAddress p) <;> cases neg <;> decide

def ofCircuitClause {n : ℕ} (m : Fin n → FiniteTable.Address q)
    (C : Tableau.Circuit.Clause n) : Clause q where
  wires i := (C.wires i).map id m
  truth := C.truth
omit [NeZero q] in
lemma ofCircuitClause_holds {n : ℕ} (m : Fin n → FiniteTable.Address q)
    (C : Tableau.Circuit.Clause n) (v : FiniteTable.Address q → Bool) :
    (ofCircuitClause m C).Holds v ↔ C.Holds (v ∘ m) := by
  have he : (fun i => Reading.eval ((C.wires i).map id m) v) =
      fun i => (C.wires i).eval (v ∘ m) := by
    funext i
    cases C.wires i <;> rfl
  change (C.truth fun i => Reading.eval ((C.wires i).map id m) v)=true ↔ C.truth _=true
  rw [he]

abbrev Triple (a b c : ℕ) := (Fin a × Fin b) × Fin c

def tripleEquiv (a b c : ℕ) : Triple a b c ≃ Fin (c*b*a) :=
  (((finProdFinEquiv (m:=a) (n:=b)).prodCongr (Equiv.refl (Fin c))).trans
    finProdFinEquiv).trans (finCongr (by ring))
lemma tripleEquiv_val (a b c : ℕ) (i : Triple a b c) :
    (tripleEquiv a b c i).val=c*(b*i.1.1.val+i.1.2.val)+i.2.val := by
  simp [tripleEquiv,finProdFinEquiv]
  ring

structure Layout (q β g T W : ℕ) where
  bit_pos : 0<β
  time_pos : 0<T
  width_ge : 3≤W
  certificate_fit : Tableau.Layout.certificateCount β g T W≤q
  clause_fit : Tableau.Layout.clauseCount β g T W≤q
  origin : Fin W

namespace Layout
variable {β g T W : ℕ} (L : Layout q β g T W)

abbrev XIndex := Triple T W β
abbrev YIndex := Triple (T-1) (W-2) g
abbrev CIndex := XIndex (β:=β) (T:=T) (W:=W) ⊕ YIndex (g:=g) (T:=T) (W:=W)

def certEquiv : CIndex (β:=β) (g:=g) (T:=T) (W:=W) ≃
    Fin (Tableau.Layout.certificateCount β g T W) :=
  ((tripleEquiv T W β).sumCongr (tripleEquiv (T-1) (W-2) g)).trans finSumFinEquiv

def core (i : CIndex (β:=β) (g:=g) (T:=T) (W:=W)) : Fin q :=
  Fin.castLE L.certificate_fit (certEquiv i)

def x (t : Fin T) (j : Fin W) (r : Fin β) : FiniteTable.Address q :=
  .certificate (L.core (.inl ((t,j),r)))
def y (t : Fin (T-1)) (j : Fin (W-2)) (v : Fin g) : FiniteTable.Address q :=
  .certificate (L.core (.inr ((t,j),v)))

omit [NeZero q] in
lemma core_x_val (t : Fin T) (j : Fin W) (r : Fin β) :
    (L.core (.inl ((t,j),r))).val=Tableau.Layout.xAddress β W t.val j.val r.val := by
  change (tripleEquiv T W β ((t,j),r)).val=Tableau.Layout.xAddress β W t.val j.val r.val
  exact tripleEquiv_val T W β ((t,j),r)
omit [NeZero q] in
lemma core_y_val (t : Fin (T-1)) (j : Fin (W-2)) (v : Fin g) :
    (L.core (.inr ((t,j),v))).val=Tableau.Layout.yAddress β g T W t.val j.val v.val := by
  change β*W*T+(tripleEquiv (T-1) (W-2) g ((t,j),v)).val=Tableau.Layout.yAddress β g T W t.val j.val v.val
  rw [tripleEquiv_val]
  simp [Tableau.Layout.yAddress,Nat.add_assoc]

omit [NeZero q] in
lemma core_injective : Function.Injective L.core :=
  (Fin.castLE_injective L.certificate_fit).comp (certEquiv.injective)

def certificate (_L : Layout q β g T W) (v : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool) (p : Fin q) : Bool :=
  if hp : p.val < Tableau.Layout.certificateCount β g T W then
    v (certEquiv.symm ⟨p.val,hp⟩) else false

omit [NeZero q] in
@[simp] lemma certificate_core (v : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool)
    (i : CIndex (β:=β) (g:=g) (T:=T) (W:=W)) : L.certificate v (L.core i)=v i := by
  unfold certificate
  rw [dite_eq_left (show (L.core i).val < Tableau.Layout.certificateCount β g T W from
    (certEquiv i).isLt)]
  change v (certEquiv.symm (certEquiv i))=v i
  exact congrArg v (certEquiv.symm_apply_apply i)

def payload (data : DataAddress q → Bool)
    (cert : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool) : FiniteTable.Address q → Bool
  | .data s b p => data (s,b,p)
  | .certificate p => L.certificate cert p
omit [NeZero q] in
@[simp] lemma payload_data (data : DataAddress q → Bool)
    (cert : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool) (p : DataAddress q) :
    L.payload data cert (dataAddress p)=data p := rfl
omit [NeZero q] in
@[simp] lemma payload_x (data : DataAddress q → Bool)
    (cert : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool)
    (t : Fin T) (j : Fin W) (r : Fin β) :
    L.payload data cert (L.x t j r)=cert (.inl ((t,j),r)) := by
  exact L.certificate_core cert _
omit [NeZero q] in
@[simp] lemma payload_y (data : DataAddress q → Bool)
    (cert : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool)
    (t : Fin (T-1)) (j : Fin (W-2)) (v : Fin g) :
    L.payload data cert (L.y t j v)=cert (.inr ((t,j),v)) := by
  exact L.certificate_core cert _

abbrev InitialIndex := Triple W β 2
abbrev BoundaryIndex := Triple (T-1) 2 β
abbrev LocalIndex := Triple (T-1) (W-2) (3*g+2*β)
abbrev ClauseIndex :=
  ((InitialIndex (β:=β) (W:=W) ⊕ BoundaryIndex (β:=β) (T:=T)) ⊕
    LocalIndex (β:=β) (g:=g) (T:=T) (W:=W)) ⊕ Fin β

def clauseEquiv : ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W) ≃
    Fin (Tableau.Layout.clauseCount β g T W) :=
  let bound : BoundaryIndex (β:=β) (T:=T) ≃ Fin (2*β*(T-1)) :=
    (tripleEquiv (T-1) 2 β).trans (finCongr (by ring))
  let first := ((tripleEquiv W β 2).sumCongr bound).trans finSumFinEquiv
  let second := (first.sumCongr (tripleEquiv (T-1) (W-2) (3*g+2*β))).trans finSumFinEquiv
  (second.sumCongr (Equiv.refl (Fin β))).trans finSumFinEquiv

def currentTime (t : Fin (T-1)) : Fin T := ⟨t.val,by have := t.isLt; omega⟩
def nextTime (t : Fin (T-1)) : Fin T := ⟨t.val+1,by have := t.isLt; omega⟩
def interior (j : Fin (W-2)) : Fin W := ⟨j.val+1,by have := j.isLt; omega⟩
def boundary (i : Fin 2) : Fin W :=
  if i.val=0 then ⟨0,by have := L.width_ge; omega⟩ else ⟨W-1,by have := L.width_ge; omega⟩

def localRead (t : Fin (T-1)) (j : Fin (W-2)) :
    Fin (3*β+g) → FiniteTable.Address q := Fin.addCases
  (fun i => let p := finProdFinEquiv.symm i
    L.x (currentTime t) ⟨j.val+p.1.val,by
      have := j.isLt
      have : p.1.val<3 := p.1.isLt
      omega⟩ p.2)
  (L.y t j)

def localClause (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (t : Fin (T-1)) (j : Fin (W-2)) (i : Fin (3*g+2*β)) : Clause q :=
  if hi : i.val<3*g then
    ofCircuitClause (L.localRead t j) (c.clauses[ i.val ]'(by rw [c.clauses_length]; exact hi))
  else
    let r : Fin β := ⟨(i.val-3*g)/2,by have := i.isLt; omega⟩
    let k : Fin 2 := ⟨(i.val-3*g)%2,Nat.mod_lt _ (by decide)⟩
    equal (.inr (L.x (nextTime t) (interior j) r)) ((output r).map id (L.localRead t j)) k

def clause (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool) :
    ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W) → Clause q
  | .inl (.inl (.inl ((j,r),k))) =>
      initial (.inr (L.x ⟨0,L.time_pos⟩ j r)) (init j r) k
  | .inl (.inl (.inr ((t,k),r))) =>
      unit (.inr (L.x (nextTime t) (L.boundary k) r)) (blank r)
  | .inl (.inr ((t,j),i)) => L.localClause c output t j i
  | .inr r => unit (.inr (L.x ⟨T-1,by have := L.time_pos; omega⟩ L.origin r)) (accept r)

def clauseAt (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (i : Fin (Tableau.Layout.clauseCount β g T W)) : Clause q :=
  L.clause c output init blank accept (clauseEquiv.symm i)

omit [NeZero q] in
lemma all_clauses_iff (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (v : FiniteTable.Address q → Bool) :
    (∀ i, (L.clauseAt c output init blank accept i).Holds v) ↔
    (∀ i, (L.clause c output init blank accept i).Holds v) := by
  constructor
  · intro h i
    have hi := h (clauseEquiv i)
    simpa only [clauseAt,Equiv.symm_apply_apply] using hi
  · intro h i
    exact h _

omit [NeZero q] in
lemma localClause_gate (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (t : Fin (T-1)) (j : Fin (W-2)) (i : Fin (3*g)) :
    L.localClause c output t j (Fin.castAdd (2*β) i) =
      ofCircuitClause (L.localRead t j) (c.clauses[i.val]'(by rw [c.clauses_length]; exact i.isLt)) := by
  simp [localClause,i.isLt]

def outputIndex (r : Fin β) (k : Fin 2) : Fin (3*g+2*β) :=
  ⟨3*g+2*r.val+k.val,by have := r.isLt; have := k.isLt; omega⟩
omit [NeZero q] in
lemma localClause_output (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (t : Fin (T-1)) (j : Fin (W-2)) (r : Fin β) (k : Fin 2) :
    L.localClause c output t j (outputIndex r k) =
      equal (.inr (L.x (nextTime t) (interior j) r)) ((output r).map id (L.localRead t j)) k := by
  have hk := k.isLt
  have hd : (3*g+2*r.val+k.val-3*g)/2 = r.val := by omega
  have hm : (3*g+2*r.val+k.val-3*g)%2 = k.val := by omega
  simp [localClause,outputIndex,show ¬3*g+2*r.val+k.val < 3*g by omega,hd,hm]

omit [NeZero q] in
lemma localClause_holds (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (t : Fin (T-1)) (j : Fin (W-2)) (v : FiniteTable.Address q → Bool) :
    (∀ i, (L.localClause c output t j i).Holds v) ↔
    c.Satisfies (v ∘ L.localRead t j) ∧
      ∀ r, v (L.x (nextTime t) (interior j) r) =
        (output r).eval (v ∘ L.localRead t j) := by
  constructor
  · intro h
    constructor
    · apply (c.clauses_iff (v ∘ L.localRead t j)).mp
      intro C hc
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
      have hi' : i<3*g := by simpa only [c.clauses_length] using hi
      have hv := h (Fin.castAdd (2*β) ⟨i,hi'⟩)
      rw [L.localClause_gate] at hv
      exact (ofCircuitClause_holds ..).mp hv
    · intro r
      have he := (equal_holds (.inr (L.x (nextTime t) (interior j) r))
        ((output r).map id (L.localRead t j)) v).mp (fun k => by
          have hk := h (outputIndex r k)
          rwa [L.localClause_output] at hk)
      change v (L.x (nextTime t) (interior j) r)=_ at he
      simpa only [Reading.eval_map] using he
  · rintro ⟨hc,ho⟩ i
    unfold localClause
    split_ifs with hi
    · apply (ofCircuitClause_holds ..).mpr
      exact (c.clauses_iff (v ∘ L.localRead t j)).mpr hc _ (List.getElem_mem _)
    · apply (equal_holds _ _ v).mpr
      change v (L.x (nextTime t) (interior j) _)=_
      have he := ho ⟨(i.val-3*g)/2,by have := i.isLt; omega⟩
      simpa only [Reading.eval_map] using he

def FiniteValid (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (v : FiniteTable.Address q → Bool) : Prop :=
  (∀ j r, v (L.x ⟨0,L.time_pos⟩ j r)=(init j r).eval v) ∧
  (∀ t k r, v (L.x (nextTime t) (L.boundary k) r)=blank r) ∧
  (∀ t j, c.Satisfies (v ∘ L.localRead t j)) ∧
  (∀ t j r, v (L.x (nextTime t) (interior j) r)=
    (output r).eval (v ∘ L.localRead t j)) ∧
  (∀ r, v (L.x ⟨T-1,by have := L.time_pos; omega⟩ L.origin r)=accept r)

omit [NeZero q] in
lemma clauseAt_holds_iff (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (v : FiniteTable.Address q → Bool) :
    (∀ i, (L.clauseAt c output init blank accept i).Holds v) ↔
      L.FiniteValid c output init blank accept v := by
  rw [L.all_clauses_iff]
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro j r
      exact (initial_holds _ _ v).mp (fun k => h (.inl (.inl (.inl ((j,r),k)))))
    · intro t k r
      exact (unit_holds _ _ v).mp (h (.inl (.inl (.inr ((t,k),r)))))
    · intro t j
      exact ((L.localClause_holds c output t j v).mp (fun i => h (.inl (.inr ((t,j),i))))).1
    · intro t j r
      exact ((L.localClause_holds c output t j v).mp (fun i => h (.inl (.inr ((t,j),i))))).2 r
    · intro r
      exact (unit_holds _ _ v).mp (h (.inr r))
  · rintro ⟨hi,hb,hg,ho,ha⟩ i
    rcases i with ((i|i)|i)|i
    · rcases i with ⟨⟨j,r⟩,k⟩
      exact (initial_holds (.inr (L.x ⟨0,L.time_pos⟩ j r)) (init j r) v).mpr (hi j r) k
    · rcases i with ⟨⟨t,k⟩,r⟩
      exact (unit_holds _ _ v).mpr (hb t k r)
    · rcases i with ⟨⟨t,j⟩,k⟩
      exact (L.localClause_holds c output t j v).mpr ⟨hg t j,ho t j⟩ k
    · exact (unit_holds _ _ v).mpr (ha i)

def rows (v : FiniteTable.Address q → Bool) (t j : ℕ) (r : Fin β) : Bool :=
  if ht : t<T then if hj : j<W then v (L.x ⟨t,ht⟩ ⟨j,hj⟩ r) else false else false

def gates (v : FiniteTable.Address q → Bool) (t j : ℕ) (r : Fin g) : Bool :=
  if ht : t<T-1 then if hj : j<W-2 then v (L.y ⟨t,ht⟩ ⟨j,hj⟩ r) else false else false

omit [NeZero q] in
lemma rows_at (v : FiniteTable.Address q → Bool) {t j : ℕ} (ht : t<T) (hj : j<W) (r : Fin β) :
    L.rows v t j r=v (L.x ⟨t,ht⟩ ⟨j,hj⟩ r) := by simp [rows,ht,hj]
omit [NeZero q] in
lemma gates_at (v : FiniteTable.Address q → Bool) {t j : ℕ} (ht : t<T-1) (hj : j<W-2) (r : Fin g) :
    L.gates v t j r=v (L.y ⟨t,ht⟩ ⟨j,hj⟩ r) := by simp [gates,ht,hj]

omit [NeZero q] in
lemma localRead_rows (v : FiniteTable.Address q → Bool) (t : Fin (T-1)) (j : Fin (W-2)) :
    v ∘ L.localRead t j =
      Rectangle.assignment (L.rows v t.val) j.val (L.gates v t.val j.val) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [Function.comp_apply,localRead,Fin.addCases_left,Rectangle.assignment,
      Rectangle.neighborhood]
    exact (L.rows_at v (show t.val<T by have := t.isLt; omega)
      (show j.val+(finProdFinEquiv.symm k : Fin 3 × Fin β).1.val<W by
        have := j.isLt
        have := (finProdFinEquiv.symm k : Fin 3 × Fin β).1.isLt
        omega) _).symm
  · simp only [Function.comp_apply,localRead,Fin.addCases_right,Rectangle.assignment]
    exact (L.gates_at v t.isLt j.isLt k).symm

def inputRow (_L : Layout q β g T W) (init : Fin W → Fin β → InputBit q) (v : FiniteTable.Address q → Bool)
    (j : ℕ) (r : Fin β) : Bool :=
  if hj : j<W then (init ⟨j,hj⟩ r).eval v else false
omit [NeZero q] in
lemma inputRow_at (init : Fin W → Fin β → InputBit q) (v : FiniteTable.Address q → Bool)
    {j : ℕ} (hj : j<W) (r : Fin β) : L.inputRow init v j r=(init ⟨j,hj⟩ r).eval v := by
  simp [inputRow,hj]

omit [NeZero q] in
lemma rectangle_of_finiteValid (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (v : FiniteTable.Address q → Bool) (hv : L.FiniteValid c output init blank accept v) :
    Rectangle.Valid c output T W blank (L.inputRow init v) (L.rows v) (L.gates v) ∧
      L.rows v (T-1) L.origin.val=accept := by
  constructor
  · refine ⟨?_,?_,?_,?_⟩
    · intro j hj
      funext r
      rw [L.rows_at v L.time_pos hj,L.inputRow_at init v hj]
      exact hv.1 _ _
    · intro t ht j hj hjb
      have ht' : t<T-1 := by omega
      funext r
      rw [L.rows_at v ht hj]
      rcases hjb with rfl|he
      · have hb := hv.2.1 ⟨t,ht'⟩ 0 r
        simpa only [nextTime,boundary,Fin.val_zero,ite_true] using hb
      · have hb := hv.2.1 ⟨t,ht'⟩ 1 r
        have hj' : j=W-1 := by omega
        subst j
        simpa only [nextTime,boundary,Fin.val_one,show ¬(1:ℕ)=0 by omega,ite_false] using hb
    · intro t ht j hj
      have ht' : t<T-1 := by omega
      have hj' : j<W-2 := by omega
      have hc := hv.2.2.1 ⟨t,ht'⟩ ⟨j,hj'⟩
      rwa [L.localRead_rows] at hc
    · intro t ht j hj r
      have ht' : t<T-1 := by omega
      have hj' : j<W-2 := by omega
      have hc := hv.2.2.2.1 ⟨t,ht'⟩ ⟨j,hj'⟩ r
      rw [L.localRead_rows] at hc
      rw [L.rows_at v ht (show j+1<W by omega)]
      exact hc
  · funext r
    rw [L.rows_at v (by have := L.time_pos; omega) L.origin.isLt]
    exact hv.2.2.2.2 r

omit [NeZero q] in
theorem clause_sound (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (v : FiniteTable.Address q → Bool)
    (hv : ∀ i, (L.clauseAt c output init blank accept i).Holds v) :
    Rectangle.run c output W blank (L.inputRow init v) (T-1) L.origin.val=accept := by
  have hh := L.rectangle_of_finiteValid c output init blank accept v
    ((L.clauseAt_holds_iff c output init blank accept v).mp hv)
  exact (Rectangle.accepting_tableau_iff c output T W L.origin.val L.time_pos L.origin.isLt
    blank accept (L.inputRow init v)).mp ⟨L.rows v,L.gates v,hh⟩

def assemble (data : DataAddress q → Bool) (cert : Fin q → Bool) : FiniteTable.Address q → Bool
  | .data s b p => data (s,b,p)
  | .certificate p => cert p

omit [NeZero q] in
lemma inputBit_assemble (b : InputBit q) (data : DataAddress q → Bool)
    (c₁ c₂ : Fin q → Bool) : b.eval (assemble data c₁)=b.eval (assemble data c₂) := by
  cases b <;> rfl

omit [NeZero q] in
lemma inputBit_payload (b : InputBit q) (data : DataAddress q → Bool)
    (cert : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool) :
    b.eval (L.payload data cert)=b.eval (assemble data (fun _ => false)) := by
  cases b <;> rfl

omit [NeZero q] in
lemma inputRow_assemble (init : Fin W → Fin β → InputBit q) (data : DataAddress q → Bool)
    (c₁ c₂ : Fin q → Bool) : L.inputRow init (assemble data c₁)=L.inputRow init (assemble data c₂) := by
  funext j r
  unfold inputRow
  split
  · exact inputBit_assemble _ _ _ _
  · rfl

def rectCertificate (X : ℕ → Rectangle.Row β) (Y : ℕ → ℕ → Fin g → Bool) :
    CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool
  | .inl ((t,j),r) => X t.val j.val r
  | .inr ((t,j),v) => Y t.val j.val v

omit [NeZero q] in
lemma localRead_rect (data : DataAddress q → Bool)
    (X : ℕ → Rectangle.Row β) (Y : ℕ → ℕ → Fin g → Bool)
    (t : Fin (T-1)) (j : Fin (W-2)) :
    L.payload data (rectCertificate X Y) ∘ L.localRead t j =
      Rectangle.assignment (X t.val) j.val (Y t.val j.val) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [Function.comp_apply,localRead,Fin.addCases_left,payload_x,rectCertificate,
      currentTime,Rectangle.assignment,Rectangle.neighborhood]
  · simp only [Function.comp_apply,localRead,Fin.addCases_right,payload_y,rectCertificate,
      Rectangle.assignment]

omit [NeZero q] in
lemma finiteValid_of_rectangle (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (data : DataAddress q → Bool)
    (X : ℕ → Rectangle.Row β) (Y : ℕ → ℕ → Fin g → Bool)
    (hv : Rectangle.Valid c output T W blank
      (L.inputRow init (assemble data (fun _ => false))) X Y)
    (ha : X (T-1) L.origin.val=accept) :
    L.FiniteValid c output init blank accept (L.payload data (rectCertificate X Y)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j r
    rw [L.payload_x,L.inputBit_payload]
    simpa only [rectCertificate,inputRow,dite_eq_left j.isLt] using congrFun (hv.1 j.val j.isLt) r
  · intro t k r
    rw [L.payload_x]
    exact congrFun (hv.2.1 t.val (by have := t.isLt; omega)
      (L.boundary k).val (L.boundary k).isLt (by
        unfold boundary
        split
        · exact Or.inl rfl
        · exact Or.inr (by have := L.width_ge; dsimp; omega))) r
  · intro t j
    rw [L.localRead_rect]
    exact hv.2.2.1 t.val (by have := t.isLt; omega) j.val (by have := j.isLt; omega)
  · intro t j r
    rw [L.payload_x,L.localRead_rect]
    exact hv.2.2.2 t.val (by have := t.isLt; omega) j.val (by have := j.isLt; omega) r
  · intro r
    rw [L.payload_x]
    exact congrFun ha r

omit [NeZero q] in
theorem certificate_iff (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (data : DataAddress q → Bool) :
    (∃ cert : Fin q → Bool, ∀ i,
      (L.clauseAt c output init blank accept i).Holds (assemble data cert)) ↔
      Rectangle.run c output W blank (L.inputRow init (assemble data (fun _ => false)))
        (T-1) L.origin.val=accept := by
  constructor
  · rintro ⟨cert,hc⟩
    have hh := L.clause_sound c output init blank accept (assemble data cert) hc
    rwa [L.inputRow_assemble init data cert (fun _ => false)] at hh
  · intro ha
    let X := Rectangle.run c output W blank (L.inputRow init (assemble data (fun _ => false)))
    let Y := fun t j v => c.evaluate (Rectangle.neighborhood (X t) j) (Fin.natAdd (3*β) v)
    refine ⟨L.certificate (rectCertificate X Y),?_⟩
    change ∀ i, (L.clauseAt c output init blank accept i).Holds
      (L.payload data (rectCertificate X Y))
    exact (L.clauseAt_holds_iff c output init blank accept _).mpr
      (L.finiteValid_of_rectangle c output init blank accept data X Y
        (Rectangle.run_valid c output T W blank _) ha)

omit [NeZero q] in
lemma clauseCount_pos (L : Layout q β g T W) : 0<Tableau.Layout.clauseCount β g T W := by
  have := L.bit_pos
  unfold Tableau.Layout.clauseCount
  omega

def schedule (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Task → Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool) : Schedule q where
  count _ := ⟨Tableau.Layout.clauseCount β g T W,by have := L.clause_fit; omega⟩
  positive _ := L.clauseCount_pos
  clause task p := if hp : p.val<Tableau.Layout.clauseCount β g T W then
    (L.clauseAt c output (init task) blank accept ⟨p.val,hp⟩).compile
    else (unit (.inl true) true).compile

lemma schedule_clause (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Task → Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (task : Task) (i : Fin (Tableau.Layout.clauseCount β g T W)) :
    (L.schedule c output init blank accept).clause task (Fin.castLE L.clause_fit i)=
      (L.clauseAt c output (init task) blank accept i).compile := by
  simp only [schedule,Fin.val_castLE,dite_eq_left i.isLt]

theorem schedule_holds_iff (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Task → Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (task : Task) (v : FiniteTable.Address q → Bool) :
    (∀ i : Fin (Tableau.Layout.clauseCount β g T W),
      let C := (L.schedule c output init blank accept).clause task (Fin.castLE L.clause_fit i)
      C.truth (fun k => bit (v (C.address k)))=true) ↔
    ∀ i, (L.clauseAt c output (init task) blank accept i).Holds v := by
  simp only [L.schedule_clause,Clause.compile_holds]

theorem schedule_certificate_iff (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Task → Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (task : Task) (data : DataAddress q → Bool) :
    (∃ cert : Fin q → Bool, ∀ i : Fin (Tableau.Layout.clauseCount β g T W),
      let C := (L.schedule c output init blank accept).clause task (Fin.castLE L.clause_fit i)
      C.truth (fun k => bit (assemble data cert (C.address k)))=true) ↔
      Rectangle.run c output W blank (L.inputRow (init task) (assemble data (fun _ => false)))
        (T-1) L.origin.val=accept := by
  simp only [L.schedule_holds_iff]
  exact L.certificate_iff c output (init task) blank accept data

end Layout
end SourceBurnside.Addressable

namespace SourceBurnside.Addressable
open FiniteTable Tableau
variable {q β g T W d : ℕ} [NeZero q]

noncomputable def physicalBits (R : FiniteTable.Region q d) (a : FiniteTable.Address q) : Bool := unbit (R.read a)

theorem physical_clauses_iff (L : Layout q β g T W)
    (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Task → Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (R : FiniteTable.Region q d) :
    (∀ i, (R.plan (L.schedule c output init blank accept)).Holds i) ↔
      ∀ i, (L.clauseAt c output (init R.task) blank accept i).Holds (physicalBits R) := by
  let S := L.schedule c output init blank accept
  have he (i : Fin (Tableau.Layout.clauseCount β g T W)) :
      (R.plan S).Holds i ↔ (L.clauseAt c output (init R.task) blank accept i).Holds (physicalBits R) := by
    rw [R.holds_iff S i]
    have hi : R.clauseIndex S i=Fin.castLE L.clause_fit i := by rfl
    rw [hi,L.schedule_clause]
    have hh := Clause.compile_holds (L.clauseAt c output (init R.task) blank accept i) (physicalBits R)
    simpa only [physicalBits,bit_unbit] using hh
  exact forall_congr' he

theorem physical_accepts (L : Layout q β g T W)
    (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Task → Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (R : FiniteTable.Region q d)
    (hc : ∀ i, (R.plan (L.schedule c output init blank accept)).Holds i) :
    Rectangle.run c output W blank (L.inputRow (init R.task) (physicalBits R))
      (T-1) L.origin.val=accept :=
  L.clause_sound c output (init R.task) blank accept _
    ((physical_clauses_iff L c output init blank accept R).mp hc)

end SourceBurnside.Addressable

namespace SourceBurnside.Addressable
open FiniteTable Tableau
variable {q β g T W d N : ℕ} [NeZero q]

theorem reached_success_accepts (L : Layout q β g T W)
    (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Task → Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (v : List (Cell q)) (f : Fin N → Cell q) (i : Fin N)
    (hv : Syntax (L.schedule c output init blank accept) d v)
    (hi : ∀ a ∈ v, a.marker=.idle)
    (hr : Reach (L.schedule c output init blank accept) d v (List.ofFn f))
    (hh : (f i).marker=.full) (hp : (f i).head.phase=.success) :
    let hs := reach_syntax hr hv
    let R := Component.region f i hs hh
    Rectangle.run c output W blank (L.inputRow (init R.task) (physicalBits R))
      (T-1) L.origin.val=accept := by
  intro hs R
  apply physical_accepts L c output init blank accept R
  apply Component.region_holds f i hs hh _ hp
  have hg := Verification.reach_clean_good (L.schedule c output init blank accept) hv hi hr
  exact ((Verification.wordGood_ofFn (L.schedule c output init blank accept) f).mp hg) i hh

end SourceBurnside.Addressable

end

end OAI
