import Mathlib
import OAI.GroupTheory.PeriodicGroups.Formulas.ClauseEncoding

namespace OAI

universe u v w
namespace SourceBurnside.PhysicalFormula
section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]

def x (β : ℕ) (W t j r : Formula ι) : AddressFormula.Expr (ι:=ι) :=
  AddressFormula.certificate (.add (.mul (.constant β) (.add (.mul W t) j)) r)
def y (β g : ℕ) (T W t j v : Formula ι) : AddressFormula.Expr (ι:=ι) :=
  AddressFormula.certificate (.add (.mul (.mul (.constant β) W) T)
    (.add (.mul (.constant g) (.add (.mul (.sub W (.constant 2)) t) j)) v))

omit [DecidableEq ι] in
lemma x_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    {w t j r : Formula ι} {v : ι → ℕ} (tt : Fin T) (jj : Fin W) (rr : Fin β)
    (hw : w.eval v=W) (ht : t.eval v=tt.val) (hj : j.eval v=jj.val) (hr : r.eval v=rr.val) :
    AddressFormula.evaluate (x β w t j r) v=AddressFormula.record (L.x tt jj rr) := by
  apply AddressFormula.certificate_exact
  rw [L.core_x_val]
  simp [Formula.eval,hw,ht,hj,hr,Tableau.Layout.xAddress]
omit [DecidableEq ι] in
lemma y_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    {T' w t j r : Formula ι} {v : ι → ℕ} (tt : Fin (T-1)) (jj : Fin (W-2)) (rr : Fin g)
    (hT : T'.eval v=T) (hw : w.eval v=W) (ht : t.eval v=tt.val) (hj : j.eval v=jj.val) (hr : r.eval v=rr.val) :
    AddressFormula.evaluate (y β g T' w t j r) v=AddressFormula.record (L.y tt jj rr) := by
  apply AddressFormula.certificate_exact
  rw [L.core_y_val]
  simp [Formula.eval,hT,hw,ht,hj,hr,Tableau.Layout.yAddress,Nat.add_assoc]

def localAddress (β g : ℕ) (T W t j : Formula ι) : Fin (3*β+g) → AddressFormula.Expr (ι:=ι) :=
  Fin.addCases (fun i => let p := finProdFinEquiv.symm i
    x β W t (.add j (.constant p.1.val)) (.constant p.2.val))
    (fun r => y β g T W t j (.constant r.val))
omit [DecidableEq ι] in
lemma localAddress_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    {T' w t j : Formula ι} {v : ι → ℕ} (tt : Fin (T-1)) (jj : Fin (W-2))
    (hT : T'.eval v=T) (hw : w.eval v=W) (ht : t.eval v=tt.val) (hj : j.eval v=jj.val)
    (i : Fin (3*β+g)) :
    AddressFormula.evaluate (localAddress β g T' w t j i) v=AddressFormula.record (L.localRead tt jj i) := by
  refine Fin.addCases ?_ ?_ i
  · intro a
    simp only [localAddress,Addressable.Layout.localRead,Fin.addCases_left]
    apply x_exact L _ _ _ hw ht
    · simp [Formula.eval,hj]
    · rfl
  · intro a
    simp only [localAddress,Addressable.Layout.localRead,Fin.addCases_right]
    exact y_exact L tt jj a hT hw ht hj rfl

omit [DecidableEq ι] in
lemma lookup_ofFn_exact {q n : ℕ} {e : Fin n → ClauseFormula.Expr (ι:=ι)}
    {index : Formula ι} {fallback : ClauseFormula.Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (k : Fin n) (hk : index.eval v=k.val) (he : ClauseFormula.Represents (e k) v C) :
    ClauseFormula.Represents (ClauseFormula.lookup index fallback 0 (List.ofFn e)) v C := by
  apply ClauseFormula.lookup_exact index fallback 0 (List.ofFn e)
    ⟨k.val,by simp⟩ v C
  · simpa using hk
  · simpa using he

def localClause (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (T W t j i : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  let addresses := localAddress β g T W t j
  let fallback := ClauseFormula.unit (ClauseFormula.fixedReading (.constant 1)) (.constant 1)
  let gates := c.clauses.map (ClauseFormula.circuitClause addresses)
  let k := .mod (.sub i (.constant (3*g))) (.constant 2)
  let out := List.ofFn (fun r : Fin β => ClauseFormula.equalReading
    (ClauseFormula.addressReading (x β W (.add t (.constant 1)) (.add j (.constant 1)) (.constant r.val)))
    (ClauseFormula.wire addresses (output r)) k)
  ClauseFormula.choose (less i (.constant (3*g)))
    (ClauseFormula.lookup i fallback 0 gates)
    (ClauseFormula.lookup (.div (.sub i (.constant (3*g))) (.constant 2)) fallback 0 out)

lemma localClause_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    {T' w t j i : Formula ι} {v : ι → ℕ} (tt : Fin (T-1)) (jj : Fin (W-2)) (ii : Fin (3*g+2*β))
    (hT : T'.eval v=T) (hw : w.eval v=W) (ht : t.eval v=tt.val) (hj : j.eval v=jj.val) (hi : i.eval v=ii.val) :
    ClauseFormula.Represents (localClause β g c output T' w t j i) v (L.localClause c output tt jj ii).compile := by
  have ha := localAddress_exact L tt jj hT hw ht hj
  by_cases hgate : ii.val<3*g
  · rw [Addressable.Layout.localClause,dite_eq_left hgate]
    apply ClauseFormula.choose_true
    · simpa [hi] using hgate
    · apply ClauseFormula.lookup_exact _ _ 0 _
        ⟨ii.val,by simpa only [List.length_map,c.clauses_length] using hgate⟩
      · simpa using hi
      · simpa using ClauseFormula.circuitClause_exact ha (c.clauses[ii.val]'(by simpa only [c.clauses_length] using hgate))
  · rw [Addressable.Layout.localClause,dite_eq_right hgate]
    apply ClauseFormula.choose_false
    · simp [less_eval,hi,hgate]
    · apply lookup_ofFn_exact ⟨(ii.val-3*g)/2,by have := ii.isLt;omega⟩
      · simp [Formula.eval,hi]
      · apply ClauseFormula.equalReading_exact
          ⟨(ii.val-3*g)%2,Nat.mod_lt _ (by decide)⟩
        · apply ClauseFormula.addressReading_exact
          apply x_exact L _ _ _ hw
          · simp [Formula.eval,ht,Addressable.Layout.nextTime]
          · simp [Formula.eval,hj,Addressable.Layout.interior]
          · rfl
        · exact ClauseFormula.wire_exact ha _
        · simp [Formula.eval,hi]

def chooseIndex (b : Formula ι) (x y : Fin 4 → Formula ι) : Fin 4 → Formula ι :=
  fun i => .branch b (x i) (y i)
def clauseIndex (β g : ℕ) (T W i : Formula ι) : Fin 4 → Formula ι :=
  let A := .mul (.constant (2*β)) W
  let B := .mul (.constant (2*β)) (.sub T (.constant 1))
  let C := .mul (.mul (.constant (3*g+2*β)) (.sub W (.constant 2))) (.sub T (.constant 1))
  let p := .sub i A
  let r := .sub p B
  let c := .constant (3*g+2*β)
  chooseIndex (less i A)
    ![.constant 0,.div (.div i (.constant 2)) (.constant β),.mod (.div i (.constant 2)) (.constant β),.mod i (.constant 2)]
    (chooseIndex (less i (.add A B))
      ![.constant 1,.div (.div p (.constant β)) (.constant 2),.mod (.div p (.constant β)) (.constant 2),.mod p (.constant β)]
      (chooseIndex (less i (.add (.add A B) C))
        ![.constant 2,.div (.div r c) (.sub W (.constant 2)),.mod (.div r c) (.sub W (.constant 2)),.mod r c]
        ![.constant 3,.constant 0,.constant 0,.sub r C]))
def indexEval (x : Fin 4 → Formula ι) (v : ι → ℕ) : ℕ × (ℕ × ℕ × ℕ) :=
  ((x 0).eval v,((x 1).eval v,(x 2).eval v,(x 3).eval v))
omit [DecidableEq ι] in
lemma clauseIndex_exact (β g : ℕ) (T W i : Formula ι) (v : ι → ℕ) :
    indexEval (clauseIndex β g T W i) v=Addressable.Layout.directIndex β g (T.eval v) (W.eval v) (i.eval v) := by
  by_cases h0 : i.eval v<2*β*W.eval v
  · simp [indexEval,clauseIndex,chooseIndex,less_eval,eval,h0,Addressable.Layout.directIndex]
  · by_cases h1 : i.eval v<2*β*W.eval v+2*β*(T.eval v-1)
    · simp [indexEval,clauseIndex,chooseIndex,less_eval,eval,h0,h1,Addressable.Layout.directIndex]
    · by_cases h2 : i.eval v<2*β*W.eval v+2*β*(T.eval v-1)+(3*g+2*β)*(W.eval v-2)*(T.eval v-1)
      all_goals simp [indexEval,clauseIndex,chooseIndex,less_eval,eval,h0,h1,h2,Addressable.Layout.directIndex]
end

section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def fallback : ClauseFormula.Expr (ι:=ι) := ClauseFormula.unit (ClauseFormula.fixedReading (.constant 1)) (.constant 1)
def initialFamily (β : ℕ) (init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι))
    (W j r k : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  ClauseFormula.lookup r fallback 0 (List.ofFn (fun s : Fin β => InitialFormula.clauses
    (ClauseFormula.addressReading (x β W (.constant 0) j (.constant s.val))) (init j s) k))
lemma initialFamily_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} {Init : Fin W → Fin β → Addressable.InputBit q}
    {w j r k : Formula ι} {v : ι → ℕ} (J : Fin W) (R : Fin β) (K : Fin 2)
    (hw : w.eval v=W) (hj : j.eval v=J.val) (hr : r.eval v=R.val) (hk : k.eval v=K.val)
    (hi : InitialFormula.Represents (init j R) v (Init J R)) :
    ClauseFormula.Represents (initialFamily β init w j r k) v
      (Addressable.initial (.inr (L.x ⟨0,L.time_pos⟩ J R)) (Init J R) K).compile := by
  apply lookup_ofFn_exact R hr
  apply InitialFormula.clauses_exact K
  · exact ClauseFormula.addressReading_exact (x_exact L ⟨0,L.time_pos⟩ J R hw rfl hj rfl)
  · exact hi
  · exact hk

def boundaryFamily (β : ℕ) (blank : Fin β → Bool) (W t j r : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  let boundary := .branch (equal j (.constant 0)) (.constant 0) (.sub W (.constant 1))
  ClauseFormula.lookup r fallback 0 (List.ofFn (fun s : Fin β => ClauseFormula.unit
    (ClauseFormula.addressReading (x β W (.add t (.constant 1)) boundary (.constant s.val))) (.constant (boolean (blank s)))))
lemma boundaryFamily_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (blank : Fin β → Bool) {w t j r : Formula ι} {v : ι → ℕ}
    (Tt : Fin (T-1)) (J : Fin 2) (R : Fin β)
    (hw : w.eval v=W) (ht : t.eval v=Tt.val) (hj : j.eval v=J.val) (hr : r.eval v=R.val) :
    ClauseFormula.Represents (boundaryFamily β blank w t j r) v
      (Addressable.unit (.inr (L.x (Addressable.Layout.nextTime Tt) (L.boundary J) R)) (blank R)).compile := by
  apply lookup_ofFn_exact R hr
  apply ClauseFormula.unit_exact
  · apply ClauseFormula.addressReading_exact
    apply x_exact L _ _ _ hw
    · simp [eval,ht,Addressable.Layout.nextTime]
    · simp [eval,equal_eval,hj,hw,Addressable.Layout.boundary]
      split_ifs <;> rfl
    · rfl
  · rfl

def finalFamily (β : ℕ) (accept : Fin β → Bool) (T W O r : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  ClauseFormula.lookup r fallback 0 (List.ofFn (fun s : Fin β => ClauseFormula.unit
    (ClauseFormula.addressReading (x β W (.sub T (.constant 1)) O (.constant s.val))) (.constant (boolean (accept s)))))
lemma finalFamily_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (accept : Fin β → Bool) {T' w O r : Formula ι} {v : ι → ℕ}
    (R : Fin β) (hT : T'.eval v=T) (hw : w.eval v=W) (hO : O.eval v=L.origin.val) (hr : r.eval v=R.val) :
    ClauseFormula.Represents (finalFamily β accept T' w O r) v
      (Addressable.unit (.inr (L.x ⟨T-1,by have := L.time_pos;omega⟩ L.origin R)) (accept R)).compile := by
  apply lookup_ofFn_exact R hr
  apply ClauseFormula.unit_exact
  · apply ClauseFormula.addressReading_exact
    exact x_exact L _ _ _ hw (by simp [eval,hT]) hO rfl
  · rfl

def familyClause (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)) (blank accept : Fin β → Bool)
    (T W O : Formula ι) (e : Fin 4 → Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  ClauseFormula.choose (equal (e 0) (.constant 0)) (initialFamily β init W (e 1) (e 2) (e 3))
    (ClauseFormula.choose (equal (e 0) (.constant 1)) (boundaryFamily β blank W (e 1) (e 2) (e 3))
      (ClauseFormula.choose (equal (e 0) (.constant 2)) (localClause β g c output T W (e 1) (e 2) (e 3))
        (finalFamily β accept T W O (e 3))))
lemma familyClause_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} {Init : Fin W → Fin β → Addressable.InputBit q}
    (blank accept : Fin β → Bool) {T' w O : Formula ι} {v : ι → ℕ} (e : Fin 4 → Formula ι)
    (hT : T'.eval v=T) (hw : w.eval v=W) (hO : O.eval v=L.origin.val)
    (hi : ∀j J, j.eval v=J.val → ∀r, InitialFormula.Represents (init j r) v (Init J r))
    (K : Addressable.Layout.ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W))
    (he : indexEval e v=(Addressable.Layout.family K,Addressable.Layout.coordinates K)) :
    ClauseFormula.Represents (familyClause β g c output init blank accept T' w O e) v
      (L.clause c output Init blank accept K).compile := by
  cases K with
  | inl K => cases K with
    | inl K => cases K with
      | inl K =>
        rcases K with ⟨⟨J,R⟩,N⟩
        simp only [indexEval,Addressable.Layout.family,Addressable.Layout.coordinates,Prod.mk.injEq] at he
        apply ClauseFormula.choose_true (by simp [he.1])
        exact initialFamily_exact L J R N hw he.2.1 he.2.2.1 he.2.2.2 (hi _ J he.2.1 R)
      | inr K =>
        rcases K with ⟨⟨Tt,J⟩,R⟩
        simp only [indexEval,Addressable.Layout.family,Addressable.Layout.coordinates,Prod.mk.injEq] at he
        apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
        apply ClauseFormula.choose_true (by simp [he.1])
        exact boundaryFamily_exact L blank Tt J R hw he.2.1 he.2.2.1 he.2.2.2
    | inr K =>
      rcases K with ⟨⟨Tt,J⟩,R⟩
      simp only [indexEval,Addressable.Layout.family,Addressable.Layout.coordinates,Prod.mk.injEq] at he
      apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
      apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
      apply ClauseFormula.choose_true (by simp [he.1])
      exact localClause_exact L c output Tt J R hT hw he.2.1 he.2.2.1 he.2.2.2
  | inr R =>
    simp only [indexEval,Addressable.Layout.family,Addressable.Layout.coordinates,Prod.mk.injEq] at he
    apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
    apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
    apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
    exact finalFamily_exact L accept R hT hw hO he.2.2.2
end

open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def clauseAt (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)) (blank accept : Fin β → Bool)
    (T W O i : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  familyClause β g c output init blank accept T W O (clauseIndex β g T W i)
lemma clauseAt_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} {Init : Fin W → Fin β → Addressable.InputBit q}
    (blank accept : Fin β → Bool) {T' w O i : Formula ι} {v : ι → ℕ}
    (hT : T'.eval v=T) (hw : w.eval v=W) (hO : O.eval v=L.origin.val)
    (hi : ∀j J, j.eval v=J.val → ∀r, InitialFormula.Represents (init j r) v (Init J r))
    (K : Fin (Tableau.Layout.clauseCount β g T W)) (hK : i.eval v=K.val) :
    ClauseFormula.Represents (clauseAt β g c output init blank accept T' w O i) v
      (L.clauseAt c output Init blank accept K).compile := by
  apply familyClause_exact L c output blank accept _ hT hw hO hi (Addressable.Layout.clauseEquiv.symm K)
  rw [clauseIndex_exact,hT,hw,hK]
  exact Addressable.Layout.clause_index_lookup K
end SourceBurnside.PhysicalFormula

namespace SourceBurnside.CellFormula
section
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def side (a : Expr (ι:=ι)) : Formula ι := a.2 1
def clause (a : Expr (ι:=ι)) : Formula ι := a.1 7
def register (a : Expr (ι:=ι)) (i : Fin 3) : Formula ι := a.2 ⟨i.val+5,by omega⟩
def zeroReg : Fin 3 → Formula ι := fun _ => .constant 0

def unaryMove (a b : Expr (ι:=ι)) (count truth : Formula ι) : Formula ι :=
  any [
    all [first b,equalCells a (idle b (side b)),equalCells b (boundary b (side b))],
    all [last b,equalCells a (boundary b (side b)),equalCells b (full b (side b) (.constant 0) .acquisition zeroReg)],
    all [last b,equalCells a (full b (side b) (clause b) .acquisition (register b)),equalCells b (full b (side b) (clause b) .readLeft (register b))],
    all [first b,equalCells a (full b (side b) (clause b) .readLeft (register b)),equalCells b (full b (side b) (clause b) .readRight (register b))],
    all [last b,equalCells a (full b (side b) (clause b) .readRight (register b)),equalCells b (full b (side b) (clause b) .beforeGate (register b))],
    all [last b,equalCells a (full b (side b) (clause b) .beforeGate (register b)),equalCells b (full b (side b) (clause b) .afterGate (register b)),equal truth (.constant 1)],
    all [last b,equalCells a (full b (side b) (clause b) .afterGate (register b)),equalCells b (full b (side b) (clause b) .undoLeft (register b))],
    all [first b,equalCells a (full b (side b) (clause b) .undoLeft (register b)),equalCells b (full b (side b) (clause b) .undoRight (register b))],
    all [last b,equalCells a (full b (side b) (clause b) .undoRight (register b)),equalCells b (full b (side b) (clause b) .finish (register b))],
    all [last b,equalCells a (full b (side b) (clause a) .finish zeroReg),equalCells b (full b (side b) (clause b) .acquisition zeroReg),equal (.add (clause a) (.constant 1)) (clause b)],
    all [last b,equalCells a (full b (side b) (clause a) .finish zeroReg),equalCells b (full b (side b) (.constant 0) .success zeroReg),equal (.add (clause a) (.constant 1)) count],
    all [last b,equalCells a (full b (neg (side b)) (.constant 0) .success zeroReg),equalCells b (full b (side b) (.constant 0) .success zeroReg),equal (b.2 0) (.constant 0)]]

section Accessors
variable {q : ℕ} {a : Expr (ι:=ι)} {v : ι → ℕ} {c : Cell q}
variable (ha : evaluate a v=cellRecord c)
include ha
omit [DecidableEq ι] in
lemma side_exact : (side a).eval v=boolean c.head.side := by
  simpa [side,cellRecord,flags] using represent_flag ha 1
omit [DecidableEq ι] in
lemma clause_exact : (clause a).eval v=c.head.clause.val := by
  simpa [clause,cellRecord,integers] using represent_int ha 7
omit [DecidableEq ι] in
lemma register_exact (i : Fin 3) : (register a i).eval v=boolean (bit (c.head.reg i)) := by
  fin_cases i
  · exact represent_flag ha 5
  · exact represent_flag ha 6
  · exact represent_flag ha 7
omit [DecidableEq ι] in
lemma notSide_exact : (neg (side a)).eval v=boolean (!c.head.side) := by
  simp only [neg_eval,side_exact ha];cases c.head.side <;> rfl
end Accessors

omit [DecidableEq ι] in
lemma zeroReg_exact (v : ι → ℕ) (i : Fin 3) : (zeroReg i).eval v=boolean (bit ((0:Reg) i)) := rfl
omit [DecidableEq ι] in
lemma zeroClause_exact {q : ℕ} [NeZero q] (v : ι → ℕ) :
    (.constant 0 : Formula ι).eval v=(0:Fin q).val := rfl
lemma equals_exact {h : ℕ} (hh : 4≤h) {a b : Expr (ι:=ι)} {v : ι → ℕ}
    {c d : Cell (2^h)} (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d) :
    (equalCells a b).eval v≠0 ↔ c=d := by
  have H := equalCells_bool a b v
  rw [← equality_exact hh a b v c d ha hb];omega

lemma unaryMove_exact {h : ℕ} (hh : 4≤h) {a b : Expr (ι:=ι)} {v : ι → ℕ} {c d : Cell (2^h)}
    (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)
    (S : Schedule (2^h)) (count truth : Formula ι)
    (hc : count.eval v=(S.count d.metadata.task).val)
    (ht : truth.eval v=boolean ((S.clause d.metadata.task d.head.clause).truth d.head.reg)) :
    (unaryMove a b count truth).eval v≠0 ↔ Unary S c d := by
  have F (p : Phase) := full_represents hb (side b) (clause b) p (register b)
    d.head.side d.head.clause d.head.reg (side_exact hb) (clause_exact hb) (register_exact hb)
  have Z (p : Phase) := full_represents hb (side b) (.constant 0) p zeroReg
    d.head.side 0 0 (side_exact hb) (zeroClause_exact v) (zeroReg_exact v)
  have A (p : Phase) := full_represents hb (side b) (clause a) p zeroReg
    d.head.side c.head.clause 0 (side_exact hb) (clause_exact ha) (zeroReg_exact v)
  have B (p : Phase) := full_represents hb (side b) (clause b) p zeroReg
    d.head.side d.head.clause 0 (side_exact hb) (clause_exact hb) (zeroReg_exact v)
  have P (p : Phase) := full_represents hb (neg (side b)) (.constant 0) p zeroReg
    (!d.head.side) 0 0 (notSide_exact hb) (zeroClause_exact v) (zeroReg_exact v)
  rw [show Unary S c d ↔ Recognizer.UnaryTest S c d from ⟨Recognizer.unary_test,Recognizer.unary_of_test⟩]
  simp only [unaryMove,Formula.any_ne_zero,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,
    exists_eq_or_imp,exists_eq_left,forall_eq_or_imp,forall_eq,first_exact hb,last_exact hb,
    equals_exact hh ha (idle_represents hb _ _ (side_exact hb)),
    equals_exact hh hb (boundary_represents hb _ _ (side_exact hb)),
    equals_exact hh ha (boundary_represents hb _ _ (side_exact hb)),
    equals_exact hh ha (F _),equals_exact hh hb (F _),
    equals_exact hh hb (Z _),equals_exact hh ha (A _),
    equals_exact hh hb (B _),equals_exact hh ha (P _),
    Formula.equal_ne_zero,Formula.add_eval,Formula.constant_eval,clause_exact ha,clause_exact hb,hc,ht,
    boolean_eq_one,Recognizer.UnaryTest]
  simp only [represent_flag hb,cellRecord,flags,boolean_eq_zero]
  rfl

end

open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def addReg (r t : Fin 3 → Formula ι) : Fin 3 → Formula ι :=
  fun i => .mod (.add (r i) (t i)) (.constant 2)
omit [DecidableEq ι] in
lemma addReg_exact {r t : Fin 3 → Formula ι} {v : ι → ℕ} {R T : Reg}
    (hr : ∀i,(r i).eval v=boolean (bit (R i))) (ht : ∀i,(t i).eval v=boolean (bit (T i))) (i : Fin 3) :
    (addReg r t i).eval v=boolean (bit ((R+T) i)) := by
  simp only [addReg,Formula.eval,hr,ht,Pi.add_apply,boolean_bit_add]

def acquireMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) : Formula ι := all
  [skeletonPair (wing a .left) (wing b' .boundary) Q,
   equalCells a (boundary a (side a)),equalCells b (idle b' (side a)),
   equalCells a' (wing a .left),equalCells b' (boundary b' (side a))]
def readLeftMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) (delta : Fin 3 → Formula ι) : Formula ι := all
  [skeletonPair (wing a .full) (wing b .right) Q,
   equalCells a (wing a .left),equalCells b (full b (side b) (clause b) .readLeft (register b)),
   equalCells a' (full a (side b) (clause b) .readLeft (addReg (register b) delta)),equalCells b' (wing b .right)]
def readRightMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) : Formula ι := all
  [skeletonPair (wing a .full) (wing b .right) Q,
   equalCells a (full a (side a) (clause a) .readRight (register a)),equalCells b (wing b .right),
   equalCells a' (wing a .left),equalCells b' (full b (side a) (clause a) .readRight (register a))]
def undoLeftMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) : Formula ι := all
  [skeletonPair (wing a .full) (wing b .right) Q,
   equalCells a (wing a .left),equalCells b (full b (side b) (clause b) .undoLeft (register b)),
   equalCells a' (full a (side b) (clause b) .undoLeft (register b)),equalCells b' (wing b .right)]
def undoRightMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) (delta : Fin 3 → Formula ι) : Formula ι := all
  [skeletonPair (wing a .full) (wing b .right) Q,
   equalCells a (full a (side a) (clause a) .undoRight (register a)),equalCells b (wing b .right),
   equalCells a' (wing a .left),equalCells b' (full b (side a) (clause a) .undoRight (addReg (register a) delta))]
def checkerCreateMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) : Formula ι := all
  [equalCells a' a,equalCells b (setChecker b' (.constant 0) (.constant 0)),
   isCore a,isPalette b',checkerHead b',equal (.add (a.1 1) (.constant 1)) Q]
def checkerAdvanceMove (a b a' b' : Expr (ι:=ι)) : Formula ι := all
  [isPalette a,isPalette b,checkerHead a,neg (equal (a.1 1) (a.1 6)),checkerIdle b,
   equalCells a' (setChecker a (.constant 1) (a.1 6)),equalCells b' (setChecker b (.constant 2) (a.1 6))]
def swapMove (a b a' b' : Expr (ι:=ι)) : Formula ι := all
  [isPalette a,isPalette b,equalCells a' b,equalCells b' a,
   equalCells (setColor a (b.1 1)) b,headFree a,headFree b]
def binaryMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) (readDelta undoDelta : Fin 3 → Formula ι) : Formula ι := any
  [acquireMove a b a' b' Q,readLeftMove a b a' b' Q readDelta,readRightMove a b a' b' Q,
   undoLeftMove a b a' b' Q,undoRightMove a b a' b' Q undoDelta,checkerCreateMove a b a' b' Q,
   checkerAdvanceMove a b a' b',swapMove a b a' b']

variable {h : ℕ} (hh : 4≤h) {a b a' b' : Expr (ι:=ι)} {v : ι → ℕ} {c d c' d' : Cell (2^h)}
variable (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)
variable (ha' : evaluate a' v=cellRecord c') (hb' : evaluate b' v=cellRecord d')
variable (Q : Formula ι) (hQ : Q.eval v=2^h)
include hh ha hb ha' hb' hQ
lemma acquireMove_exact : (acquireMove a b a' b' Q).eval v≠0 ↔ Recognizer.AcquireTest c d c' d' := by
  simp only [acquireMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    skeletonPair_exact (wing_represents ha .left) (wing_represents hb' .boundary) Q hQ,
    equals_exact hh ha (boundary_represents ha _ _ (side_exact ha)),
    equals_exact hh hb (idle_represents hb' _ _ (side_exact ha)),
    equals_exact hh ha' (wing_represents ha .left),
    equals_exact hh hb' (boundary_represents hb' _ _ (side_exact ha)),Recognizer.AcquireTest,Cell.wing]
lemma readLeftMove_exact (S : Schedule (2^h)) (delta : Fin 3 → Formula ι)
    (hd : ∀i,(delta i).eval v=boolean (bit (c.delta (S.clause c.metadata.task d.head.clause) i))) :
    (readLeftMove a b a' b' Q delta).eval v≠0 ↔ Recognizer.ReadLeftTest S c d c' d' := by
  simp only [readLeftMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    skeletonPair_exact (wing_represents ha .full) (wing_represents hb .right) Q hQ,
    equals_exact hh ha (wing_represents ha .left),
    equals_exact hh hb (full_represents hb _ _ _ _ _ _ _ (side_exact hb) (clause_exact hb) (register_exact hb)),
    equals_exact hh ha' (full_represents ha _ _ _ _ _ _ _ (side_exact hb) (clause_exact hb) (addReg_exact (register_exact hb) hd)),
    equals_exact hh hb' (wing_represents hb .right),Recognizer.ReadLeftTest,Cell.wing]
lemma readRightMove_exact : (readRightMove a b a' b' Q).eval v≠0 ↔ Recognizer.ReadRightTest c d c' d' := by
  simp only [readRightMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    skeletonPair_exact (wing_represents ha .full) (wing_represents hb .right) Q hQ,
    equals_exact hh ha (full_represents ha _ _ _ _ _ _ _ (side_exact ha) (clause_exact ha) (register_exact ha)),
    equals_exact hh hb (wing_represents hb .right),equals_exact hh ha' (wing_represents ha .left),
    equals_exact hh hb' (full_represents hb _ _ _ _ _ _ _ (side_exact ha) (clause_exact ha) (register_exact ha)),
    Recognizer.ReadRightTest,Cell.wing]
lemma undoLeftMove_exact : (undoLeftMove a b a' b' Q).eval v≠0 ↔ Recognizer.UndoLeftTest c d c' d' := by
  simp only [undoLeftMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    skeletonPair_exact (wing_represents ha .full) (wing_represents hb .right) Q hQ,
    equals_exact hh ha (wing_represents ha .left),
    equals_exact hh hb (full_represents hb _ _ _ _ _ _ _ (side_exact hb) (clause_exact hb) (register_exact hb)),
    equals_exact hh ha' (full_represents ha _ _ _ _ _ _ _ (side_exact hb) (clause_exact hb) (register_exact hb)),
    equals_exact hh hb' (wing_represents hb .right),Recognizer.UndoLeftTest,Cell.wing]
lemma undoRightMove_exact (S : Schedule (2^h)) (delta : Fin 3 → Formula ι)
    (hd : ∀i,(delta i).eval v=boolean (bit (c.delta (S.clause c.metadata.task c.head.clause) i))) :
    (undoRightMove a b a' b' Q delta).eval v≠0 ↔ Recognizer.UndoRightTest S c d c' d' := by
  simp only [undoRightMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    skeletonPair_exact (wing_represents ha .full) (wing_represents hb .right) Q hQ,
    equals_exact hh ha (full_represents ha _ _ _ _ _ _ _ (side_exact ha) (clause_exact ha) (register_exact ha)),
    equals_exact hh hb (wing_represents hb .right),equals_exact hh ha' (wing_represents ha .left),
    equals_exact hh hb' (full_represents hb _ _ _ _ _ _ _ (side_exact ha) (clause_exact ha) (addReg_exact (register_exact ha) hd)),
    Recognizer.UndoRightTest,Cell.wing]
lemma checkerCreateMove_exact : (checkerCreateMove a b a' b' Q).eval v≠0 ↔ Recognizer.CheckerCreateTest c d c' d' := by
  have hc := setChecker_represents hb' (.constant 0) (.constant 0) Palette.Check.idle rfl rfl
  simp only [checkerCreateMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    equals_exact hh ha' ha,equals_exact hh hb hc,core_exact ha,palette_exact hb',checkerHead_exact hb',
    Formula.equal_ne_zero,Formula.add_eval,Formula.constant_eval,hQ]
  cases hp : c.pos <;> cases hd : d'.pos <;> cases hh' : d'.checker <;>
    simp [Recognizer.CheckerCreateTest,Cell.isCore,Cell.isPalette,hp,hd,hh',
      represent_int ha,cellRecord,integers,positionIndex]
omit hQ in
lemma checkerAdvanceMove_exact : (checkerAdvanceMove a b a' b').eval v≠0 ↔ Recognizer.CheckerAdvanceTest c d c' d' := by
  simp only [checkerAdvanceMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    palette_exact ha,palette_exact hb,checkerHead_exact ha,checkerIdle_exact hb,Formula.neg_ne_zero,Formula.equal_ne_zero]
  cases hp : c.pos <;> cases hd : d.pos <;> cases hk : c.checker <;>
    simp [Recognizer.CheckerAdvanceTest,Cell.isPalette,hp,hd,hk]
  rename_i x y z
  have hi : (a.1 6).eval v=z.val := by simpa [cellRecord,integers,hk,checkerIndex] using represent_int ha 6
  simp only [← ne_eq]
  rw [equals_exact hh ha' (setChecker_represents ha (.constant 1) _ (.passed z) rfl hi),
    equals_exact hh hb' (setChecker_represents hb (.constant 2) _ (.head z) rfl hi)]
  simp only [represent_int ha,cellRecord,integers,hp,hk,positionIndex,checkerIndex]
  change (x.val≠z.val ∧ _) ↔ (x≠z ∧ _)
  simp only [ne_eq,Fin.val_inj]
omit hQ in
lemma swapMove_exact : (swapMove a b a' b').eval v≠0 ↔ Recognizer.SwapTest c d c' d' := by
  simp only [swapMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    palette_exact ha,palette_exact hb,equals_exact hh ha' hb,equals_exact hh hb' ha,headFree_exact ha,headFree_exact hb]
  cases hp : c.pos <;> cases hd : d.pos <;> simp [Recognizer.SwapTest,Cell.isPalette,hp,hd]
  rename_i x y
  have hi : (b.1 1).eval v=y.val := by simpa [cellRecord,integers,hd,positionIndex] using represent_int hb 1
  simp only [← ne_eq]
  rw [equals_exact hh (setColor_represents ha _ _ hi) hb]
  simp
lemma binaryMove_exact (S : Schedule (2^h)) (rd ud : Fin 3 → Formula ι)
    (hrd : ∀i,(rd i).eval v=boolean (bit (c.delta (S.clause c.metadata.task d.head.clause) i)))
    (hud : ∀i,(ud i).eval v=boolean (bit (c.delta (S.clause c.metadata.task c.head.clause) i))) :
    (binaryMove a b a' b' Q rd ud).eval v≠0 ↔ Binary S c d c' d' := by
  rw [show Binary S c d c' d' ↔ Recognizer.BinaryTest S c d c' d' from
    ⟨Recognizer.binary_test,Recognizer.binary_of_test⟩]
  simp only [binaryMove,Formula.any_ne_zero,List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,exists_eq_left,
    acquireMove_exact hh ha hb ha' hb' Q hQ,readLeftMove_exact hh ha hb ha' hb' Q hQ S rd hrd,
    readRightMove_exact hh ha hb ha' hb' Q hQ,undoLeftMove_exact hh ha hb ha' hb' Q hQ,
    undoRightMove_exact hh ha hb ha' hb' Q hQ S ud hud,checkerCreateMove_exact hh ha hb ha' hb' Q hQ,
    checkerAdvanceMove_exact hh ha hb ha' hb',swapMove_exact hh ha hb ha' hb',Recognizer.BinaryTest]
end SourceBurnside.CellFormula

namespace SourceBurnside.PredicateFormula
section
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
open CellFormula
variable {ι : Type} [DecidableEq ι]

structure Table where
  count : CellFormula.Expr (ι:=ι) → Formula ι
  clause : CellFormula.Expr (ι:=ι) → Formula ι → ClauseFormula.Expr (ι:=ι)
def Table.Represents {q : ℕ} (P : Table (ι:=ι)) (v : ι → ℕ) (S : Schedule q) : Prop :=
  ∀a (c : Cell q), CellFormula.evaluate a v=cellRecord c →
    (P.count a).eval v=(S.count c.metadata.task).val ∧
    ∀j (J : Fin q),j.eval v=J.val → ClauseFormula.Represents (P.clause a j) v (S.clause c.metadata.task J)

def Table.truth (P : Table (ι:=ι)) (a : CellFormula.Expr (ι:=ι)) : Formula ι :=
  ClauseFormula.truth (P.clause a (CellFormula.clause a)) (register a)
def Table.delta (P : Table (ι:=ι)) (a b : CellFormula.Expr (ι:=ι)) : Fin 3 → Formula ι :=
  ClauseFormula.delta (P.clause a (CellFormula.clause b)) a
lemma Table.truth_exact {q : ℕ} (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule q}
    (hP : P.Represents v S) {a : CellFormula.Expr (ι:=ι)} {c : Cell q} (ha : CellFormula.evaluate a v=cellRecord c) :
    (P.truth a).eval v=boolean ((S.clause c.metadata.task c.head.clause).truth c.head.reg) :=
  ClauseFormula.truth_value ((hP a c ha).2 _ c.head.clause (clause_exact ha)) (register_exact ha)
lemma Table.delta_exact {q : ℕ} [NeZero q] (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule q}
    (hP : P.Represents v S) {a b : CellFormula.Expr (ι:=ι)} {c d : Cell q}
    (ha : CellFormula.evaluate a v=cellRecord c) (hb : CellFormula.evaluate b v=cellRecord d) (i : Fin 3) :
    (P.delta a b i).eval v=boolean (bit (c.delta (S.clause c.metadata.task d.head.clause) i)) :=
  ClauseFormula.delta_exact ((hP a c ha).2 _ d.head.clause (clause_exact hb)) ha i

def unaryRep (P : Table (ι:=ι)) (size : Formula ι) (a b : CellFormula.Expr (ι:=ι)) : Formula ι :=
  all [formats a size (P.count a),formats b size (P.count b),
    or (unaryMove a b (P.count b) (P.truth b)) (unaryMove b a (P.count a) (P.truth a))]
def binaryRep (P : Table (ι:=ι)) (size Q : Formula ι) (a b a' b' : CellFormula.Expr (ι:=ι)) : Formula ι :=
  all [formats a size (P.count a),formats b size (P.count b),formats a' size (P.count a'),formats b' size (P.count b'),
    or (binaryMove a b a' b' Q (P.delta a b) (P.delta a a))
      (binaryMove a' b' a b Q (P.delta a' b') (P.delta a' a'))]
lemma unaryRep_exact {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {size : Formula ι} (hs : size.eval v=n)
    {a b : CellFormula.Expr (ι:=ι)} {c d : Cell (2^h)}
    (ha : CellFormula.evaluate a v=cellRecord c) (hb : CellFormula.evaluate b v=cellRecord d) :
    (unaryRep P size a b).eval v≠0 ↔ Replacement S n [c] [d] := by
  rw [←Recognizer.replacementTest_iff]
  simp only [unaryRep,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    Formula.or_ne_zero,formats_exact ha S size (P.count a) n hs (hP a c ha).1,
    formats_exact hb S size (P.count b) n hs (hP b d hb).1,
    unaryMove_exact hh ha hb S (P.count b) (P.truth b) (hP b d hb).1 (P.truth_exact hP hb),
    unaryMove_exact hh hb ha S (P.count a) (P.truth a) (hP a c ha).1 (P.truth_exact hP ha),Recognizer.ReplacementTest]
lemma binaryRep_exact {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {size Q : Formula ι} (hs : size.eval v=n) (hQ : Q.eval v=2^h)
    {a b a' b' : CellFormula.Expr (ι:=ι)} {c d c' d' : Cell (2^h)}
    (ha : CellFormula.evaluate a v=cellRecord c) (hb : CellFormula.evaluate b v=cellRecord d)
    (ha' : CellFormula.evaluate a' v=cellRecord c') (hb' : CellFormula.evaluate b' v=cellRecord d') :
    (binaryRep P size Q a b a' b').eval v≠0 ↔ Replacement S n [c,d] [c',d'] := by
  rw [←Recognizer.replacementTest_iff]
  simp only [binaryRep,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    Formula.or_ne_zero,formats_exact ha S size (P.count a) n hs (hP a c ha).1,
    formats_exact hb S size (P.count b) n hs (hP b d hb).1,
    formats_exact ha' S size (P.count a') n hs (hP a' c' ha').1,
    formats_exact hb' S size (P.count b') n hs (hP b' d' hb').1,
    binaryMove_exact hh ha hb ha' hb' Q hQ S (P.delta a b) (P.delta a a) (P.delta_exact hP ha hb) (P.delta_exact hP ha ha),
    binaryMove_exact hh ha' hb' ha hb Q hQ S (P.delta a' b') (P.delta a' a') (P.delta_exact hP ha' hb') (P.delta_exact hP ha' ha'),
    Recognizer.ReplacementTest]
end

open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def clauseCount (β g : ℕ) (T W : Formula ι) : Formula ι :=
  .add (.add (.mul (.constant (2*β)) W) (.mul (.constant (2*β)) (.sub T (.constant 1))))
    (.add (.mul (.mul (.constant (3*g+2*β)) (.sub W (.constant 2))) (.sub T (.constant 1))) (.constant β))
omit [DecidableEq ι] in
lemma clauseCount_exact (β g : ℕ) (T W : Formula ι) (v : ι → ℕ) :
    (clauseCount β g T W).eval v=Tableau.Layout.clauseCount β g (T.eval v) (W.eval v) := by
  simp [clauseCount,eval,Tableau.Layout.clauseCount,Nat.add_assoc]

def physical (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank origin accept : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    (T W O code codeLength H : Formula ι) : Table (ι:=ι) where
  count _ := clauseCount β g T W
  clause a j :=
    let initial := InitialFormula.cell blank origin encoding O
      (InitialFormula.inputPiece code codeLength H (.add (a.1 3) (.constant 1)) (a.2 0))
    ClauseFormula.choose (less j (clauseCount β g T W))
      (PhysicalFormula.clauseAt β g c output initial blank accept T W O j)
      PhysicalFormula.fallback

def initial {q β g T W : ℕ} (L : Addressable.Layout q β g T W)
    (blank origin : Fin β → Bool) (encoding : Bool → Fin β → Bool) (code : List Bool) (H : ℕ)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (task : Task) : Fin W → Fin β → Addressable.InputBit q :=
  InitialFormula.row blank origin encoding L.origin.val
    (InitialFormula.sourceInput code H (task.arity.val+1) task.zeroTask hd hdq (by omega) (by have := task.arity.isLt;omega))

lemma physical_exact {q β g T W H : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank origin accept : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    (code : List Bool) (hd : 0<10000*H) (hdq : 10000*H≤q)
    {T' W' O C N H' : Formula ι} {v : ι → ℕ}
    (hT : T'.eval v=T) (hW : W'.eval v=W) (hO : O.eval v=L.origin.val)
    (hC : C.eval v=binaryValue code) (hN : N.eval v=code.length) (hH : H'.eval v=H) :
    (physical β g c output blank origin accept encoding T' W' O C N H').Represents v
      (L.schedule c output (initial L blank origin encoding code H hd hdq) blank accept) := by
  intro a A ha
  have hcount : (clauseCount β g T' W').eval v=Tableau.Layout.clauseCount β g T W := by
    rw [clauseCount_exact,hT,hW]
  refine ⟨hcount,?_⟩
  intro j J hj
  change ClauseFormula.Represents (ClauseFormula.choose _ _ _) v _
  by_cases hJ : J.val<Tableau.Layout.clauseCount β g T W
  · simp only [Addressable.Layout.schedule,dite_eq_left hJ]
    apply ClauseFormula.choose_true (by simp [hj,hcount,hJ])
    apply PhysicalFormula.clauseAt_exact L c output blank accept hT hW hO _ ⟨J.val,hJ⟩ hj
    intro p P hp r
    apply InitialFormula.cell_exact blank origin encoding P r hO hp
    apply InitialFormula.inputPiece_exact code A.metadata.zeroTask hd hdq _ _ hC hN hH
    · simp [eval,CellFormula.represent_int ha,cellRecord,integers,Meta.task]
    · simp [CellFormula.represent_flag ha,cellRecord,flags]
  · simp only [Addressable.Layout.schedule,dite_eq_right hJ]
    apply ClauseFormula.choose_false (by simp [less_eval,hj,hcount,hJ])
    exact ClauseFormula.unit_exact (ClauseFormula.fixedReading_exact (by rfl)) rfl
end SourceBurnside.PredicateFormula

namespace SourceBurnside.Structured.Device.Formula
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
def bind (f : ι → Formula κ) : Formula ι → Formula κ
  | .read i => f i
  | .constant a => .constant a
  | .add x y => .add (x.bind f) (y.bind f)
  | .sub x y => .sub (x.bind f) (y.bind f)
  | .mul x y => .mul (x.bind f) (y.bind f)
  | .div x y => .div (x.bind f) (y.bind f)
  | .mod x y => .mod (x.bind f) (y.bind f)
  | .le x y => .le (x.bind f) (y.bind f)
  | .powTwo x => .powTwo (x.bind f)
  | .bitLength x => .bitLength (x.bind f)
  | .branch c a b => .branch (c.bind f) (a.bind f) (b.bind f)
omit [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma bind_eval (f : ι → Formula κ) (e : Formula ι) (v : κ → ℕ) :
    (e.bind f).eval v=e.eval (fun i => (f i).eval v) := by
  induction e <;> simp_all [bind,eval]
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.PredicateFormula
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
open CellFormula
variable {ι : Type} [DecidableEq ι]
omit [DecidableEq ι] in
lemma branch_value (c a b : Formula ι) (v : ι → ℕ) :
    (Formula.branch c a b).eval v=if c.eval v=0 then b.eval v else a.eval v := rfl
def valid (H W : Formula ι) : Formula ι := RawFormula.valid.bind ![H,W]
omit [DecidableEq ι] in
lemma valid_value {h : ℕ} (hh : 0<h) (w : Raw h) {H W : Formula ι} {v : ι → ℕ}
    (hH : H.eval v=h) (hW : W.eval v=natCode w) :
    (valid H W).eval v=boolean (decode hh w).isSome := by
  have hv : (fun i : Fin 2 => (![H,W] i).eval v)=RawFormula.inputs h (natCode w) := by
    funext i;fin_cases i <;> simp [RawFormula.inputs,hH,hW]
  rw [valid,bind_eval,hv]
  have hb := RawFormula.valid_boolean h (natCode w)
  have he := RawFormula.accepts_iff_decode hh w
  cases hd : decode hh w with
  | none => simp only [hd,Option.isSome_none,Bool.false_eq_true,iff_false] at he; simpa [hd,boolean] using (show RawFormula.valid.eval (RawFormula.inputs h (natCode w))=0 by omega)
  | some c => simp only [hd,Option.isSome_some] at he;simpa [hd,boolean] using he.mpr trivial

omit [DecidableEq ι] in
lemma rawRepresents {h : ℕ} (hh : 4≤h) (w : Raw h) {H W : Formula ι} {v : ι → ℕ}
    {c : Cell (2^h)} (hc : decode (by omega) w=some c) (hH : H.eval v=h) (hW : W.eval v=natCode w) :
    CellFormula.evaluate (CellFormula.ofRaw H W) v=cellRecord c := by
  apply ofRaw_represents hh c H W v hH
  rw [hW,(decode_eq_some_iff hh w c).mp hc]

def rawUnaryZero (P : Table (ι:=ι)) (H size W : Formula ι) : Formula ι :=
  let a := ofRaw H W
  .branch (valid H W) (unaryZero a size (P.count a) (P.truth a)) (.constant 1)
def rawBinaryZero (H Q W Z : Formula ι) : Formula ι :=
  .branch (and (valid H W) (valid H Z)) (binaryZero (ofRaw H W) (ofRaw H Z) Q) (.constant 0)
def rawUnaryRep (P : Table (ι:=ι)) (H size W Z : Formula ι) : Formula ι :=
  .branch (and (valid H W) (valid H Z)) (unaryRep P size (ofRaw H W) (ofRaw H Z)) (.constant 0)
def rawBinaryRep (P : Table (ι:=ι)) (H size Q W X Y Z : Formula ι) : Formula ι :=
  .branch (all [valid H W,valid H X,valid H Y,valid H Z])
    (binaryRep P size Q (ofRaw H W) (ofRaw H X) (ofRaw H Y) (ofRaw H Z)) (.constant 0)

lemma rawUnaryZero_exact {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size W : Formula ι} (w : Raw h)
    (hH : H.eval v=h) (hs : size.eval v=n) (hW : W.eval v=natCode w) :
    (rawUnaryZero P H size W).eval v≠0 ↔ Codec.unaryZero (by omega) S n w := by
  have hv := valid_value (show 0<h by omega) w hH hW
  cases hd : decode (show 0<h by omega) w with
  | none => simp [rawUnaryZero,branch_value,hv,hd,Codec.unaryZero]
  | some c =>
    have hc := rawRepresents hh w hd hH hW
    simpa only [rawUnaryZero,branch_value,hv,hd,Option.isSome_some,boolean_true,Nat.one_ne_zero,ite_false,Codec.unaryZero] using
      (unaryZero_exact hc S size (P.count (ofRaw H W)) (P.truth (ofRaw H W)) n hs (hP _ c hc).1 (P.truth_exact hP hc))
lemma rawBinaryZero_exact {h : ℕ} (hh : 4≤h) {v : ι → ℕ} {H Q W Z : Formula ι} (w z : Raw h)
    (hH : H.eval v=h) (hQ : Q.eval v=2^h) (hW : W.eval v=natCode w) (hZ : Z.eval v=natCode z) :
    (rawBinaryZero H Q W Z).eval v≠0 ↔ Codec.binaryZero (by omega) w z := by
  have hw := valid_value (show 0<h by omega) w hH hW
  have hz := valid_value (show 0<h by omega) z hH hZ
  cases hdw : decode (show 0<h by omega) w <;> cases hdz : decode (show 0<h by omega) z
  all_goals try simp [rawBinaryZero,branch_value,and_eval,hw,hz,hdw,hdz,Codec.binaryZero]
  rename_i c d
  have hc := rawRepresents hh w hdw hH hW
  have hd := rawRepresents hh z hdz hH hZ
  simpa only [rawBinaryZero,branch_value,and_eval,hw,hz,hdw,hdz,Option.isSome_some,boolean_true,Nat.one_ne_zero,ite_false,Codec.binaryZero] using
    (binaryZero_exact hc hd Q hQ)
lemma rawUnaryRep_exact {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size W Z : Formula ι} (w z : Raw h)
    (hH : H.eval v=h) (hs : size.eval v=n) (hW : W.eval v=natCode w) (hZ : Z.eval v=natCode z) :
    (rawUnaryRep P H size W Z).eval v≠0 ↔ Codec.replacement (by omega) S n [w] [z] := by
  have hw := valid_value (show 0<h by omega) w hH hW
  have hz := valid_value (show 0<h by omega) z hH hZ
  cases hdw : decode (show 0<h by omega) w <;> cases hdz : decode (show 0<h by omega) z
  all_goals try simp [rawUnaryRep,branch_value,and_eval,hw,hz,hdw,hdz,Codec.replacement,decodeWord]
  rename_i c d
  have hc := rawRepresents hh w hdw hH hW
  have hd := rawRepresents hh z hdz hH hZ
  simpa only [rawUnaryRep,branch_value,and_eval,hw,hz,hdw,hdz,Option.isSome_some,boolean_true,Nat.one_ne_zero,ite_false,
    Codec.replacement,decodeWord,Option.bind_some,Option.some.injEq] using
    (unaryRep_exact hh P hP hs hc hd)
end SourceBurnside.PredicateFormula

end OAI
