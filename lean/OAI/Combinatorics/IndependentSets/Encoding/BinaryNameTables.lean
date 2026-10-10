import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.FiniteScan

namespace OAI

namespace LargeIndependentSets.BinaryNames
open IndependentSetsCut.CounterMachine
open scoped BigOperators

def raw (s : List Bool) (i : ℕ) : Bool := (s[i]?).getD false

lemma raw_out (s : List Bool) (i : ℕ) (hi : s.length ≤ i) : raw s i = false := by
  simp [raw,List.getElem?_eq_none hi]

lemma end_exists (s : List Bool) (p : ℕ) : ∃ t, raw s (p+1+2*t) = false :=
  ⟨s.length,raw_out s _ (by omega)⟩

def nameLength (s : List Bool) (p : ℕ) : ℕ := Nat.find (end_exists s p)

lemma nameLength_le (s : List Bool) (p : ℕ) : nameLength s p ≤ s.length :=
  Nat.find_min' _ (raw_out s _ (by omega))
lemma nameLength_end (s : List Bool) (p : ℕ) : raw s (p+1+2*nameLength s p) = false :=
  Nat.find_spec (end_exists s p)
lemma nameLength_before (s : List Bool) (p j : ℕ) (hj : j<nameLength s p) :
    raw s (p+1+2*j) = true := by
  have h := Nat.find_min (end_exists s p) hj
  cases he : raw s (p+1+2*j) <;> simp_all

def payload (s : List Bool) (p : ℕ) : List Bool :=
  (List.range (nameLength s p)).map (fun j => raw s (p+2+2*j))

lemma payload_eq_iff (s : List Bool) (p q : ℕ) :
    payload s p = payload s q ↔ nameLength s p = nameLength s q ∧
      ∀ j<nameLength s p, raw s (p+2+2*j) = raw s (q+2+2*j) := by
  constructor
  · intro h
    have hl : nameLength s p=nameLength s q := by simpa [payload] using congrArg List.length h
    refine ⟨hl,?_⟩
    intro j hj
    have he := congrArg (fun l : List Bool => l[j]?) h
    simpa [payload,List.getElem?_range,hl,hl ▸ hj] using he
  · rintro ⟨hl,he⟩
    unfold payload
    rw [← hl]
    apply List.map_congr_left
    intro j hj
    exact he j (List.mem_range.mp hj)

lemma key_exists (s : List Bool) (p : ℕ) :
    ∃ q, q ≤ s.length ∧ payload s q = payload s (min p s.length) :=
  ⟨min p s.length,Nat.min_le_right _ _,rfl⟩

def key (s : List Bool) (p : ℕ) : ℕ := Nat.find (key_exists s p)
lemma key_le (s : List Bool) (p : ℕ) : key s p ≤ s.length := (Nat.find_spec (key_exists s p)).1
lemma key_payload (s : List Bool) (p : ℕ) (hp : p ≤ s.length) :
    payload s (key s p) = payload s p := by
  simpa only [key,Nat.min_eq_left hp] using (Nat.find_spec (key_exists s p)).2
lemma key_eq (s : List Bool) (p q : ℕ) (hp : p ≤ s.length) (hq : q ≤ s.length)
    (he : payload s p = payload s q) : key s p = key s q := by
  apply le_antisymm
  · apply Nat.find_min'
    exact ⟨key_le s q,by rw [Nat.min_eq_left hp,key_payload s q hq,he]⟩
  · apply Nat.find_min'
    exact ⟨key_le s p,by rw [Nat.min_eq_left hq,key_payload s p hp,he]⟩

def next (s : List Bool) (p : ℕ) : ℕ := p+2+2*nameLength s p

lemma raw_middle (pre mid post : List Bool) (i : ℕ) (hi : i < mid.length) :
    raw (pre++mid++post) (pre.length+i) = raw mid i := by
  rw [show pre++mid++post=pre++(mid++post) by rw [List.append_assoc]]
  unfold raw
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hi]

lemma frame_eq (s : List Bool) : LargeIndependentSets.frame s = IndependentSetsCut.CounterMachine.frame s := by
  induction s with
  | nil => rfl
  | cons b s ih => simp only [LargeIndependentSets.frame,IndependentSetsCut.CounterMachine.frame,ih]

lemma literal_marker (l : Literal) (j : ℕ) (hj : j ≤ l.name.bits.length) :
    raw (literalBits l) (1+2*j) = decide (j<l.name.bits.length) := by
  simp only [raw,literalBits,nameBits,frame_eq,show 1+2*j=2*j+1 by omega,
    List.getElem?_cons_succ,IndependentSetsCut.CounterMachine.frame_get]
  simp [show 2*j%2=0 by omega,show 2*j<2*l.name.bits.length ↔ j<l.name.bits.length by omega]

lemma literal_payload (l : Literal) (j : ℕ) (hj : j<l.name.bits.length) :
    raw (literalBits l) (2+2*j) = raw l.name.bits j := by
  simp only [raw,literalBits,nameBits,frame_eq,show 2+2*j=(2*j+1)+1 by omega,
    List.getElem?_cons_succ,IndependentSetsCut.CounterMachine.frame_get]
  simp [show 2*j+1<2*l.name.bits.length by omega,
    show (2*j+1)/2=j by omega]

lemma nameLength_literal (pre post : List Bool) (l : Literal) :
    nameLength (pre++literalBits l++post) pre.length = l.name.bits.length := by
  apply (Nat.find_eq_iff _).mpr
  have hl : (literalBits l).length=2*l.name.bits.length+2 := by
    simp [literalBits,nameBits,LargeIndependentSets.frame_length]
  constructor
  · rw [show pre.length+1+2*l.name.bits.length=pre.length+(1+2*l.name.bits.length) by omega,
      raw_middle _ _ _ _ (by omega),literal_marker l _ le_rfl]
    simp
  · intro j hj
    rw [show pre.length+1+2*j=pre.length+(1+2*j) by omega,
      raw_middle _ _ _ _ (by omega),literal_marker l j hj.le]
    simp [hj]

lemma payload_literal (pre post : List Bool) (l : Literal) :
    payload (pre++literalBits l++post) pre.length = l.name.bits := by
  unfold payload
  rw [nameLength_literal]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range]
    have hl : (literalBits l).length=2*l.name.bits.length+2 := by
      simp [literalBits,nameBits,LargeIndependentSets.frame_length]
    rw [show pre.length+2+2*i=pre.length+(2+2*i) by omega,
      raw_middle _ _ _ _ (by omega),literal_payload l i hi']
    simp [raw,List.getElem?_eq_getElem hi']

lemma next_literal (pre post : List Bool) (l : Literal) :
    next (pre++literalBits l++post) pre.length = (pre++literalBits l).length := by
  rw [next,nameLength_literal]
  simp [literalBits,nameBits,LargeIndependentSets.frame_length]
  omega

def rawExpr (i : Expr) : Expr :=
  Expr.cond (Expr.lt i FiniteScan.nExpr) (FiniteScan.inputExpr i) (.const 0)

lemma rawExpr_eval {m : ℕ} (s : FiniteScan.State m) (i : Expr) (a : ℕ → ℕ) :
    (rawExpr i).eval s.bits a = if raw s.input (i.eval s.bits a) then 1 else 0 := by
  by_cases hi : i.eval s.bits a<s.input.length
  · simp [rawExpr,hi,FiniteScan.read_input s _ hi,Expr.bitValue,raw]
  · simp [rawExpr,Expr.eval,hi,raw_out s.input (i.eval s.bits a) (by omega)]

def nameLengthExpr (p : Expr) : Expr := Expr.least (.add FiniteScan.nExpr (.const 1))
  (.zero (rawExpr (.add (.add (p.rename Nat.succ) (.const 1)) (.mul (.const 2) (.arg 0)))))

lemma nameLengthExpr_eval {m : ℕ} (s : FiniteScan.State m) (p : Expr) (a : ℕ → ℕ) :
    (nameLengthExpr p).eval s.bits a = nameLength s.input (p.eval s.bits a) := by
  unfold nameLengthExpr
  apply Expr.least_eq
  · simpa [Expr.eval] using Nat.lt_succ_of_le (nameLength_le s.input _)
  · simp [Expr.eval,rawExpr_eval,Expr.bind,nameLength_end]
  · intro j hj
    simp [Expr.eval,rawExpr_eval,Expr.bind,nameLength_before s.input _ j hj]

def payloadEqExpr (p q : Expr) : Expr := .mul (Expr.equal (nameLengthExpr p) (nameLengthExpr q))
  (.zero (.sum (nameLengthExpr p) (.zero (Expr.equal
    (rawExpr (.add (.add (p.rename Nat.succ) (.const 2)) (.mul (.const 2) (.arg 0))))
    (rawExpr (.add (.add (q.rename Nat.succ) (.const 2)) (.mul (.const 2) (.arg 0))))))))

lemma payloadEqExpr_eval {m : ℕ} (s : FiniteScan.State m) (p q : Expr) (a : ℕ → ℕ) :
    (payloadEqExpr p q).eval s.bits a =
      if payload s.input (p.eval s.bits a) = payload s.input (q.eval s.bits a) then 1 else 0 := by
  have hb (x y : Bool) : ((if x then 1 else 0 : ℕ) = if y then 1 else 0) ↔ x=y := by
    cases x <;> cases y <;> decide
  simp only [payloadEqExpr,Expr.eval,Expr.equal_eval,nameLengthExpr_eval,rawExpr_eval,
    Expr.rename_eval,Expr.bind,hb]
  have hz : (∑ j ∈ Finset.range (nameLength s.input (p.eval s.bits a)),
      if raw s.input (p.eval s.bits a+2+2*j)=raw s.input (q.eval s.bits a+2+2*j) then 0 else 1)=0 ↔
      ∀ j<nameLength s.input (p.eval s.bits a),
        raw s.input (p.eval s.bits a+2+2*j)=raw s.input (q.eval s.bits a+2+2*j) := by
    simp [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [show ∀ b : Prop, ∀ _ : Decidable b, (if (if b then (1:ℕ) else 0)=0 then 1 else 0) =
      if b then 0 else 1 by intros; split_ifs <;> simp_all]
  simp only [hz,payload_eq_iff]
  by_cases h : nameLength s.input (p.eval s.bits a)=nameLength s.input (q.eval s.bits a)
  · simp [h]
  · simp [h]

def minExpr (a b : Expr) : Expr := Expr.cond (Expr.le a b) a b
@[simp] lemma minExpr_eval (x y : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (minExpr x y).eval s a = min (x.eval s a) (y.eval s a) := by
  by_cases h : x.eval s a ≤ y.eval s a <;> simp [minExpr,h, min_def]

def keyExpr (p : Expr) : Expr := Expr.least (.add FiniteScan.nExpr (.const 1))
  (payloadEqExpr (.arg 0) ((minExpr p FiniteScan.nExpr).rename Nat.succ))

lemma keyExpr_eval {m : ℕ} (s : FiniteScan.State m) (p : Expr) (a : ℕ → ℕ) :
    (keyExpr p).eval s.bits a = key s.input (p.eval s.bits a) := by
  unfold keyExpr
  apply Expr.least_eq
  · simpa [Expr.eval] using Nat.lt_succ_of_le (key_le s.input _)
  · simp only [payloadEqExpr_eval,Expr.eval,Expr.bind,Expr.rename_eval,minExpr_eval,FiniteScan.nExpr_eval]
    have hk : payload s.input (key s.input (p.eval s.bits a)) =
        payload s.input (min (p.eval s.bits a) s.input.length) :=
      (Nat.find_spec (key_exists s.input (p.eval s.bits a))).2
    simpa only [hk,ite_true] using (show (1:ℕ)≠0 by decide)
  · intro j hj
    have hjn : j ≤ s.input.length := (Nat.le_of_lt hj).trans (key_le s.input _)
    have hne : payload s.input j ≠ payload s.input (min (p.eval s.bits a) s.input.length) := by
      intro he
      exact Nat.find_min (key_exists s.input (p.eval s.bits a)) hj ⟨hjn,he⟩
    simp [payloadEqExpr_eval,Expr.eval,Expr.bind,hne]

def nextExpr (p : Expr) : Expr := .add (.add p (.const 2)) (.mul (.const 2) (nameLengthExpr p))
lemma nextExpr_eval {m : ℕ} (s : FiniteScan.State m) (p : Expr) (a : ℕ → ℕ) :
    (nextExpr p).eval s.bits a = next s.input (p.eval s.bits a) := by
  simp [nextExpr,Expr.eval,nameLengthExpr_eval,next]

end LargeIndependentSets.BinaryNames

end OAI
