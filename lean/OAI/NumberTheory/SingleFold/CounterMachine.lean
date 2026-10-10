import OAI.NumberTheory.SingleFold.Packed

namespace OAI

namespace SingleFold.Counter

section
inductive Instr (Q J : Type)
  | halt
  | inc (j : J) (p : Q)
  | test (j : J) (pzero pdec : Q)
  deriving DecidableEq

structure Machine (Q J : Type) where
  instr : Q → Instr Q J
  start : Q
  halt : Q
  halt_iff : ∀q,instr q=Instr.halt ↔ q=halt

structure Cfg (Q J : Type) where
  state : Q
  value : J → ℕ

variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
def next (M : Machine Q J) (c : Cfg Q J) : Cfg Q J :=
  match M.instr c.state with
  | .halt => c
  | .inc j p => ⟨p,Function.update c.value j (c.value j+1)⟩
  | .test j p0 pd => if c.value j=0 then ⟨p0,c.value⟩ else ⟨pd,Function.update c.value j (c.value j-1)⟩
def run (M : Machine Q J) (d : J → ℕ) (t : ℕ) : Cfg Q J := (next M)^[t] ⟨M.start,d⟩
omit [DecidableEq Q] in
@[simp] lemma run_zero (M : Machine Q J) (d : J → ℕ) : run M d 0=⟨M.start,d⟩ := rfl
omit [DecidableEq Q] in
lemma run_succ (M : Machine Q J) (d : J → ℕ) (t : ℕ) : run M d (t+1)=next M (run M d t) :=
  Function.iterate_succ_apply' _ _ _
def HaltsAt (M : Machine Q J) (d : J → ℕ) (T : ℕ) : Prop :=
  (run M d T).state=M.halt ∧ ∀t < T,(run M d t).state≠M.halt
def Halts (M : Machine Q J) (d : J → ℕ) : Prop := ∃T,HaltsAt M d T
omit [DecidableEq Q] in
lemma haltsAt_unique {M : Machine Q J} {d : J → ℕ} {T U : ℕ}
    (hT : HaltsAt M d T) (hU : HaltsAt M d U) : T=U := by
  rcases lt_trichotomy T U with h|h|h
  · exact False.elim (hU.2 T h hT.1)
  · exact h
  · exact False.elim (hT.2 U h hU.1)
omit [DecidableEq Q] in
lemma value_bound (M : Machine Q J) (d : J → ℕ) (t : ℕ) (j : J) : (run M d t).value j ≤ d j+t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [run_succ,next]
    split
    · omega
    · rename_i k p hk
      dsimp
      by_cases h : j=k
      · subst j; simp; omega
      · simp [Function.update_of_ne h]; omega
    · rename_i k p0 pd hk
      split
      · change (run M d t).value j ≤ d j+(t+1)
        omega
      · dsimp
        by_cases h : j=k
        · subst j; simp; omega
        · simp [Function.update_of_ne h]; omega

def dest (M : Machine Q J) (q : Q) (b : Bool) : Option Q :=
  match M.instr q,b with
  | .inc _ p,false => some p
  | .test _ p0 _,false => some p0
  | .test _ _ pd,true => some pd
  | _,_ => none

structure Witness (Q J : Type) where
  w : ℕ
  B : ℕ
  b : ℕ
  k : ℕ
  H : ℕ
  last : ℕ
  mask : ℕ
  state : Q → ℕ
  zeroBranch : Q → ℕ
  decBranch : Q → ℕ
  complement : Q → ℕ
  counter : Option J → ℕ
  final : Option J → ℕ
  rem : Option J → ℕ

variable [Fintype Q] [Fintype J]
def baseC (Q : Type) [Fintype Q] (d : J → ℕ) : ℕ := 1+Fintype.card Q+∑j,d j

def arc (M : Machine Q J) (v : Witness Q J) (q : Q) (b : Bool) : ℕ :=
  match M.instr q,b with
  | .inc _ _,false => v.state q
  | .test _ _ _,false => v.zeroBranch q
  | .test _ _ _,true => v.decBranch q
  | _,_ => 0

def incoming (M : Machine Q J) (v : Witness Q J) (p : Q) : ℕ :=
  ∑q,∑b : Bool,if dest M q b=some p then arc M v q b else 0

def increments (M : Machine Q J) (v : Witness Q J) (j : J) : ℕ :=
  ∑q, match M.instr q with | .inc i _ => if i=j then v.state q else 0 | _ => 0

def decrements (M : Machine Q J) (v : Witness Q J) (j : J) : ℕ :=
  ∑q, match M.instr q with | .test i _ _ => if i=j then v.decBranch q else 0 | _ => 0

def Bits (x y : ℕ) : Prop := ∀i, x/2^i%2 ≤ y/2^i%2

structure System (M : Machine Q J) (d : J → ℕ) (v : Witness Q J) : Prop where
  power : v.B=2^v.w
  base : v.B=4*v.b
  bound : 2*baseC Q d < v.B
  length : 0 < v.k
  full : v.H=v.B^v.k
  last : v.B*v.last=v.H
  mask : (v.B-1)*v.mask=v.H-1
  state_bits : ∀q,Bits (v.state q) v.mask
  partition : (∑q,v.state q)=v.mask
  branch : ∀q,match M.instr q with
    | .test _ _ _ => Bits (v.zeroBranch q) (v.state q) ∧ Bits (v.decBranch q) (v.state q) ∧
        v.zeroBranch q+v.decBranch q=v.state q ∧ v.zeroBranch q+v.complement q=v.mask
    | _ => v.zeroBranch q=0 ∧ v.decBranch q=0 ∧ v.complement q=0
  transition : ∀q,v.state q=(if q=M.start then 1 else 0)+v.B*incoming M v q
  counter : ∀j,Bits (v.counter j) ((2*v.b-1)*v.mask) ∧ v.counter j=v.final j*v.last+v.rem j ∧ v.rem j < v.last
  update : ∀j,v.counter (some j)+v.B*decrements M v j=d j+v.B*(v.rem (some j)+increments M v j)
  zero_test : ∀q,match M.instr q with | .test j _ _ => Bits (v.counter (some j)) ((v.B-1)*v.complement q) | _ => True
  clock : v.counter none+v.B*v.last=baseC Q d+v.B*(v.rem none+v.mask)
  scale_lower : v.b ≤ v.final none
  scale_upper : 2*v.final none < v.B
end

open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System

section
variable (h : System M d v)
include h
omit [DecidableEq Q] [DecidableEq J] h in
lemma Cpos : 0 < baseC Q d := by simp [baseC]
lemma Bpos : 0 < v.B := by have := h.bound; have := (System.Cpos (Q:=Q) (d:=d)); omega
lemma Bfour : 4 ≤ v.B := by have := h.base; have := h.Bpos; omega
lemma Bgt : 1 < v.B := by have := h.Bfour; omega
lemma bpos : 0 < v.b := by have := h.base; have := h.Bpos; omega
lemma width : 0 < v.w := by
  by_contra hh
  have hw : v.w=0 := by omega
  have := h.power
  rw [hw,pow_zero] at this
  have := h.Bfour
  omega
lemma states_bound : 2*Fintype.card Q < v.B := by
  have := h.bound
  dsimp [baseC] at this
  omega
lemma initial_bound (j : J) : d j < 2*v.b := by
  have hh : d j ≤ ∑i,d i := Finset.single_le_sum (fun i _=>Nat.zero_le _) (Finset.mem_univ j)
  have hb := h.bound
  have hbase := h.base
  dsimp [baseC] at hb
  omega
lemma clock_bound : baseC Q d < 2*v.b := by have := h.bound; have := h.base; omega
lemma last_eq : v.last=v.B^(v.k-1) := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have he := h.last
  rw [h.full,hk,pow_succ'] at he
  exact Nat.eq_of_mul_eq_mul_left h.Bpos he
lemma mask_eq : v.mask=ones v.B v.k := by
  have he := h.mask
  rw [h.full,←geometric h.Bgt v.k] at he
  exact Nat.eq_of_mul_eq_mul_left (by have := h.Bgt; omega) he
lemma state_info (q : Q) : v.state q < v.B^v.k ∧ ∀t < v.k,digit v.B (v.state q) t ≤ 1 := by
  have hh := h.state_bits q
  change Packed.Bits (v.state q) v.mask at hh
  rw [h.mask_eq,h.power] at hh
  rw [h.power]
  exact (bits_ones h.width).mp hh
lemma counter_info (j : Option J) : v.counter j < v.B^v.k ∧ ∀t < v.k,digit v.B (v.counter j) t < 2*v.b := by
  have hh := (h.counter j).1
  change Packed.Bits (v.counter j) ((2*v.b-1)*v.mask) at hh
  rw [h.mask_eq,h.power] at hh
  have hfcap : 2*v.b-1 < 2^v.w := by have := h.base; rw [←h.power]; have := h.bpos; omega
  have hc := (bits_mask h.width hfcap).mp hh
  rw [←h.power] at hc
  refine ⟨hc.1,?_⟩
  intro t ht
  have := bits_le (hc.2 t ht)
  have := h.bpos
  omega
lemma rem_eq (j : Option J) : v.rem j=pack v.B (v.k-1) (digit v.B (v.counter j)) := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have he := (h.counter j).2.1
  rw [h.last_eq] at he
  have hr := (h.counter j).2.2
  rw [h.last_eq] at hr
  exact (division_last h.Bpos (by rw [←hk]; exact (h.counter_info j).1) he hr).2
lemma final_eq (j : Option J) : v.final j=digit v.B (v.counter j) (v.k-1) := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have he := (h.counter j).2.1
  rw [h.last_eq] at he
  have hr := (h.counter j).2.2
  rw [h.last_eq] at hr
  exact (division_last h.Bpos (by rw [←hk]; exact (h.counter_info j).1) he hr).1
lemma state_partition (t : ℕ) (ht : t < v.k) : (∑q,digit v.B (v.state q) t)=1 := by
  have hc : ∀u < v.k,(∑q,digit v.B (v.state q) u) < v.B := by
    intro u hu
    have hh : (∑q,digit v.B (v.state q) u) ≤ Fintype.card Q := by
      calc _  ≤ ∑q : Q,1 := Finset.sum_le_sum (fun q _=>(h.state_info q).2 u hu)
           _ =_ := by simp
    have := h.states_bound
    omega
  have he := digit_sum h.Bpos v.state (fun q=>(h.state_info q).1) hc t
  rw [h.partition,h.mask_eq] at he
  change digit v.B (pack v.B v.k (fun _=>1)) t=_ at he
  rw [digit_pack h.Bpos (fun _ _=>h.Bgt),ite_eq_left ht] at he
  simpa only [ite_eq_left ht] using he.symm
end

section
variable (h : System M d v)
include h
omit [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J] h in
lemma arc_none (q : Q) (b : Bool) (he : dest M q b=none) : arc M v q b=0 := by
  cases hi : M.instr q <;> cases b <;> simp_all [dest,arc]
omit [Fintype J] [DecidableEq J] h in
lemma incoming_sum : (∑p,incoming M v p)=∑q,∑b : Bool,arc M v q b := by
  unfold incoming
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  cases he : dest M q b with
  | none => simp [System.arc_none (M:=M) (v:=v) q b he]
  | some p => simp
lemma outgoing (q : Q) : v.state q=(if q=M.halt then v.state q else 0)+∑b : Bool,arc M v q b := by
  cases hi : M.instr q with
  | halt => have hq := (M.halt_iff q).mp hi; simp [hq,arc,(M.halt_iff M.halt).mpr rfl]
  | inc j p =>
    have hq : q≠M.halt := by intro hh; have := (M.halt_iff q).mpr hh; rw [hi] at this; contradiction
    simp [hq,arc,hi]
  | test j p0 pd =>
    have hq : q≠M.halt := by intro hh; have := (M.halt_iff q).mpr hh; rw [hi] at this; contradiction
    have hb := h.branch q
    rw [hi] at hb
    simpa [hq,arc,hi,add_comm] using hb.2.2.1.symm
lemma outgoing_sum : v.mask=v.state M.halt+∑q,∑b : Bool,arc M v q b := by
  rw [←h.partition]
  calc
    _ = ∑q,((if q=M.halt then v.state q else 0)+∑b : Bool,arc M v q b) :=
      Finset.sum_congr rfl (fun q _=>h.outgoing q)
    _ = _ := by rw [Finset.sum_add_distrib]; simp
lemma transition_sum : v.mask=1+v.B*(∑q,∑b : Bool,arc M v q b) := by
  rw [←h.partition]
  calc
    _ = ∑q,((if q=M.start then 1 else 0)+v.B*incoming M v q) :=
      Finset.sum_congr rfl (fun q _=>h.transition q)
    _ = _ := by rw [Finset.sum_add_distrib,←Finset.mul_sum,(System.incoming_sum (M:=M) (v:=v))]; simp
lemma halt_mask : v.state M.halt=v.last := by
  have h₁:=h.outgoing_sum
  have h₂:=h.transition_sum
  have h₃:=h.mask
  have h₄:=h.last
  have h₅ : 0 < v.H := by rw [h.full]; exact pow_pos h.Bpos _
  have h₆ : (v.B-1)*v.mask+v.mask=v.B*v.mask := by
    have hh : v.B-1+1=v.B := Nat.sub_add_cancel h.Bgt.le
    nlinarith
  have h₇ := congrArg (fun n=>v.B*n) h₁
  have h₈ : v.H-1+1=v.H := Nat.sub_add_cancel h₅
  have he : v.B*v.state M.halt=v.B*v.last := by nlinarith only [h₂,h₃,h₄,h₆,h₇,h₈]
  exact Nat.eq_of_mul_eq_mul_left h.Bpos he
lemma arc_bits (q : Q) (b : Bool) : Packed.Bits (arc M v q b) v.mask := by
  cases hi : M.instr q with
  | halt => cases b <;> simp [arc,hi,bits_zero_left]
  | inc j p => cases b <;> simp [arc,hi,bits_zero_left]; exact h.state_bits q
  | test j p0 pd =>
    have hb:=h.branch q
    rw [hi] at hb
    cases b
    · simpa only [arc,hi] using bits_trans hb.1 (h.state_bits q)
    · simpa only [arc,hi] using bits_trans hb.2.1 (h.state_bits q)
lemma arc_info (q : Q) (b : Bool) : arc M v q b < v.B^v.k ∧ ∀t < v.k,digit v.B (arc M v q b) t ≤ 1 := by
  have hh:=h.arc_bits q b
  rw [h.mask_eq,h.power] at hh
  rw [h.power]
  exact (bits_ones h.width).mp hh
end

variable (h : System M d v)
include h
lemma arcs_sum_eq : (∑q,∑b : Bool,arc M v q b)=ones v.B (v.k-1) := by
  have he:=h.outgoing_sum
  rw [h.mask_eq,h.halt_mask,h.last_eq] at he
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have hp : ones v.B v.k=ones v.B (v.k-1)+v.B^(v.k-1) := by
    nth_rw 1 [hk]
    simp only [ones,pack_succ,one_mul]
  rw [hp] at he
  omega
lemma arc_digit_cap (t : ℕ) (ht : t < v.k) : (∑q,∑b : Bool,digit v.B (arc M v q b) t) < v.B := by
  have hc : (∑q,∑b : Bool,digit v.B (arc M v q b) t) ≤ 2*Fintype.card Q := by
    calc _ ≤ ∑q : Q,∑b : Bool,1 := Finset.sum_le_sum (fun q _=>Finset.sum_le_sum (fun b _=>(h.arc_info q b).2 t ht))
         _ = _ := by simp; omega
  exact hc.trans_lt h.states_bound
lemma arc_digit_sum (t : ℕ) (ht : t < v.k) :
    (∑q,∑b : Bool,digit v.B (arc M v q b) t)=if t < v.k-1 then 1 else 0 := by
  have hc : ∀u < v.k,(∑a : Q×Bool,digit v.B (arc M v a.1 a.2) u) < v.B := by
    intro u hu
    simpa only [Fintype.sum_prod_type] using h.arc_digit_cap u hu
  have he:=digit_sum h.Bpos (fun a : Q×Bool=>arc M v a.1 a.2) (fun a=>(h.arc_info a.1 a.2).1) hc t
  simp only [Fintype.sum_prod_type,ite_eq_left ht,h.arcs_sum_eq] at he
  rw [ones,digit_pack h.Bpos (fun _ _=>h.Bgt)] at he
  exact he.symm

def selected (P : Q → Bool → Prop) [DecidableRel P] : ℕ := ∑q,∑b : Bool,if P q b then arc M v q b else 0
lemma selected_digit (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) :
    digit v.B (selected (M:=M) (v:=v) P) t=∑q,∑b : Bool,if P q b then digit v.B (arc M v q b) t else 0 := by
  have hx (a : Q×Bool) : (if P a.1 a.2 then arc M v a.1 a.2 else 0) < v.B^v.k := by
    split_ifs
    · exact (h.arc_info a.1 a.2).1
    · exact pow_pos h.Bpos _
  have hc : ∀u < v.k,(∑a : Q×Bool,digit v.B (if P a.1 a.2 then arc M v a.1 a.2 else 0) u) < v.B := by
    intro u hu
    apply lt_of_le_of_lt _ (h.arc_digit_cap u hu)
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro q hq
    apply Finset.sum_le_sum
    intro b hb
    split_ifs <;> simp [digit_zero]
  have he:=digit_sum h.Bpos (fun a : Q×Bool=>if P a.1 a.2 then arc M v a.1 a.2 else 0) hx hc t
  simpa only [selected,Fintype.sum_prod_type,ite_eq_left ht,apply_ite (digit v.B) _,ite_apply,digit_zero] using he
lemma selected_bound (P : Q → Bool → Prop) [DecidableRel P] : selected (M:=M) (v:=v) P < v.B^v.k := by
  have hl : selected (M:=M) (v:=v) P ≤ ∑q,∑b : Bool,arc M v q b := by
    apply Finset.sum_le_sum
    intro q hq
    apply Finset.sum_le_sum
    intro b hb
    split_ifs <;> simp
  have hb : ones v.B (v.k-1) ≤ ones v.B v.k := by
    have hk : v.k=v.k-1+1 := by have := h.length; omega
    conv_rhs => rw [hk,ones,pack_succ]
    exact Nat.le_add_right _ _
  exact hl.trans_lt ((h.arcs_sum_eq ▸ hb).trans_lt (pack_lt h.Bpos (fun _ _=>h.Bgt)))
lemma selected_le_one (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) :
    digit v.B (selected (M:=M) (v:=v) P) t ≤ if t < v.k-1 then 1 else 0 := by
  rw [h.selected_digit P t ht,←h.arc_digit_sum t ht]
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro b hb
  split_ifs <;> simp
end System
end SingleFold.Counter

end OAI
