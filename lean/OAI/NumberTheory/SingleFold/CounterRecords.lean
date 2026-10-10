import OAI.NumberTheory.SingleFold.CounterMachine

namespace OAI

namespace SingleFold.Packed
lemma digit_init {B a x : ℕ} (hB : 0 < B) (ha : a < B) :
    digit B (a+B*x) 0=a ∧ ∀t,digit B (a+B*x) (t+1)=digit B x t := by
  constructor
  · simp [digit,Nat.mod_eq_of_lt ha]
  · intro t
    rw [digit,pow_succ',←Nat.div_div_eq_div_mul,Nat.add_mul_div_left _ _ hB,
      Nat.div_eq_of_lt ha,zero_add]
    rfl
lemma digit_add {B k x y : ℕ} (hB : 0 < B) (hx : x < B^k) (hy : y < B^k)
    (hc : ∀t < k,digit B x t+digit B y t < B) (t : ℕ) (ht : t < k) :
    digit B (x+y) t=digit B x t+digit B y t := by
  have he : x+y=pack B k (fun t=>digit B x t+digit B y t) := by
    rw [pack_add,pack_digits hB hx,pack_digits hB hy]
  rw [he,digit_pack hB hc,ite_eq_left ht]
end SingleFold.Packed

namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System
variable (h : System M d v)
include h
lemma selected_pack (P : Q → Bool → Prop) [DecidableRel P] :
    selected (M:=M) (v:=v) P=pack v.B (v.k-1) (digit v.B (selected (M:=M) (v:=v) P)) := by
  have hp := pack_digits h.Bpos (h.selected_bound P)
  have hz : digit v.B (selected (M:=M) (v:=v) P) (v.k-1)=0 := by
    have hh:=h.selected_le_one P (v.k-1) (by have:=h.length; omega)
    simpa using hh
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  nth_rw 1 [hk] at hp
  rw [pack_last hz] at hp
  exact hp.symm
omit [Fintype J] [DecidableEq J] h in
lemma incoming_selected (p : Q) : incoming M v p=selected (M:=M) (v:=v) (fun q b=>dest M q b=some p) := rfl
attribute [local instance] Classical.propDecidable
omit [Fintype J] [DecidableEq Q] h in
lemma inc_selected (j : J) : increments M v j=selected (M:=M) (v:=v)
    (fun q b=>match M.instr q with | .inc i _ => i=j ∧ b=false | _=>False) := by
  unfold increments selected
  apply Finset.sum_congr rfl
  intro q hq
  cases hi : M.instr q <;> simp [hi,arc]
omit [Fintype J] [DecidableEq Q] h in
lemma dec_selected (j : J) : decrements M v j=selected (M:=M) (v:=v)
    (fun q b=>match M.instr q with | .test i _ _ => i=j ∧ b=true | _=>False) := by
  unfold decrements selected
  apply Finset.sum_congr rfl
  intro q hq
  cases hi : M.instr q <;> simp [hi,arc]
lemma counter_update (j : J) :
    digit v.B (v.counter (some j)) 0=d j ∧ ∀t < v.k-1,
    digit v.B (v.counter (some j)) (t+1)+digit v.B (decrements M v j) t=
      digit v.B (v.counter (some j)) t+digit v.B (increments M v j) t := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have ha : ∀t < v.k-1,digit v.B (increments M v j) t ≤ 1 := by
    intro t ht
    rw [(System.inc_selected (M:=M) (v:=v))]
    have hh:=h.selected_le_one (fun q b=>match M.instr q with | .inc i _=>i=j ∧ b=false | _=>False) t (by omega)
    simpa [ht] using hh
  have hf : ∀t < v.k-1,digit v.B (decrements M v j) t ≤ 1 := by
    intro t ht
    rw [(System.dec_selected (M:=M) (v:=v))]
    have hh:=h.selected_le_one (fun q b=>match M.instr q with | .test i _ _=>i=j ∧ b=true | _=>False) t (by omega)
    simpa [ht] using hh
  apply update_coefficients (B:=v.B) (T:=v.k-1) (m:=2*v.b) (by have:=h.base; omega) (h.initial_bound j) _ _ _
    (by intro t ht; exact (h.counter_info (some j)).2 t (by omega)) ha hf
  have he:=h.update j
  rw [h.rem_eq] at he
  have hac := h.selected_pack (fun q b=>match M.instr q with | .inc i _=>i=j ∧ b=false | _=>False)
  have hfc := h.selected_pack (fun q b=>match M.instr q with | .test i _ _=>i=j ∧ b=true | _=>False)
  rw [←(System.inc_selected (M:=M) (v:=v))] at hac
  rw [←(System.dec_selected (M:=M) (v:=v))] at hfc
  rw [←hk,pack_digits h.Bpos (h.counter_info (some j)).1,←hac,←hfc]
  exact he
lemma state_initial (q : Q) : digit v.B (v.state q) 0=if q=M.start then 1 else 0 := by
  rw [h.transition q]
  apply (digit_init h.Bpos _).1
  split_ifs <;> have := h.Bgt <;> omega
lemma state_step (q : Q) (t : ℕ) : digit v.B (v.state q) (t+1)=digit v.B (incoming M v q) t := by
  rw [h.transition q]
  apply (digit_init h.Bpos _).2
  split_ifs <;> have := h.Bgt <;> omega
lemma clock_update : digit v.B (v.counter none) 0=baseC Q d ∧ ∀t < v.k-1,
    digit v.B (v.counter none) (t+1)=digit v.B (v.counter none) t+1 := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have hmask : v.mask=v.last+ones v.B (v.k-1) := by
    rw [h.mask_eq,h.last_eq]
    nth_rw 1 [hk]
    rw [ones,pack_succ]
    simp only [one_mul]
    exact Nat.add_comm _ _
  have he : v.counter none=baseC Q d+v.B*(v.rem none+ones v.B (v.k-1)) := by
    have hh:=h.clock
    rw [hmask] at hh
    nlinarith only [hh]
  have hh := update_coefficients (B:=v.B) (T:=v.k-1) (m:=2*v.b) (d:=baseC Q d)
    (by have:=h.base; omega) h.clock_bound (digit v.B (v.counter none)) (fun _=>1) (fun _=>0)
    (by intro t ht; exact (h.counter_info none).2 t (by omega)) (by intros; omega) (by intros; omega)
  simp only [pack_const_zero,mul_zero,add_zero] at hh
  apply hh
  rw [←hk,pack_digits h.Bpos (h.counter_info none).1,←h.rem_eq]
  exact he
lemma clock_digits (t : ℕ) (ht : t < v.k) : digit v.B (v.counter none) t=baseC Q d+t := by
  induction t with
  | zero => simpa using h.clock_update.1
  | succ t ih => rw [h.clock_update.2 t (by omega),ih (by omega)]; omega
lemma clock_final : v.final none=baseC Q d+(v.k-1) := by
  rw [h.final_eq,h.clock_digits _ (by have:=h.length; omega)]
end System
end SingleFold.Counter

namespace SingleFold.Packed
lemma digit_power {B T t : ℕ} (hB : 1 < B) (ht : t < T+1) : digit B (B^T) t=if t=T then 1 else 0 := by
  have he : B^T=pack B (T+1) (fun u=>if u=T then 1 else 0) := by simp [pack]
  have hc : ∀u < T+1,(if u=T then 1 else 0) < B := by intro u hu; split_ifs <;> omega
  rw [he,digit_pack (by omega) hc,ite_eq_left ht]
end SingleFold.Packed
namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System

section
variable (h : System M d v)
include h
lemma arc_state_bits (q : Q) (b : Bool) : Packed.Bits (arc M v q b) (v.state q) := by
  cases hi : M.instr q with
  | halt => cases b <;> simp [arc,hi,bits_zero_left]
  | inc j p => cases b <;> simp [arc,hi,bits_zero_left,bits_refl]
  | test j p0 pd =>
    have hb:=h.branch q
    rw [hi] at hb
    cases b
    · simpa only [arc,hi,Bits,Packed.Bits] using hb.1
    · simpa only [arc,hi,Bits,Packed.Bits] using hb.2.1
lemma arc_digit_le (q : Q) (b : Bool) (t : ℕ) : digit v.B (arc M v q b) t ≤ digit v.B (v.state q) t := by
  have hh:=h.arc_state_bits q b
  rw [h.power] at *
  exact bits_le ((bits_blocks h.width _ _).mp hh t)
lemma selected_at_state (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0) :
    digit v.B (selected (M:=M) (v:=v) P) t=∑b : Bool,if P q b then digit v.B (arc M v q b) t else 0 := by
  rw [h.selected_digit P t ht]
  apply Finset.sum_eq_single q
  · intro p hp hpq
    apply Finset.sum_eq_zero
    intro b hb
    have hzero : digit v.B (arc M v p b) t=0 := by have hh:=h.arc_digit_le p b t; rw [hs p,ite_eq_right hpq] at hh; omega
    simp [hzero]
  · simp
lemma halt_digit (t : ℕ) (ht : t < v.k) : digit v.B (v.state M.halt) t=if t=v.k-1 then 1 else 0 := by
  rw [h.halt_mask,h.last_eq]
  apply digit_power h.Bgt
  have := h.length
  omega
lemma test_partition (q : Q) (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) (t : ℕ) (ht : t < v.k) :
    digit v.B (v.zeroBranch q) t+digit v.B (v.decBranch q) t=digit v.B (v.state q) t := by
  have hz:=h.arc_info q false
  have hn:=h.arc_info q true
  simp only [arc,hi] at hz hn
  have hb:=h.branch q
  rw [hi] at hb
  rw [←hb.2.2.1]
  symm
  apply digit_add h.Bpos hz.1 hn.1 _ t ht
  intro u hu
  have := hz.2 u hu
  have := hn.2 u hu
  have := h.Bfour
  omega
lemma complement_pack (q : Q) (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) :
    v.complement q=pack v.B v.k (fun t=>1-digit v.B (v.zeroBranch q) t) := by
  have hz:=h.arc_info q false
  simp only [arc,hi] at hz
  have hb:=h.branch q
  rw [hi] at hb
  have he : pack v.B v.k (digit v.B (v.zeroBranch q))+pack v.B v.k (fun t=>1-digit v.B (v.zeroBranch q) t)=ones v.B v.k := by
    rw [←pack_add]
    apply pack_congr
    intro t ht
    exact Nat.add_sub_of_le (hz.2 t ht)
  rw [pack_digits h.Bpos hz.1,←h.mask_eq] at he
  omega
lemma zero_branch_forces (q : Q) (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd)
    (t : ℕ) (ht : t < v.k) (hz : digit v.B (v.zeroBranch q) t=1) : digit v.B (v.counter (some j)) t=0 := by
  have hb:=h.zero_test q
  rw [hi] at hb
  change Packed.Bits _ _ at hb
  rw [h.complement_pack q j p0 pd hi,←pack_mul] at hb
  have hc : ∀u < v.k,(v.B-1)*(1-digit v.B (v.zeroBranch q) u) < v.B := by
    intro u hu
    have hh : 1-digit v.B (v.zeroBranch q) u ≤ 1 := Nat.sub_le _ _
    have := h.Bpos
    nlinarith only [hh,this,Nat.sub_le v.B 1,Nat.sub_lt this (by omega : 0 < 1)]
  have hb' : Packed.Bits (digit v.B (v.counter (some j)) t)
      (digit v.B (pack v.B v.k (fun u=>(v.B-1)*(1-digit v.B (v.zeroBranch q) u))) t) := by
    rw [h.power] at hb ⊢
    exact (bits_blocks h.width _ _).mp hb t
  rw [digit_pack h.Bpos hc,ite_eq_left ht,hz,Nat.sub_self,mul_zero] at hb'
  exact (bits_zero_right _).mp hb'
end

section
variable (h : System M d v)
include h
attribute [local instance] Classical.propDecidable
lemma select_inc (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p : Q) (hi : M.instr q=.inc j p) :
    digit v.B (selected (M:=M) (v:=v) P) t=if P q false then 1 else 0 := by
  rw [h.selected_at_state P t ht q hs]
  simp [arc,hi,hs q,digit_zero]
lemma select_test (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) :
    digit v.B (selected (M:=M) (v:=v) P) t=
      (if P q true then digit v.B (v.decBranch q) t else 0)+
      (if P q false then digit v.B (v.zeroBranch q) t else 0) := by
  rw [h.selected_at_state P t ht q hs]
  simp [arc,hi]
lemma inc_values (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p : Q) (hi : M.instr q=.inc j p) :
    (∀z,digit v.B (incoming M v z) t=if z=p then 1 else 0) ∧
    (∀i,digit v.B (increments M v i) t=if i=j then 1 else 0) ∧
    (∀i,digit v.B (decrements M v i) t=0) := by
  constructor
  · intro z
    rw [(System.incoming_selected (M:=M) (v:=v)),h.select_inc _ t ht q hs j p hi]
    simp [dest,hi,eq_comm]
  constructor
  · intro i
    rw [(System.inc_selected (M:=M) (v:=v)),h.select_inc _ t ht q hs j p hi]
    simp [hi,eq_comm]
  · intro i
    rw [(System.dec_selected (M:=M) (v:=v)),h.select_inc _ t ht q hs j p hi]
    simp [hi]
lemma test_values (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) :
    (∀z,digit v.B (incoming M v z) t=
      (if z=pd then digit v.B (v.decBranch q) t else 0)+
      (if z=p0 then digit v.B (v.zeroBranch q) t else 0)) ∧
    (∀i,digit v.B (increments M v i) t=0) ∧
    (∀i,digit v.B (decrements M v i) t=if i=j then digit v.B (v.decBranch q) t else 0) := by
  constructor
  · intro z
    rw [(System.incoming_selected (M:=M) (v:=v)),h.select_test _ t ht q hs j p0 pd hi]
    simp [dest,hi,eq_comm]
  constructor
  · intro i
    rw [(System.inc_selected (M:=M) (v:=v)),h.select_test _ t ht q hs j p0 pd hi]
    simp [hi]
  · intro i
    rw [(System.dec_selected (M:=M) (v:=v)),h.select_test _ t ht q hs j p0 pd hi]
    simp [hi,eq_comm]
lemma test_choice (t : ℕ) (ht : t < v.k-1) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) :
    digit v.B (v.zeroBranch q) t=(if digit v.B (v.counter (some j)) t=0 then 1 else 0) ∧
    digit v.B (v.decBranch q) t=(if digit v.B (v.counter (some j)) t=0 then 0 else 1) := by
  have ht' : t < v.k := by omega
  have hp:=h.test_partition q j p0 pd hi t ht'
  rw [hs q,ite_eq_left rfl] at hp
  have hv:=h.test_values t ht' q hs j p0 pd hi
  have hu:=(h.counter_update j).2 t ht
  rw [hv.2.1 j,hv.2.2 j,ite_eq_left rfl,add_zero] at hu
  by_cases hz : digit v.B (v.counter (some j)) t=0
  · simp only [ite_eq_left hz]
    omega
  · have hn : digit v.B (v.zeroBranch q) t≠1 := by
      intro hh
      exact hz (h.zero_branch_forces q j p0 pd hi t ht' hh)
    simp only [ite_eq_right hz]
    omega
lemma decode (t : ℕ) (ht : t < v.k) :
    (∀q,digit v.B (v.state q) t=if q=(run M d t).state then 1 else 0) ∧
    (∀j,digit v.B (v.counter (some j)) t=(run M d t).value j) := by
  induction t with
  | zero => exact ⟨h.state_initial,fun j=>(h.counter_update j).1⟩
  | succ t ih =>
    have ht' : t < v.k-1 := by omega
    have ht0 : t < v.k := by omega
    rcases ih ht0 with ⟨hs,hr⟩
    have hnh : (run M d t).state≠M.halt := by
      intro hh
      have hd:=h.halt_digit t ht0
      rw [hh] at hs
      rw [hs M.halt,ite_eq_left rfl,ite_eq_right (by omega)] at hd
      omega
    cases hi : M.instr (run M d t).state with
    | halt => exact False.elim (hnh ((M.halt_iff _).mp hi))
    | inc j p =>
      have hv:=h.inc_values t ht0 _ hs j p hi
      have hn : run M d (t+1)=⟨p,Function.update (run M d t).value j ((run M d t).value j+1)⟩ := by
        rw [run_succ,next,hi]
      rw [hn]
      constructor
      · intro q; exact (h.state_step q t).trans (hv.1 q)
      · intro i
        have hu:=(h.counter_update i).2 t ht'
        rw [hv.2.1 i,hv.2.2 i,hr i,add_zero] at hu
        by_cases hij : i=j
        · subst i; simpa using hu
        · simpa [hij,Function.update_of_ne hij] using hu
    | test j p0 pd =>
      have hv:=h.test_values t ht0 _ hs j p0 pd hi
      have hc:=h.test_choice t ht' _ hs j p0 pd hi
      rw [hr j] at hc
      by_cases hz : (run M d t).value j=0
      · simp only [ite_eq_left hz] at hc
        have hn : run M d (t+1)=⟨p0,(run M d t).value⟩ := by rw [run_succ]; simp [next,hi,hz]
        rw [hn]
        constructor
        · intro q
          rw [h.state_step,hv.1,hc.1,hc.2]
          simp
        · intro i
          have hu:=(h.counter_update i).2 t ht'
          rw [hv.2.1 i,hv.2.2 i,hc.2,hr i] at hu
          simpa using hu
      · simp only [ite_eq_right hz] at hc
        have hn : run M d (t+1)=⟨pd,Function.update (run M d t).value j ((run M d t).value j-1)⟩ := by
          rw [run_succ]; simp [next,hi,hz]
        rw [hn]
        constructor
        · intro q
          rw [h.state_step,hv.1,hc.1,hc.2]
          simp
        · intro i
          have hu:=(h.counter_update i).2 t ht'
          rw [hv.2.1 i,hv.2.2 i,hc.2,hr i,add_zero] at hu
          by_cases hij : i=j
          · subst i
            simp only [ite_true] at hu
            change _=(Function.update (run M d t).value j ((run M d t).value j-1)) j
            simp only [Function.update_self]
            omega
          · simpa [hij,Function.update_of_ne hij] using hu
lemma haltsAt : HaltsAt M d (v.k-1) := by
  constructor
  · have ht : v.k-1 < v.k := by have:=h.length; omega
    have hs:=(h.decode _ ht).1 M.halt
    rw [h.halt_digit _ ht,ite_eq_left rfl] at hs
    by_contra hh
    rw [ite_eq_right (Ne.symm hh)] at hs
    omega
  · intro t ht hh
    have ht' : t < v.k := by omega
    have hs:=(h.decode t ht').1 M.halt
    rw [h.halt_digit t ht',hh,ite_eq_left rfl,ite_eq_right (by omega)] at hs
    omega
end

variable (h : System M d v)
include h
lemma branch_digits (q : Q) (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd)
    (t : ℕ) (ht : t < v.k) :
    digit v.B (v.zeroBranch q) t=(if q=(run M d t).state ∧ (run M d t).value j=0 then 1 else 0) ∧
    digit v.B (v.decBranch q) t=(if q=(run M d t).state ∧ (run M d t).value j≠0 then 1 else 0) := by
  by_cases hq : q=(run M d t).state
  · have hnh : q≠M.halt := by intro hh; have := (M.halt_iff q).mpr hh; rw [hi] at this; contradiction
    have hlt : t < v.k-1 := by
      have hh:=h.haltsAt.1
      by_contra hn
      have he : t=v.k-1 := by omega
      rw [he,hh] at hq
      exact hnh hq
    have hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0 := by
      intro p; rw [(h.decode t ht).1 p,hq]
    have hh:=h.test_choice t hlt q hs j p0 pd hi
    rw [(h.decode t ht).2 j] at hh
    by_cases hz : (run M d t).value j=0 <;> simpa [hq,hz] using hh
  · have hz:=h.arc_digit_le q false t
    have hn:=h.arc_digit_le q true t
    simp only [arc,hi] at hz hn
    rw [(h.decode t ht).1 q,ite_eq_right hq] at hz hn
    simp only [hq,false_and,ite_false]
    omega
end System

lemma system_unique {v u : Witness Q J} (hv : System M d v) (hu : System M d u) : v=u := by
  have hk : v.k=u.k := by
    have hh:=haltsAt_unique hv.haltsAt hu.haltsAt
    have := hv.length
    have := hu.length
    omega
  have hf : v.final none=u.final none := by rw [hv.clock_final,hu.clock_final,hk]
  have hw : v.w=u.w := by
    have hp : 0 < v.final none := by rw [hv.clock_final]; have:=(System.Cpos (Q:=Q) (d:=d)); omega
    obtain ⟨w,hw,huniq⟩:=unique_scale hp
    apply (huniq v.w _).trans (huniq u.w _).symm
    · have h₁:=hv.scale_lower; have h₂:=hv.scale_upper; have h₃:=hv.base
      rw [←hv.power]; omega
    · have h₁:=hu.scale_lower; have h₂:=hu.scale_upper; have h₃:=hu.base
      rw [←hu.power]; rw [hf]; omega
  have hB : v.B=u.B := by rw [hv.power,hu.power,hw]
  have hb : v.b=u.b := by have := hv.base; have := hu.base; omega
  have hH : v.H=u.H := by rw [hv.full,hu.full,hB,hk]
  have hl : v.last=u.last := by rw [hv.last_eq,hu.last_eq,hB,hk]
  have hm : v.mask=u.mask := by rw [hv.mask_eq,hu.mask_eq,hB,hk]
  have hs : v.state=u.state := by
    funext q
    apply digits_ext hv.Bpos (hv.state_info q).1 (by rw [hB,hk]; exact (hu.state_info q).1)
    intro t ht
    rw [(hv.decode t ht).1 q,hB,(hu.decode t (by omega)).1 q]
  have hc : v.counter=u.counter := by
    funext j
    apply digits_ext hv.Bpos (hv.counter_info j).1 (by rw [hB,hk]; exact (hu.counter_info j).1)
    intro t ht
    cases j with
    | none => rw [hv.clock_digits t ht,hB,hu.clock_digits t (by omega)]
    | some j => rw [(hv.decode t ht).2 j,hB,(hu.decode t (by omega)).2 j]
  have hz : v.zeroBranch=u.zeroBranch ∧ v.decBranch=u.decBranch ∧ v.complement=u.complement := by
    suffices ∀q,v.zeroBranch q=u.zeroBranch q ∧ v.decBranch q=u.decBranch q ∧ v.complement q=u.complement q from
      ⟨funext (fun q=>(this q).1),funext (fun q=>(this q).2.1),funext (fun q=>(this q).2.2)⟩
    intro q
    have hbv:=hv.branch q
    have hbu:=hu.branch q
    cases hi : M.instr q with
    | halt => rw [hi] at hbv hbu; omega
    | inc j p => rw [hi] at hbv hbu; omega
    | test j p0 pd =>
      rw [hi] at hbv hbu
      have hve:=hv.arc_info q false
      have hue:=hu.arc_info q false
      have hvn:=hv.arc_info q true
      have hun:=hu.arc_info q true
      simp only [arc,hi] at hve hue hvn hun
      have hze : v.zeroBranch q=u.zeroBranch q := by
        apply digits_ext hv.Bpos hve.1 (by rw [hB,hk]; exact hue.1)
        intro t ht
        rw [(hv.branch_digits q j p0 pd hi t ht).1,hB,(hu.branch_digits q j p0 pd hi t (by omega)).1]
      have hne : v.decBranch q=u.decBranch q := by
        apply digits_ext hv.Bpos hvn.1 (by rw [hB,hk]; exact hun.1)
        intro t ht
        rw [(hv.branch_digits q j p0 pd hi t ht).2,hB,(hu.branch_digits q j p0 pd hi t (by omega)).2]
      exact ⟨hze,hne,by omega⟩
  have hfinal : v.final=u.final := by
    funext j
    rw [hv.final_eq,hu.final_eq,hB,hk,hc]
  have hrem : v.rem=u.rem := by
    funext j
    rw [hv.rem_eq,hu.rem_eq,hB,hk,hc]
  rcases hz with ⟨hz,hn,hcpl⟩
  cases v
  cases u
  simp_all only
end SingleFold.Counter

end OAI
