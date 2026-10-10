import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.BinaryAddition

namespace OAI

namespace MatchingFPRAS.StackSubtract
open Turing MachineCost StackAddition

def borrow (c a b : Bool) : Bool := decide (a.toNat < b.toNat+c.toNat)
lemma digit_balance (c a b : Bool) :
    a.toNat+2*(borrow c a b).toNat=(digit c a b).toNat+b.toNat+c.toNat := by
  cases c <;> cases a <;> cases b <;> decide

def subDigits (c : Bool) (A B : List Bool) : Bool × List Bool :=
  match A,B with
  | [],[] => (c,[])
  | a::A,[] => let r:=subDigits (borrow c a false) A []; (r.1,digit c a false::r.2)
  | [],b::B => let r:=subDigits (borrow c false b) [] B; (r.1,digit c false b::r.2)
  | a::A,b::B => let r:=subDigits (borrow c a b) A B; (r.1,digit c a b::r.2)
termination_by A.length+B.length

lemma subDigits_length (A B : List Bool) (c : Bool) :
    (subDigits c A B).2.length=max A.length B.length := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => simp [subDigits]
    | cons b B ih => simp [subDigits,ih]
  | cons a A ih =>
    cases B with
    | nil => simp [subDigits,ih]
    | cons b B => simp [subDigits,ih,max_add_add_right]

lemma subDigits_balance (A B : List Bool) (c : Bool) :
    value A+2^(max A.length B.length)*(subDigits c A B).1.toNat=
      value (subDigits c A B).2+value B+c.toNat := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => simp [subDigits,value]
    | cons b B ih =>
      have hh:=ih (borrow c false b)
      have hd:=digit_balance c false b
      simp only [List.length_nil,Nat.zero_max,value] at hh
      simp only [subDigits,List.length_nil,List.length_cons,Nat.zero_max,value,pow_succ,
        Bool.toNat_false] at hd ⊢
      nlinarith
  | cons a A ih =>
    cases B with
    | nil =>
      have hh:=ih [] (borrow c a false)
      have hd:=digit_balance c a false
      simp only [List.length_nil,Nat.max_zero,value] at hh
      simp only [subDigits,List.length_nil,List.length_cons,Nat.max_zero,value,pow_succ,
        Bool.toNat_false] at hd ⊢
      nlinarith
    | cons b B =>
      have hh:=ih B (borrow c a b)
      have hd:=digit_balance c a b
      simp only [subDigits,List.length_cons,max_add_add_right,value,pow_succ]
      nlinarith

lemma value_lt (A : List Bool) : value A<2^A.length := by
  induction A with
  | nil => simp [value]
  | cons a A ih =>
    have ha : a.toNat≤1 := by cases a <;> decide
    simp only [value,List.length_cons,pow_succ]
    omega

lemma subDigits_correct (A B : List Bool) (c : Bool) (h : value B+c.toNat≤value A) :
    (subDigits c A B).1=false ∧ value (subDigits c A B).2=value A-value B-c.toNat := by
  have hh:=subDigits_balance A B c
  have hl:=value_lt (subDigits c A B).2
  rw [subDigits_length] at hl
  cases hc : (subDigits c A B).1 with
  | false => simp only [hc,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hh; exact ⟨rfl,by omega⟩
  | true => simp only [hc,Bool.toNat_true,Nat.mul_one] at hh; omega

def program (c : Bool) : TM2.Stmt (fun _ : Fin 3=>Bool) Bool Store :=
  .pop 0 (fun v a=>(a,v.2)) (.pop 1 (fun v b=>(v.1,b))
    (.branch (fun v=>v.1.isNone && v.2.isNone)
      (.load (fun _=>default) .halt)
      (.push 2 (fun v=>digit c (v.1.getD false) (v.2.getD false))
        (.goto (fun v=>borrow c (v.1.getD false) (v.2.getD false))))))
def cfg (c : Option Bool) (A B L : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Bool Store := ⟨c,v,stackData A B L⟩
lemma step_empty (c : Bool) (L : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some c) [] [] L v)=cfg none [] [] L default := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one]
lemma step_digits (c : Bool) (A B L : List Bool) (v : Store) (h : A ≠ [] ∨ B ≠ []) :
    advance (TM2.step program) (cfg (some c) A B L v)=
      cfg (some (borrow c (A.headD false) (B.headD false))) A.tail B.tail
        (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?) := by
  cases A <;> cases B <;> simp_all [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two]
lemma subDigits_step (c : Bool) (A B : List Bool) (h : A ≠ [] ∨ B ≠ []) :
    (subDigits c A B).2 = digit c (A.headD false) (B.headD false)::
      (subDigits (borrow c (A.headD false) (B.headD false)) A.tail B.tail).2 := by
  cases A <;> cases B <;> simp_all [subDigits]

theorem run_subtraction (A B L : List Bool) (c : Bool) (v : Store) :
    ∃ t≤A.length+B.length+1,MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
      cfg none [] [] ((subDigits c A B).2.reverse++L) default := by
  have aux : ∀ n (A B : List Bool),A.length+B.length=n → ∀ (c : Bool) (L : List Bool) (v : Store),
      ∃ t≤A.length+B.length+1,MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
        cfg none [] [] ((subDigits c A B).2.reverse++L) default := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B hn c L v
      by_cases he : A=[] ∧ B=[]
      · rcases he with ⟨rfl,rfl⟩
        refine ⟨1,by simp,?_⟩
        simpa only [MachineCost.run,subDigits,List.reverse_nil,List.nil_append] using step_empty c L v
      · have hne : A≠[] ∨ B≠[] := by tauto
        have hlt : A.tail.length+B.tail.length<n := by
          cases A <;> cases B <;> simp_all
          all_goals omega
        obtain ⟨t,ht,hr⟩:=ih _ hlt A.tail B.tail rfl
          (borrow c (A.headD false) (B.headD false))
          (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?)
        refine ⟨t+1,by omega,?_⟩
        rw [MachineCost.run,step_digits c A B L v hne,hr,subDigits_step c A B hne]
        simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
  exact aux _ A B rfl c L v
end MatchingFPRAS.StackSubtract

end OAI
