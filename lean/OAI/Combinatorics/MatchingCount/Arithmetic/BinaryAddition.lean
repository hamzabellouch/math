import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.StackCompilerCost

namespace OAI

namespace MatchingFPRAS.StackAddition
open Turing MachineCost

abbrev Stacks := Fin 3 → List Bool
abbrev Store := Option Bool × Option Bool
def value : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs
def digit (c a b : Bool) : Bool := xor (xor c a) b
def carry (c a b : Bool) : Bool := (c && a) || (c && b) || (a && b)
lemma digit_identity (c a b : Bool) :
    (digit c a b).toNat+2*(carry c a b).toNat=c.toNat+a.toNat+b.toNat := by
  cases c <;> cases a <;> cases b <;> rfl

def addDigits (c : Bool) (A B : List Bool) : List Bool :=
  match A,B with
  | [],[] => if c then [true] else []
  | a::A,[] => digit c a false::addDigits (carry c a false) A []
  | [],b::B => digit c false b::addDigits (carry c false b) [] B
  | a::A,b::B => digit c a b::addDigits (carry c a b) A B
termination_by A.length+B.length

lemma addDigits_value (A B : List Bool) (c : Bool) :
    value (addDigits c A B)=value A+value B+c.toNat := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => cases c <;> simp [addDigits,value]
    | cons b B ih =>
      rw [addDigits]
      simp only [value]
      rw [ih]
      have h:=digit_identity c false b
      simp only [Bool.toNat_false,Nat.add_zero] at h
      simp only [value]
      omega
  | cons a A ih =>
    cases B with
    | nil =>
      rw [addDigits]
      simp only [value]
      rw [ih]
      have h:=digit_identity c a false
      simp only [Bool.toNat_false,Nat.add_zero] at h
      simp only [value]
      omega
    | cons b B =>
      rw [addDigits]
      simp only [value]
      rw [ih]
      have h:=digit_identity c a b
      omega
lemma addDigits_length (A B : List Bool) (c : Bool) :
    (addDigits c A B).length ≤ max A.length B.length+1 := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => cases c <;> simp [addDigits]
    | cons b B ih =>
      rw [addDigits,List.length_cons]
      have h:=ih (carry c false b)
      simp only [List.length_nil,Nat.zero_max,List.length_cons] at h ⊢
      omega
  | cons a A ih =>
    cases B with
    | nil =>
      rw [addDigits,List.length_cons]
      have h:=ih [] (carry c a false)
      simp only [List.length_nil,Nat.max_zero,List.length_cons] at h ⊢
      omega
    | cons b B =>
      rw [addDigits,List.length_cons]
      have h:=ih B (carry c a b)
      simp only [List.length_cons]
      omega

def program (c : Bool) : TM2.Stmt (fun _ : Fin 3=>Bool) Bool Store :=
  .pop 0 (fun v a=>(a,v.2)) (.pop 1 (fun v b=>(v.1,b))
    (.branch (fun v=>v.1.isNone && v.2.isNone)
      (.branch (fun _=>c) (.push 2 (fun _=>true) (.load (fun _=>default) .halt))
        (.load (fun _=>default) .halt))
      (.push 2 (fun v=>digit c (v.1.getD false) (v.2.getD false))
        (.goto (fun v=>carry c (v.1.getD false) (v.2.getD false))))))
def stackData (A B L : List Bool) : Stacks := ![A,B,L]
@[simp] lemma stackData_zero (A B L : List Bool) : stackData A B L 0=A := rfl
@[simp] lemma stackData_one (A B L : List Bool) : stackData A B L 1=B := rfl
@[simp] lemma stackData_two (A B L : List Bool) : stackData A B L 2=L := rfl
def cfg (c : Option Bool) (A B L : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Bool Store := ⟨c,v,stackData A B L⟩
lemma update_zero (A B L X : List Bool) :
    Function.update (stackData A B L) 0 X=stackData X B L := by
  funext i
  fin_cases i <;> simp [stackData]
lemma update_one (A B L X : List Bool) :
    Function.update (stackData A B L) 1 X=stackData A X L := by
  funext i
  fin_cases i <;> simp [stackData]
lemma update_two (A B L X : List Bool) :
    Function.update (stackData A B L) 2 X=stackData A B X := by
  funext i
  fin_cases i <;> simp [stackData]
lemma step_empty (c : Bool) (L : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some c) [] [] L v)=
      cfg none [] [] ((addDigits c [] []).reverse++L) default := by
  cases c <;> simp [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two,addDigits]
lemma step_digits (c : Bool) (A B L : List Bool) (v : Store)
    (h : A≠[] ∨ B≠[]) :
    advance (TM2.step program) (cfg (some c) A B L v)=
      cfg (some (carry c (A.headD false) (B.headD false))) A.tail B.tail
        (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?) := by
  cases A <;> cases B <;> simp_all [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two]
lemma addDigits_step (c : Bool) (A B : List Bool) (h : A ≠ [] ∨ B ≠ []) :
    addDigits c A B=digit c (A.headD false) (B.headD false)::
      addDigits (carry c (A.headD false) (B.headD false)) A.tail B.tail := by
  cases A <;> cases B <;> simp_all [addDigits]

theorem run_addition (A B L : List Bool) (c : Bool) (v : Store) :
    ∃ t ≤ A.length+B.length+1,
      MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
        cfg none [] [] ((addDigits c A B).reverse++L) default := by
  have aux : ∀ n (A B : List Bool), A.length+B.length=n →
      ∀ (c : Bool) (L : List Bool) (v : Store),
      ∃ t ≤ A.length+B.length+1,
        MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
          cfg none [] [] ((addDigits c A B).reverse++L) default := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B hn c L v
      by_cases he : A=[] ∧ B=[]
      · rcases he with ⟨rfl,rfl⟩
        exact ⟨1,by simp,step_empty c L v⟩
      · have hne : A≠[] ∨ B≠[] := by tauto
        have hlt : A.tail.length+B.tail.length<n := by
          cases A <;> cases B <;> simp_all
          all_goals omega
        obtain ⟨t,ht,hr⟩:=ih _ hlt A.tail B.tail rfl
          (carry c (A.headD false) (B.headD false))
          (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?)
        refine ⟨t+1,by omega,?_⟩
        rw [MachineCost.run,step_digits c A B L v hne,hr,addDigits_step c A B hne]
        simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
  exact aux _ A B rfl c L v
lemma accesses_bound (c : Bool) : StackCost.accesses (program c) ≤ 3 := by
  cases c <;> decide
lemma finite_support : TM2.Supports program Finset.univ := by
  simp [TM2.Supports,program,TM2.SupportsStmt]
lemma value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [value,ih]
    cases b <;> simp [Nat.bit,Bool.toNat]
    omega

lemma addition_numerals (m n : ℕ) : value (addDigits false m.bits n.bits)=m+n := by
  simp only [addDigits_value,value_bits,Bool.toNat_false,Nat.add_zero]
end MatchingFPRAS.StackAddition

end OAI
