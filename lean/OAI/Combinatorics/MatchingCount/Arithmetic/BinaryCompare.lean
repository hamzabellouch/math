import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.BinaryAddition

namespace OAI

namespace MatchingFPRAS.StackCompare
open Turing MachineCost StackAddition

def updateOrder (c : Ordering) (a b : Bool) : Ordering :=
  if a=b then c else if a then .gt else .lt

def compareDigits (c : Ordering) (A B : List Bool) : Ordering :=
  match A,B with
  | [],[] => c
  | a::A,[] => compareDigits (updateOrder c a false) A []
  | [],b::B => compareDigits (updateOrder c false b) [] B
  | a::A,b::B => compareDigits (updateOrder c a b) A B
termination_by A.length+B.length

def result (c : Ordering) (m n : ℕ) : Ordering := if m=n then c else compare m n
lemma result_digits (c : Ordering) (a b : Bool) (m n : ℕ) :
    result (updateOrder c a b) m n=result c (a.toNat+2*m) (b.toNat+2*n) := by
  rcases lt_trichotomy m n with h|h|h
  · have hb : a.toNat+2*m < b.toNat+2*n := by
      cases a <;> cases b <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega
    simp [result,ne_of_lt h,ne_of_lt hb,compare_lt_iff_lt.mpr h,compare_lt_iff_lt.mpr hb]
  · subst n
    cases a <;> cases b <;> cases c <;>
      simp [result,updateOrder,eq_comm]
    all_goals first
    | exact (compare_lt_iff_lt.mpr (by omega)).symm
    | exact (compare_gt_iff_gt.mpr (by omega)).symm
  · have hb : b.toNat+2*n < a.toNat+2*m := by
      cases a <;> cases b <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega
    simp [result,ne_of_gt h,ne_of_gt hb,compare_gt_iff_gt.mpr h,compare_gt_iff_gt.mpr hb]
lemma compareDigits_result (A B : List Bool) (c : Ordering) :
    compareDigits c A B=result c (value A) (value B) := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => simp [compareDigits,result,value]
    | cons b B ih =>
      rw [compareDigits,ih]
      simpa only [value,Bool.toNat_false,Nat.zero_add,Nat.mul_zero] using result_digits c false b 0 (value B)
  | cons a A ih =>
    cases B with
    | nil =>
      rw [compareDigits,ih]
      simpa only [value,Bool.toNat_false,Nat.zero_add,Nat.mul_zero,Nat.add_zero] using result_digits c a false (value A) 0
    | cons b B =>
      rw [compareDigits,ih]
      exact result_digits c a b (value A) (value B)
lemma compares_values (A B : List Bool) :
    compareDigits .eq A B=compare (value A) (value B) := by
  rw [compareDigits_result]
  unfold result
  split_ifs with h
  · simp [h]
  · rfl
def flags (c : Ordering) : List Bool := [decide (c=.lt),decide (c=.gt)]
def program (c : Ordering) : TM2.Stmt (fun _ : Fin 3=>Bool) Ordering Store :=
  .pop 0 (fun v a=>(a,v.2)) (.pop 1 (fun v b=>(v.1,b))
    (.branch (fun v=>v.1.isNone && v.2.isNone)
      (.push 2 (fun _=>decide (c=.gt)) (.push 2 (fun _=>decide (c=.lt))
         (.load (fun _=>default) .halt)))
      (.goto (fun v=>updateOrder c (v.1.getD false) (v.2.getD false)))))
def cfg (c : Option Ordering) (A B L : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Ordering Store := ⟨c,v,stackData A B L⟩
lemma step_empty (c : Ordering) (L : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some c) [] [] L v)=
      cfg none [] [] (flags c++L) default := by
  cases c <;> simp [advance,TM2.step,program,TM2.stepAux,cfg,flags,
    update_zero,update_one,update_two]
lemma step_digits (c : Ordering) (A B L : List Bool) (v : Store)
    (h : A≠[] ∨ B≠[]) :
    advance (TM2.step program) (cfg (some c) A B L v)=
      cfg (some (updateOrder c (A.headD false) (B.headD false))) A.tail B.tail L (A.head?,B.head?) := by
  cases A <;> cases B <;> simp_all [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two,List.headD]
lemma compareDigits_step (c : Ordering) (A B : List Bool) (h : A ≠ [] ∨ B ≠ []) :
    compareDigits c A B=
      compareDigits (updateOrder c (A.headD false) (B.headD false)) A.tail B.tail := by
  cases A <;> cases B <;> simp_all [compareDigits,List.headD]
theorem run_comparison (A B L : List Bool) (c : Ordering) (v : Store) :
    ∃ t ≤ A.length+B.length+1,
      MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
        cfg none [] [] (flags (compareDigits c A B)++L) default := by
  have aux : ∀ n (A B : List Bool), A.length+B.length=n →
      ∀ (c : Ordering) (L : List Bool) (v : Store),
      ∃ t ≤ A.length+B.length+1,
        MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
          cfg none [] [] (flags (compareDigits c A B)++L) default := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B hn c L v
      by_cases he : A=[] ∧ B=[]
      · rcases he with ⟨rfl,rfl⟩
        refine ⟨1,by simp,?_⟩
        simpa only [MachineCost.run,compareDigits] using step_empty c L v
      · have hne : A≠[] ∨ B≠[] := by tauto
        have hlt : A.tail.length+B.tail.length<n := by
          cases A <;> cases B <;> simp_all
          all_goals omega
        obtain ⟨t,ht,hr⟩:=ih _ hlt A.tail B.tail rfl
          (updateOrder c (A.headD false) (B.headD false)) L (A.head?,B.head?)
        refine ⟨t+1,by omega,?_⟩
        rw [MachineCost.run,step_digits c A B L v hne,hr,compareDigits_step c A B hne]
  exact aux _ A B rfl c L v
lemma accesses_bound (c : Ordering) : StackCost.accesses (program c) ≤ 4 := by
  cases c <;> decide
lemma finite_support : TM2.Supports program Finset.univ := by
  simp [TM2.Supports,program,TM2.SupportsStmt]
lemma numerical_comparison (m n : ℕ) : compareDigits .eq m.bits n.bits=compare m n := by
  simp only [compares_values,value_bits]
end MatchingFPRAS.StackCompare

end OAI
