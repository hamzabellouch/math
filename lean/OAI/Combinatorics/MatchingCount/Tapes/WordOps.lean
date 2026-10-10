import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeTransfer

namespace OAI

namespace MatchingFPRAS.WordOps
open Turing MachineCost TreeTransfer

def duplicate : Unit → TM2.Stmt (fun _ : Fin 3=>Bool) Unit Store := fun _=>
  .pop 0 (fun _ b=>b) (.branch Option.isNone (.load (fun _=>none) .halt)
    (.push 1 (fun v=>v.getD false) (.push 2 (fun v=>v.getD false) (.goto (fun _=>())))))
lemma duplicate_nil (B D : List Bool) (v : Store) :
    advance (TM2.step duplicate) (cfg (some ()) [] B D v)=cfg none [] B D none := by
  simp [advance,TM2.step,duplicate,TM2.stepAux,cfg,update_zero]
lemma duplicate_cons (b : Bool) (A B D : List Bool) (v : Store) :
    advance (TM2.step duplicate) (cfg (some ()) (b::A) B D v)=
      cfg (some ()) A (b::B) (b::D) (some b) := by
  simp [advance,TM2.step,duplicate,TM2.stepAux,cfg,update_zero,update_one,update_two]
theorem run_duplicate (A B D : List Bool) (v : Store) :
    MachineCost.run (TM2.step duplicate) (A.length+1) (cfg (some ()) A B D v)=
      cfg none [] (A.reverse++B) (A.reverse++D) none := by
  induction A generalizing B D v with
  | nil => simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append,MachineCost.run] using duplicate_nil B D v
  | cons b A ih =>
    rw [List.length_cons,Nat.add_right_comm,MachineCost.run,duplicate_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
lemma duplicate_accesses (l : Unit) : StackCost.accesses (duplicate l)≤3 := by cases l; decide

def clear : Unit → TM2.Stmt (fun _ : Fin 3=>Bool) Unit Store := fun _=>
  .pop 0 (fun _ b=>b) (.branch Option.isNone (.load (fun _=>none) .halt) (.goto (fun _=>())))
lemma clear_nil (B D : List Bool) (v : Store) :
    advance (TM2.step clear) (cfg (some ()) [] B D v)=cfg none [] B D none := by
  simp [advance,TM2.step,clear,TM2.stepAux,cfg,update_zero]
lemma clear_cons (b : Bool) (A B D : List Bool) (v : Store) :
    advance (TM2.step clear) (cfg (some ()) (b::A) B D v)=cfg (some ()) A B D (some b) := by
  simp [advance,TM2.step,clear,TM2.stepAux,cfg,update_zero]
theorem run_clear (A B D : List Bool) (v : Store) :
    MachineCost.run (TM2.step clear) (A.length+1) (cfg (some ()) A B D v)=cfg none [] B D none := by
  induction A generalizing v with
  | nil => exact clear_nil B D v
  | cons b A ih => rw [List.length_cons,Nat.add_right_comm,MachineCost.run,clear_cons,ih]
lemma clear_accesses (l : Unit) : StackCost.accesses (clear l)≤1 := by cases l; decide
end MatchingFPRAS.WordOps

end OAI
