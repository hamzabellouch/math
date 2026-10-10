import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.StackCompilerCost

namespace OAI

namespace MatchingFPRAS.TreeData
inductive Data where
  | nil
  | cons (head tail : Data)
  deriving DecidableEq, Inhabited
open Data

def encode : Data → List Bool
  | .nil => [false]
  | .cons a b => true::(encode a++encode b)
lemma encode_nonempty (v : Data) : encode v≠[] := by cases v <;> simp [encode]
lemma encode_length_pos (v : Data) : 0<(encode v).length := List.length_pos_iff.mpr (encode_nonempty v)
def size : Data → ℕ
  | .nil => 1
  | .cons a b => 1+size a+size b
lemma encode_length (v : Data) : (encode v).length=size v := by
  induction v with
  | nil => rfl
  | cons head tail head_ih tail_ih =>
    simp only [encode, List.length_cons, List.length_append, head_ih, tail_ih, size]
    omega
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreeTransfer
open Turing MachineCost TreeData

abbrev Store := Option Bool
abbrev Stacks := Fin 3 → List Bool
def program : Unit → TM2.Stmt (fun _ : Fin 3=>Bool) Unit Store := fun _=>
  .peek 2 (fun _ b=>b) (.branch Option.isNone (.load (fun _=>none) .halt)
    (.pop 2 (fun v _=>v) (.pop 0 (fun _ b=>b)
      (.push 1 (fun v=>v.getD false) (.branch (fun v=>v.getD false)
        (.push 2 (fun _=>false) (.push 2 (fun _=>false) (.goto (fun _=>()))))
        (.goto (fun _=>())))))))
def stackData (A B D : List Bool) : Stacks := ![A,B,D]
def cfg (l : Option Unit) (A B D : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Unit Store := ⟨l,v,stackData A B D⟩
@[simp] lemma stacks_zero (A B D : List Bool) : stackData A B D 0=A := rfl
@[simp] lemma stacks_one (A B D : List Bool) : stackData A B D 1=B := rfl
@[simp] lemma stacks_two (A B D : List Bool) : stackData A B D 2=D := rfl
lemma update_zero (A B D X : List Bool) : Function.update (stackData A B D) 0 X=stackData X B D := by
  funext i; fin_cases i <;> simp [stackData]
lemma update_one (A B D X : List Bool) : Function.update (stackData A B D) 1 X=stackData A X D := by
  funext i; fin_cases i <;> simp [stackData]
lemma update_two (A B D X : List Bool) : Function.update (stackData A B D) 2 X=stackData A B X := by
  funext i; fin_cases i <;> simp [stackData]
lemma step_nil (A B D : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some ()) (false::A) B (false::D) v)=
      cfg (some ()) A (false::B) D (some false) := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one,update_two]
lemma step_cons (A B D : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some ()) (true::A) B (false::D) v)=
      cfg (some ()) A (true::B) (false::false::D) (some true) := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one,update_two]
lemma step_stop (A B : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some ()) A B [] v)=cfg none A B [] none := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg]

theorem run_tree (x : Data) (A B D : List Bool) (v : Store) :
    MachineCost.run (TM2.step program) (encode x).length
      (cfg (some ()) (encode x++A) B (false::D) v)=
      cfg (some ()) A ((encode x).reverse++B) D (some false) := by
  induction x generalizing A B D v with
  | nil => simpa [encode,MachineCost.run] using step_nil A B D v
  | cons x y ihx ihy =>
    simp only [encode,List.length_cons,List.length_append,List.cons_append]
    rw [MachineCost.run,step_cons]
    rw [show (encode x++encode y)++A=encode x++(encode y++A) by simp only [List.append_assoc]]
    rw [run_add,ihx,ihy]
    simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.singleton_append]

theorem run_transfer (x : Data) (A B : List Bool) (v : Store) :
    MachineCost.run (TM2.step program) ((encode x).length+1)
      (cfg (some ()) (encode x++A) B [false] v)=
      cfg none A ((encode x).reverse++B) [] none := by
  rw [run_add,run_tree]
  exact step_stop A ((encode x).reverse++B) (some false)
lemma accesses_bound (l : Unit) : StackCost.accesses (program l)≤6 := by cases l; decide
end MatchingFPRAS.TreeTransfer

end OAI
