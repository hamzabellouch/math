import Mathlib
import OAI.Combinatorics.UniformKServer.StackSimulation

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler

def run {q m g : ℕ} (P : Processor q m g) (s : State q m g) (coins : List Bool) : State q m g :=
  coins.foldl (step P) s

def padded : List Bool → List Bool
  | []=>[]
  | b::bs=>b::false::padded bs

theorem run_append {q m g : ℕ} (P : Processor q m g) (s : State q m g) (xs ys : List Bool) :
    run P s (xs++ys)=run P (run P s xs) ys := List.foldl_append

theorem run_cons {q m g : ℕ} (P : Processor q m g) (s : State q m g) (b : Bool) (bs : List Bool) :
    run P s (b::bs)=run P (step P s b) bs := rfl

theorem matches_run {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (bs : List Bool) :
    Matches P (run P s bs) ((machine P).run z (padded bs)) := by
  induction bs generalizing s z with
  | nil=>exact h
  | cons b bs ih=>
    exact ih _ _ (matches_step P s z h b false)

theorem padded_length (bs : List Bool) : (padded bs).length=2*bs.length := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>simp [padded,ih];omega

theorem padded_false (n : ℕ) : padded (List.replicate n false)=List.replicate (2*n) false := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp [List.replicate_succ,padded,ih,Nat.mul_succ]

theorem matches_capped {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (t : ℕ) :
    Matches P (run P s (List.replicate t false))
      ((machine P).run z (List.replicate (2*t) false)) := by
  simpa only [padded_false] using matches_run P s z h (List.replicate t false)

theorem run_halted {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (hy : s.yielded=true) (bs : List Bool) : run P s bs=s := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>simpa [run_cons,step,hy] using ih

theorem capped_after {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    {t B : ℕ} (h : (run P s (List.replicate t false)).yielded=true) (htB : t≤B) :
    run P s (List.replicate B false)=run P s (List.replicate t false) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_add_of_le htB
  rw [List.replicate_add,run_append]
  exact run_halted P _ h _

end UniformKServer.StackCompiler

end

end OAI
