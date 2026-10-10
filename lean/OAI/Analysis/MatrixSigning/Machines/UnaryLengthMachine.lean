import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.FixedPositiveSerializer

namespace OAI

namespace KS.W28.UnaryLength
open KS.W29

def dispatch (_ : Fin 1) (heads : Fin 27) (_coin : Bool) : Instruction 1 :=
  if heads.val % 3 = 0 then ⟨none, .stay, .stay, .stay⟩
  else ⟨some 0, .pop, .push true, .stay⟩
def machine : BinaryMachine := FiniteDispatch.compile 0 dispatch

def cfg (state : Option (Fin 1)) (xs ys zs : List Bool) : Config 1 := ⟨state, ![xs,ys,zs]⟩

private theorem head_zero (state : Option (Fin 1)) (xs ys zs : List Bool) :
    headCode (cfg state xs ys zs) % 3 = topCode xs := by
  have hx := topCode_lt_three xs
  have hy := topCode_lt_three ys
  have hz := topCode_lt_three zs
  change (topCode xs + 3 * topCode ys + 9 * topCode zs) % 3 = topCode xs
  omega

theorem step_cons (a coin : Bool) (xs ys zs : List Bool) :
    machine.step (cfg (some 0) (a::xs) ys zs) coin = cfg (some 0) xs (true::ys) zs := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  have hh := head_zero (some 0) (a::xs) ys zs
  change headCode (Config.mk (some (0 : Fin 1)) ![a::xs,ys,zs]) % 3 = topCode (a::xs) at hh
  simp only [dispatch]
  erw [hh]
  cases a <;> change Config.mk (some (0 : Fin 1)) _ = Config.mk (some (0 : Fin 1)) _
  all_goals
    apply congrArg (Config.mk (some (0 : Fin 1)))
    funext j
    fin_cases j <;> rfl

theorem step_empty (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 0) [] ys zs) coin = cfg none [] ys zs := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  have hh := head_zero (some 0) [] ys zs
  change headCode (Config.mk (some (0 : Fin 1)) ![[],ys,zs]) % 3 = topCode [] at hh
  simp only [dispatch]
  erw [hh]
  change Config.mk none _ = Config.mk none _
  apply congrArg (Config.mk none)
  funext j
  fin_cases j <;> rfl

theorem run_length (xs ys zs bits : List Bool) (hlen : bits.length = xs.length+1) :
    machine.run (cfg (some 0) xs ys zs) bits =
      cfg none [] (List.replicate xs.length true ++ ys) zs := by
  induction xs generalizing ys bits with
  | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin bits =>
          erw [BinaryMachine.run.eq_2, step_empty, BinaryMachine.run_halted _ _ rfl]
          rfl
  | cons a xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin bits =>
          have ht : bits.length = xs.length+1 := by simpa using Nat.succ.inj hlen
          erw [BinaryMachine.run.eq_2, step_cons, ih _ bits ht]
          simp only [List.length_cons, List.replicate_succ', List.append_assoc, List.singleton_append]
          rfl

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers registers_other)

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k := ofMachine (lift3 machine ports)

theorem length_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys zs : List Bool) :
    RunSpec (program ports) (registers ports spare xs ys zs)
      (registers ports spare [] (List.replicate xs.length true ++ ys) zs) (xs.length+1) := by
  intro bits hbits
  change (lift3 machine ports).run ⟨some (0 : Fin 1), registers ports spare xs ys zs⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports
        (⟨some 0, registers ports spare xs ys zs⟩ : KS.W01.FixedStack.Config k 1) = cfg (some 0) xs ys zs := by
      change KS.W29.Config.mk (some (0 : Fin 1)) _ = KS.W29.Config.mk (some (0 : Fin 1)) _
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 1)))
      funext j
      fin_cases j <;> simp [registers, ports.injective.eq_iff]
    erw [hp, run_length xs ys zs bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    fin_cases j <;> simp
  · intro j hj
    change registers ports spare [] (List.replicate xs.length true ++ ys) zs j =
      registers ports spare xs ys zs j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

end KS.W28.UnaryLength

end OAI
