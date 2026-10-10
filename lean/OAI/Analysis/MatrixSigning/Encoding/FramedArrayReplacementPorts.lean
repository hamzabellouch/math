import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.FramedArrayReplacement

namespace OAI

namespace KS.W11.FramedArrayRewrite
open KS.W01.FixedStack
open KS.W29.FixedSequential

def liftedProgram {k : ℕ} (ports : Fin 5 ↪ Fin k) : Program k :=
  KS.W29.FixedSequential.liftPorts program ports

theorem liftedProgram_states {k : ℕ} (ports : Fin 5 ↪ Fin k) :
    (liftedProgram ports).states = 8 := rfl

theorem run_replace_ports {k : ℕ} (ports : Fin 5 ↪ Fin k)
    (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length)
    (new tail bits : List Bool) (c : Config k program.states)
    (hc : projectPorts ports c =
      config (some program.initial) (xs.flatMap KS.W01.frame ++ tail)
        (KS.W01.frame new) [] [] (List.replicate i true))
    (hlen : 2 * (xs.flatMap KS.W01.frame ++ tail).length +
      2 * (KS.W01.frame new).length + i + 3 ≤ bits.length) :
    let result := (liftedProgram ports).toMachine.run c bits
    result.state = none ∧
      result.«stacks» (ports 0) = (xs.set i new).flatMap KS.W01.frame ++ tail ∧
      (∀ r, r ≠ 0 → result.«stacks» (ports r) = []) ∧
      ∀ j, (∀ r, j ≠ ports r) → result.«stacks» j = c.«stacks» j := by
  have hp := KS.W01.FixedStack.liftPorts_project_run program.toMachine ports c bits
  erw [hc, run_replace xs i hi new tail bits hlen] at hp
  refine ⟨congrArg (fun d : Config 5 program.states => d.state) hp,
    congrArg (fun d : Config 5 program.states => d.«stacks» 0) hp, ?_, ?_⟩
  · intro r hr
    have he := congrArg (fun d : Config 5 program.states => d.«stacks» r) hp
    fin_cases r
    · exact (hr rfl).elim
    · exact he
    · exact he
    · exact he
    · exact he
  · intro j hj
    exact KS.W01.FixedStack.liftPorts_run_preserves_other program.toMachine ports c bits j hj

theorem replacement_ports_linear_time {k : ℕ} (ports : Fin 5 ↪ Fin k)
    (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length)
    (new tail : List Bool) (c : Config k program.states)
    (hc : projectPorts ports c =
      config (some program.initial) (xs.flatMap KS.W01.frame ++ tail)
        (KS.W01.frame new) [] [] (List.replicate i true)) :
    HaltsFromWithin (liftedProgram ports) c
      (2 * (xs.flatMap KS.W01.frame ++ tail).length +
        2 * (KS.W01.frame new).length + i + 3) := by
  intro bits hlen
  exact (run_replace_ports ports xs i hi new tail bits c hc hlen.ge).1

end KS.W11.FramedArrayRewrite

end OAI
