import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProgram
import OAI.Combinatorics.MatchingCount.Tapes.Codec

namespace OAI

namespace MatchingFPRAS.PhysicalPost.Program
open Turing PhysicalStream

lemma run_tape (P : Program) (input : List Symbol) (n : ℕ) (b : Bits n) :
    (MatchingFPRAS.run P.machine input b).tape=
      (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).tape := by
  let : Inhabited {q //q∈P.states}:=⟨⟨P.entry,P.entry_mem⟩⟩
  rw [machine,restrictedMachine_run]
  exact (congrArg Cfg.tape (execute_lift P.table P.states P.supported n
    ⟨some default,Tape.mk₁ input⟩ (extend b))).symm
lemma run_halted (P : Program) (input : List Symbol) (n : ℕ) (b : Bits n)
    (h : (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).state=none) :
    (MatchingFPRAS.run P.machine input b).state=none := by
  let : Inhabited {q //q∈P.states}:=⟨⟨P.entry,P.entry_mem⟩⟩
  have he:=congrArg Cfg.state (execute_lift P.table P.states P.supported n
    ⟨some default,Tape.mk₁ input⟩ (extend b))
  have hs : (execute (restrict P.table P.states P.supported) n
      ⟨some default,Tape.mk₁ input⟩ (extend b)).state=none := by
    exact Option.map_eq_none_iff.mp (he.symm.trans h)
  rw [machine,restrictedMachine_run]
  change ((execute (restrict P.table P.states P.supported) n
    ⟨some default,Tape.mk₁ input⟩ (extend b)).state.map enumeration)=none
  rw [hs,Option.map_none]
lemma Realizes.run_all {P : Program} {input : List Symbol} {f : Experiment (Tape Symbol)} {N : ℕ}
    (hP : P.Realizes (Tape.mk₁ input) f N) (R : Tape Symbol→Prop) (hf : f.All R)
    (n : ℕ) (hn : N≤n) (b : Bits n) :
    (MatchingFPRAS.run P.machine input b).state=none ∧
      R (MatchingFPRAS.run P.machine input b).tape := by
  obtain ⟨p,hp,hm,hc⟩:=hP
  have hex:=hp.padded_execution (fun _=>rfl) n (hc.trans hn) (extend b)
  have ht : (MatchingFPRAS.run P.machine input b).tape=(p.run (extend b)).1 := by
    rw [run_tape,hex];rfl
  refine ⟨run_halted P input n b (by rw [hex];rfl),?_⟩
  rw [ht]
  exact p.all_run R (Experiment.all_of_mean_eq hm R hf) (extend b)
lemma Realizes.run_mean {P : Program} {input : List Symbol} {f : Experiment (Tape Symbol)} {N : ℕ}
    (hP : P.Realizes (Tape.mk₁ input) f N) (w : Tape Symbol→ℚ)
    (n : ℕ) (hn : N≤n) :
    average (fun b : Bits n=>w (MatchingFPRAS.run P.machine input b).tape)=f.mean w := by
  obtain ⟨p,hp,hm,hc⟩:=hP
  simp_rw [run_tape]
  exact (hp.fair_law (fun _=>rfl) n (hc.trans hn) (fun c=>w c.tape)).trans (hm w)
end MatchingFPRAS.PhysicalPost.Program

end OAI
