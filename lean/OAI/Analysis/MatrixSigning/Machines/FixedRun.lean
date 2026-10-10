import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedStackMachine

namespace OAI

namespace KS.W19.FixedRun
open KS.W01.FixedStack

def pack {k q : Nat} (ports : Fin 3 ↪ Fin k) (c : KS.W29.Config q)
    (rest : Fin k → List Bool) : Config k q :=
  ⟨c.state, fun j => if j = ports 0 then c.«stacks» 0 else if j = ports 1 then c.«stacks» 1
    else if j = ports 2 then c.«stacks» 2 else rest j⟩

@[simp] theorem pack_on_port {k q : Nat} (ports : Fin 3 ↪ Fin k) (c : KS.W29.Config q)
    (rest : Fin k → List Bool) (j : Fin 3) :
    (pack ports c rest).«stacks» (ports j) = c.«stacks» j := by
  fin_cases j <;> simp [pack, ports.injective.eq_iff]

@[simp] theorem project_pack {k q : Nat} (ports : Fin 3 ↪ Fin k) (c : KS.W29.Config q)
    (rest : Fin k → List Bool) : project ports (pack ports c rest) = c := by
  cases c with
  | mk state «stacks» =>
    change KS.W29.Config.mk state _ = KS.W29.Config.mk state «stacks»
    congr 1
    funext j
    exact pack_on_port ports _ rest j

theorem config_ext {k q : Nat} {c d : Config k q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

theorem run_pack {k : Nat} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : KS.W29.Config M.states) (rest : Fin k → List Bool) (bits : List Bool) :
    (lift3 M ports).run (pack ports c rest) bits = pack ports (M.run c bits) rest := by
  have hp := lift3_project_run M ports (pack ports c rest) bits
  rw [project_pack] at hp
  apply config_ext
  · exact congrArg KS.W29.Config.state hp
  · intro j
    by_cases h0 : j = ports 0
    · subst j
      rw [pack_on_port]
      exact congrArg (fun d : KS.W29.Config M.states => d.«stacks» 0) hp
    by_cases h1 : j = ports 1
    · subst j
      rw [pack_on_port]
      exact congrArg (fun d : KS.W29.Config M.states => d.«stacks» 1) hp
    by_cases h2 : j = ports 2
    · subst j
      rw [pack_on_port]
      exact congrArg (fun d : KS.W29.Config M.states => d.«stacks» 2) hp
    have hj : ∀ r : Fin 3, j ≠ ports r := by
      intro r
      fin_cases r <;> assumption
    have hrun := lift3_run_preserves_other M ports (pack ports c rest) bits j hj
    have hc : (pack ports c rest).«stacks» j = rest j :=
      (ite_eq_right h0).trans ((ite_eq_right h1).trans (ite_eq_right h2))
    have hout : (pack ports (M.run c bits) rest).«stacks» j = rest j :=
      (ite_eq_right h0).trans ((ite_eq_right h1).trans (ite_eq_right h2))
    exact hrun.trans (hc.trans hout.symm)

end KS.W19.FixedRun

end OAI
