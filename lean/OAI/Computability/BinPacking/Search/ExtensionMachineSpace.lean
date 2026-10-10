import OAI.Computability.BinPacking.Computation.MachineCanonicalOutput

namespace OAI

namespace BinPackingGap.ExtensionMachineSpace

open Turing BinPackingGames.Foundations.Complexity

def lengthSum {K : Type} {Γ : K → Type} (chosen : List K)
    (tapes : ∀ k, List (Γ k)) : Nat :=
  (chosen.map fun k => (tapes k).length).sum

theorem execution_stackLength (tm : FinTM2) (k : tm.K)
    {start finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step start (some finish) budget) :
    (finish.stk k).length ≤ (start.stk k).length + budget * Runtime.programPushBound tm :=
  Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) run

theorem execution_lengthSum (tm : FinTM2) (chosen : List tm.K)
    {start finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step start (some finish) budget) :
    lengthSum chosen finish.stk ≤
      lengthSum chosen start.stk + chosen.length * (budget * Runtime.programPushBound tm) := by
  induction chosen with
  | nil => simp [lengthSum]
  | cons k chosen ih =>
      have stepBound := execution_stackLength tm k run
      simp only [lengthSum, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, Nat.one_mul] at ih ⊢
      omega

theorem execution_uniformStackLength (tm : FinTM2)
    {start finish : tm.Cfg} {budget initialBound : Nat}
    (initial : ∀ k, (start.stk k).length ≤ initialBound)
    (run : StateTransition.EvalsToInTime tm.step start (some finish) budget) :
    ∀ k, (finish.stk k).length ≤ initialBound + budget * Runtime.programPushBound tm := by
  intro k
  exact (execution_stackLength tm k run).trans (Nat.add_le_add_right (initial k) _)

theorem lengthSum_le_uniform {K : Type} {Γ : K → Type} (chosen : List K)
    (tapes : ∀ k, List (Γ k)) (bound : Nat) (bounded : ∀ k, (tapes k).length ≤ bound) :
    lengthSum chosen tapes ≤ chosen.length * bound := by
  induction chosen with
  | nil => simp [lengthSum]
  | cons k chosen ih =>
      have head := bounded k
      simp only [lengthSum, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, Nat.one_mul] at ih ⊢
      omega

theorem lengthSum_eq_cleanup {K : Type} (chosen : List K) (tapes : K → List Bool) :
    lengthSum chosen tapes = MachineDrainMany.lengthSum chosen tapes := rfl

end BinPackingGap.ExtensionMachineSpace

end OAI
