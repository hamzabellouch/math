import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedSequential
import OAI.Analysis.MatrixSigning.Machines.Sequential

namespace OAI

section

namespace KS.W29.FixedSequential

theorem lift3_run_state {k : Nat} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : KS.W01.FixedStack.Config k M.states) (bits : List Bool) :
    ((KS.W01.FixedStack.lift3 M ports).run c bits).state =
      (M.run (KS.W01.FixedStack.project ports c) bits).state :=
  congrArg (fun d : KS.W29.Config M.states => d.state)
    (KS.W01.FixedStack.lift3_project_run M ports c bits)

theorem activeFor_lift3_iff {k : Nat} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : KS.W01.FixedStack.Config k M.states) (bits : List Bool) :
    ActiveFor (ofMachine (KS.W01.FixedStack.lift3 M ports)) c bits ↔
      KS.W29.Sequential.ActiveFor M (KS.W01.FixedStack.project ports c) bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      simp only [ActiveFor, KS.W29.Sequential.ActiveFor]
      have ht := ih ((KS.W01.FixedStack.lift3 M ports).step c b)
      erw [KS.W01.FixedStack.lift3_project_step] at ht
      exact and_congr Iff.rfl ht

theorem haltsAfter_lift3_iff {k : Nat} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : KS.W01.FixedStack.Config k M.states) (bits : List Bool) :
    HaltsAfter (ofMachine (KS.W01.FixedStack.lift3 M ports)) c bits ↔
      KS.W29.Sequential.HaltsAfter M (KS.W01.FixedStack.project ports c) bits := by
  unfold HaltsAfter KS.W29.Sequential.HaltsAfter
  apply and_congr (activeFor_lift3_iff M ports c bits)
  change ((KS.W01.FixedStack.lift3 M ports).run c bits).state = none ↔ _
  rw [lift3_run_state]
  rfl

theorem haltsFromWithin_lift3_iff {k : Nat} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : KS.W01.FixedStack.Config k M.states) (fuel : Nat) :
    HaltsFromWithin (ofMachine (KS.W01.FixedStack.lift3 M ports)) c fuel ↔
      KS.W29.Sequential.HaltsFromWithin M (KS.W01.FixedStack.project ports c) fuel := by
  unfold HaltsFromWithin KS.W29.Sequential.HaltsFromWithin
  change (∀ bits : List Bool, bits.length = fuel →
    ((KS.W01.FixedStack.lift3 M ports).run c bits).state = none) ↔ _
  simp only [lift3_run_state]
  rfl

end KS.W29.FixedSequential

end

end OAI
