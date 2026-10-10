import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Machines.Deterministic

namespace OAI

section

namespace KS.W03.MachineRoundTrip
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem runSpec_ofMachine (M : Machine) (before after : Fin M.stackCount → List Bool) (ticks : ℕ)
    (h : ∀ bits : List Bool, bits.length = ticks →
      M.run ⟨some M.initial,before⟩ bits = ⟨none,after⟩) :
    RunSpec (ofMachine M) before after ticks := by
  cases M
  exact h

theorem deterministic_run (M : Machine) (h : KS.W29.Deterministic.CoinIndependent (ofMachine M))
    (c : Config M.stackCount M.states) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    M.run c xs = M.run c ys := by
  cases M
  exact KS.W29.Deterministic.run_eq_of_length_eq _ h c xs ys hlen

end KS.W03.MachineRoundTrip

end

end OAI
