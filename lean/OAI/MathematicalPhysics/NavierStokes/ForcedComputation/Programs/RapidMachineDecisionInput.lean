import OAI.MathematicalPhysics.RapidForcing.Model
import OAI.MathematicalPhysics.AlternatingFlow.Model
import OAI.Analysis.PeriodicLattice.Basic

namespace OAI

/-! Turing's Section 8 designated-symbol undecidability, specialized to the
three finite presentations used by the rapid-forcing constructions. These
are purely machine-theoretic conditional inputs. -/

namespace ForcedComputation

/-- Finite transition tables with a distinguished terminal state. -/
def RapidMachineHaltingUndecidable : Prop :=
  ¬ ∃ d : ℕ → Bool, Computable d ∧
    ∀ (M : RapidForcing.Machine) (w : M.Input),
      d (M.inputDescription w) = true ↔ M.Halts w

/-- Flattened finite tables with a finite list of terminal states. -/
def AlternatingMachineHaltingUndecidable : Prop :=
  ¬ ∃ d : AlternatingNS.Machine × List ℕ → Bool, Computable d ∧
    ∀ (M : AlternatingNS.Machine) (w : List ℕ), M.WellFormed → M.ValidInput w → (d (M,w) = true ↔ M.Halts w)

/-- Ragged finite tables, stopping at the first absent instruction. -/
def LatticeMachineHaltingUndecidable : Prop :=
  ¬ ∃ d : PeriodicLattice.Input → Bool, Computable d ∧
    ∀ I : PeriodicLattice.Input, I.WellFormed → (d I = true ↔ PeriodicLattice.Halts I)

end ForcedComputation

end OAI
