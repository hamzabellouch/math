import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialTimeSize
import OAI.Computability.MinUncut.Machines.MachineSubstitution

namespace OAI

/-! Polynomial-time composition uses concrete finite TM2
compiler. It lifts the heterogeneous machine programs and performs a two-pass
stack transfer with a proved linear intermediate-word cost. -/

namespace ContinuumCoulomb.TM2Composition
open Turing

/-- Actual polynomial-time composition, with the intermediate length bound
proved from the first machine's execution rather than postulated. -/
noncomputable def computable {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (hf : TM2ComputableInPolyTime ea eb f) (hg : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (g ∘ f) :=
  MinUncutGames.Foundations.Complexity.MachineSequential.composeBits (f := f) (g := g) hf hg

end ContinuumCoulomb.TM2Composition

end OAI
