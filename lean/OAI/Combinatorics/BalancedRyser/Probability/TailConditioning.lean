import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.Combinatorics.BalancedRyser.Probability.SlotProbability
import OAI.Combinatorics.BalancedRyser.Probability.TailGraph

namespace OAI

namespace Balanced
namespace TailConditioning

universe u v
variable {I : Type u} (Q : I → Type v)

noncomputable def minSlotSize [Fintype I] [∀ i, Fintype (Q i)] : ℕ := by
  classical
  exact WithTop.untopD 0 (Finset.univ.image (fun i => Fintype.card (Q i))).min

def independentTransversals (G : SimpleGraph (Sigma Q)) : Set (Slots.Assignment Q) :=
  {ω | ∀ i j, ¬ G.Adj ⟨i, ω i⟩ ⟨j, ω j⟩}

noncomputable def conditionalCylinder [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)]
    (G : SimpleGraph (Sigma Q)) (J : Finset I) (a : Slots.Assignment Q) : ℝ :=
  (Slots.law Q).real (Slots.cylinder Q J a ∩ independentTransversals Q G) /
    (Slots.law Q).real (independentTransversals Q G)

end TailConditioning
end Balanced

end OAI
