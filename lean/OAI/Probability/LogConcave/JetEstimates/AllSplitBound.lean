import Mathlib
import OAI.Probability.LogConcave.JetEstimates.Bound

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.TensorEnergy
open scoped Classical

universe u

def AllSplitBound {S : Type u} [Fintype S] {d : ℕ}
    (T : (S → Fin d) → ℝ) (M : ℝ) : Prop :=
  ∀(I O : Type u) [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (e : S ≃ I ⊕ O),
    Bound (fun (o : O → Fin d) (i : I → Fin d) => T (fun s => Sum.elim i o (e s))) (M^2)
end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
