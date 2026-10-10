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

namespace LogConcaveSampling.JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ : Type*}

lemma jet_map_positions (v : ι → E) (e : κ → ι) (l : List κ) (f : E → ℝ) :
    jet v (l.map e) f=jet (v ∘ e) l f := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons,jet,ih,Function.comp_apply]

lemma jet_finRange (v : ι → E) (l : List ι) (f : E → ℝ) :
    jet v l f=jet (fun k : Fin l.length => v (l.get k)) (List.finRange l.length) f := by
  change jet v l f=jet (v ∘ l.get) (List.finRange l.length) f
  rw [← jet_map_positions]
  congr 1
  exact (List.map_get_finRange l).symm
end LogConcaveSampling.JetCalculus

end UpperProof
end
end
end

end OAI
