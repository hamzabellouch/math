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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

lemma jet_congr_on_list (v w : ι → E) (l : List ι) (f : E → ℝ)
    (h : ∀i∈l,v i=w i) : jet v l f=jet w l f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change dir (v i) (jet v l f) = dir (w i) (jet w l f)
    rw [h i (by simp)]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
end LogConcaveSampling.JetCalculus

end UpperProof
end
end
end

end OAI
