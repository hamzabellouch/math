import Mathlib
import OAI.Probability.LogConcave.JetEstimates.PolySmooth

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

namespace LogConcaveSampling.PolySmooth
variable {d : ℕ} {ι : Type*}

lemma multiset_prod (m : Multiset ι) (f : ι → Point d → ℝ)
    (hf : ∀i∈m,PolySmooth (f i)) :
    PolySmooth (fun x => (m.map (fun i => f i x)).prod) := by
  induction m using Multiset.induction_on with
  | empty => simpa using PolySmooth.const (d:=d) 1
  | @cons i m ih =>
    simp only [Multiset.map_cons,Multiset.prod_cons]
    exact (hf i (Multiset.mem_cons_self _ _)).mul
      (ih (fun j hj => hf j (Multiset.mem_cons_of_mem hj)))
end LogConcaveSampling.PolySmooth

end UpperProof
end
end
end

end OAI
