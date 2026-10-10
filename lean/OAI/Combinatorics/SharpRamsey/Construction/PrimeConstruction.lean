import Mathlib
import OAI.Combinatorics.SharpRamsey.Construction.GraphWitness
import OAI.Combinatorics.SharpRamsey.Construction.SourceSizes
import OAI.Combinatorics.SharpRamsey.Bounds.Lower

namespace OAI

section
namespace SharpLogRamsey.LowerTransfer
open Real Filter
open scoped Topology
noncomputable section

theorem actual_prime_construction (i : ℕ) : PrimeConstruction (i+3) := by
  intro η hη hηu
  have hσ:=Marking.eventually_graph_witness i η hη (by linarith : η ≤ 1)
  have ht : Tendsto (fun q : ℕ=>log (q:ℝ)) atTop atTop:=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually hσ,InitialExperiment.eventually_source_sizes i η hη.le]
    with q hgraph hsize
  intro hq
  have : Fact q.Prime:=⟨hq⟩
  have hq0 : (0:ℝ) < q:=by exact_mod_cast hq.pos
  exact hgraph q hsize.1 (exp_log hq0) _ _ hsize.2.2.1 hsize.2.2.2.1
    hsize.2.2.2.2.1 hsize.2.2.2.2.2.1 hsize.2.2.2.2.2.2

theorem prime_construction (d : ℕ) (hd : 5 ≤ d) : PrimeConstruction d := by
  have he : d-3+3=d:=by omega
  simpa only [he] using actual_prime_construction (d-3)
end
end SharpLogRamsey.LowerTransfer

end

end OAI
