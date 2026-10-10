import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

namespace Yau.Analysis
open Filter Set
open scoped Topology
noncomputable section
variable {X F : Type*} [NormedAddCommGroup F] [CompleteSpace F]

theorem uniform_limit_of_summable_increments (f : ℕ → X → F) (S : Set X)
    (b : ℕ → ℝ) (hb : Summable b)
    (hstep : ∀ n x, x ∈ S → dist (f n x) (f (n+1) x) ≤ b n) :
    ∃ g : X → F, TendstoUniformlyOn f g atTop S ∧
      ∀ n x, x ∈ S → dist (f n x) (g x) ≤ ∑' j, b (n+j) := by
  classical
  have hex (x : S) : ∃ y : F, Tendsto (fun n ↦ f n x.val) atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable b (fun n ↦ hstep n x.val x.property) hb)
  choose g hg using hex
  let G : X → F := fun x ↦ if hx : x ∈ S then g ⟨x,hx⟩ else 0
  have hpoint (x : X) (hx : x ∈ S) : Tendsto (fun n ↦ f n x) atTop (𝓝 (G x)) := by
    simpa only [G,dite_eq_left hx] using hg ⟨x,hx⟩
  have htail (n : ℕ) (x : X) (hx : x ∈ S) :
      dist (f n x) (G x) ≤ ∑' j, b (n+j) :=
    dist_le_tsum_of_dist_le_of_tendsto b (fun n ↦ hstep n x hx) hb (hpoint x hx) n
  refine ⟨G,?_,htail⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have ht : Tendsto (fun n ↦ ∑' j, b (n+j)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add b
  filter_upwards [ht.eventually (gt_mem_nhds heps)] with n hn x hx
  rw [dist_comm]
  exact (htail n x hx).trans_lt hn

end
end Yau.Analysis

end OAI
