import OAI.Analysis.CircleDomains.Topology.FiniteCompactTests
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Function.LpSpace.Complete

namespace OAI

/-! Summable changes produce genuine continuous and L2 limits, with the
same explicit tail estimates used to preserve saved barriers. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem continuous_limit_of_summable_steps
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : ℕ → C(X,ℝ)) (d : ℕ → ℝ) (hd : Summable d) (hd0 : ∀ n, 0 ≤ d n)
    (hstep : ∀ n x, |f n x-f (n+1) x| ≤ d n) :
    ∃ g : C(X,ℝ), Tendsto f atTop (𝓝 g) ∧
      ∀ n x, |f n x-g x| ≤ ∑' j, d (n+j) := by
  have hdist : ∀ n, dist (f n) (f (n+1)) ≤ d n := fun n =>
    (ContinuousMap.dist_le (hd0 n)).mpr (fun x => by
      simpa only [Real.dist_eq] using hstep n x)
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable d hdist hd)
  refine ⟨g,hg,fun n x => ?_⟩
  have ht := dist_le_tsum_of_dist_le_of_tendsto d hdist hd hg n
  have hp := (ContinuousMap.dist_apply_le_dist x : dist (f n x) (g x) ≤ dist (f n) g)
  simpa only [Real.dist_eq] using hp.trans ht

 theorem lp_limit_of_summable_steps
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (f : ℕ → X → E) (hf : ∀ n, MemLp (f n) 2 μ)
    (d : ℕ → ℝ) (hd : Summable d)
    (hstep : ∀ n, (eLpNorm (fun x => f n x-f (n+1) x) 2 μ).toReal ≤ d n) :
    ∃ g : Lp E 2 μ, Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 g) ∧
      ∀ n, dist ((hf n).toLp (f n)) g ≤ ∑' j, d (n+j) := by
  have hdist : ∀ n, dist ((hf n).toLp (f n)) ((hf (n+1)).toLp (f (n+1))) ≤ d n := by
    intro n
    rw [Lp.dist_edist, Lp.edist_toLp_toLp]
    change (eLpNorm (fun x => f n x-f (n+1) x) 2 μ).toReal ≤ d n
    exact hstep n
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable d hdist hd)
  exact ⟨g,hg,dist_le_tsum_of_dist_le_of_tendsto d hdist hd hg⟩

end CircleDomainRigidity

end

end OAI
