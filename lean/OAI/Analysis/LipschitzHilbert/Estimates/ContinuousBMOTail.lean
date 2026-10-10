import OAI.Analysis.LipschitzHilbert.Trees.LineGridBMO_Tail
import OAI.Analysis.LipschitzHilbert.Trees.LineGridLimit
import OAI.Analysis.LipschitzHilbert.Estimates.TailLimit

namespace OAI

/-! John--Nirenberg's geometric distribution bound for a continuous
function on an actual finite interval. The proof passes the uniform finite
grid estimate to the function, using pointwise convergence of cell means. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LipschitzHilbert.FiniteLineGrid

def HasFullMeanOscillationBound (g : FiniteLineGrid) (f : ℝ → ℝ) (A : ℝ) : Prop :=
  ∀ n i, i < g.branching ^ n →
    (∫ x in g.cell n i, |f x - g.cellMean f n i|) ≤ A * g.meshWidth n

theorem continuous_mean_oscillation_tail (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasFullMeanOscillationBound f A) (k : ℕ) :
    g.lineMeasure.real {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
      |f x - integralAverage g.lineMeasure f|} ≤
        (1 / 2 : ℝ) ^ k * g.lineMeasure.real univ := by
  let F := fun N x => |(g.withDepth N).average (g.withDepth N).lineMeasure f N x -
    integralAverage g.lineMeasure f|
  have hlim : ∀ᵐ x ∂g.lineMeasure,
      Tendsto (fun N => F N x) atTop (𝓝 |f x - integralAverage g.lineMeasure f|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    have h := (g.average_tendsto_at_continuity hb f hf hx (hc x hx)).sub_const
      (integralAverage g.lineMeasure f)
    simpa only [F, Real.norm_eq_abs] using h.norm
  apply strict_tail_bound_of_ae_tendsto g.lineMeasure F _ hlim _ _ (by positivity)
  intro N
  have hBN : (g.withDepth N).HasMeanOscillationBound f A := by
    intro n i _ hi
    exact hBMO n i hi
  have htail := (g.withDepth N).mean_oscillation_average_tail f hf hA hBN le_rfl k
  have heq : {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A < F N x} =ᵐ[g.lineMeasure]
      {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
        |(g.withDepth N).average (g.withDepth N).lineMeasure f N x -
          (g.withDepth N).average (g.withDepth N).lineMeasure f 0 x|} := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    simp only [F, (g.withDepth N).average_zero_eq_integralAverage f hf hx]
    rfl
  have hm := congrArg ENNReal.toReal (measure_congr heq)
  exact hm.trans_le htail

end LipschitzHilbert.FiniteLineGrid

end

end OAI
