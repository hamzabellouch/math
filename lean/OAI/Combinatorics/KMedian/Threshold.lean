import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweringMoment
import OAI.Combinatorics.KMedian.Expanders.GraphRelabel
import OAI.Combinatorics.KMedian.Hardness.Analysis
import OAI.Combinatorics.KMedian.Hardness.ProjectionReduction
import OAI.Combinatorics.KMedian.Hardness.Threads
import OAI.Combinatorics.KMedian.Machines.AdviceInstances
import OAI.Combinatorics.KMedian.Machines.TablePromises
import OAI.Combinatorics.KMedian.PCP.UniformProjection
import OAI.Combinatorics.KMedian.Projection.Contraction
import OAI.Combinatorics.KMedian.Projection.IncidenceExpansion

namespace OAI

section Inline_PCPThreshold
namespace MetricKMedian

theorem below_threshold_impossible (h : Complexity.PNeNP) :
    ∀ α ∈ approximationFactors, 1+2/Real.exp 1≤α := by
  intro α hα
  by_contra hn
  obtain ⟨ε,hε,L,hL,hno⟩ := Coverage.remaining_projection_obstruction h hα (lt_of_not_ge hn)
  exact hno (Coverage.projection_gap_np_reductions ε hε L hL)

theorem threshold (h : Complexity.PNeNP) :
    sInf approximationFactors=1+2/Real.exp 1 := by
  apply le_antisymm infimum_le_threshold
  exact le_csInf approximationFactors_nonempty (below_threshold_impossible h)
end MetricKMedian

end Inline_PCPThreshold

end OAI
