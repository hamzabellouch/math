import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.RootedInjectionEquiv
import OAI.Combinatorics.TriangleRemoval.Process.OlderSeed
import OAI.Combinatorics.TriangleRemoval.Tracking.RootedExposedCollisionWitness
import OAI.Combinatorics.TriangleRemoval.Process.SuffixBoundary
import OAI.Combinatorics.TriangleRemoval.Embeddings.SuffixTemplate
import OAI.Combinatorics.TriangleRemoval.Process.InitialAssignmentSet
import OAI.Combinatorics.TriangleRemoval.Process.InitialAssignmentSetBound
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEmbeddingsEdgeCover
import OAI.Combinatorics.TriangleRemoval.Process.InitialAssignmentSetMatching
import OAI.Combinatorics.TriangleRemoval.Process.LongWitnessMatchingCount
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth2
import OAI.Combinatorics.TriangleRemoval.Process.FreshMemSelected
import OAI.Combinatorics.TriangleRemoval.Queries.KeyCandidate
import OAI.Combinatorics.TriangleRemoval.Probability.TriangleSafeTemplateFreedman
import OAI.Combinatorics.TriangleRemoval.Process.MatchingSeedFullEdge
import OAI.Combinatorics.TriangleRemoval.Process.RootClosers
import OAI.Combinatorics.TriangleRemoval.Process.SeedEdgeSubsetPath
import OAI.Combinatorics.TriangleRemoval.Queries.VertexCall
import OAI.Combinatorics.TriangleRemoval.Process.FilteredSigmaWeightBound
import OAI.Combinatorics.TriangleRemoval.Stability.RelativeTemplateResidual
import OAI.Combinatorics.TriangleRemoval.Probability.MainProbabilityPrefixFailure
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixFailureEnvelopeSuperpolynomial
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixCodegreeErrorExit
import OAI.Combinatorics.TriangleRemoval.Tracking.NormalizedTrackingAbsolute

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open Filter Classical

namespace SharpTerminalLeave

theorem sharp_terminal_leave_l2 :
    Tendsto (fun n => expectation n (fun G =>
      (normalizedLeave n G-sharpConstant)^2)) atTop (𝓝 0) := by
  obtain ⟨c,hc,C,hprefix⟩ := uniform_prefix_obligation
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le
      (pmfMean_nonneg (terminalLaw n) (fun G _ => sq_nonneg (normalizedLeave n G-sharpConstant))))
  · intro b hb
    have hb2 : 0 < b/2 := by linarith
    filter_upwards [hprefix,main_l2_prefix_failure_bound c C hc (b/2) hb2,
      (tendsto_order.mp prefix_failure_l2_envelope_tendsto).2 (b/2) hb2] with n hpre hmain htail
    have hh := mul_le_mul_of_nonneg_left hpre (by positivity : 0 ≤ 2*(n : ℝ)+1)
    linarith only [hmain,hh,htail]

theorem sharp_terminal_leave_probability (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => probability n (fun G =>
      ε < |normalizedLeave n G-sharpConstant|)) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    apply pmfMean_nonneg (terminalLaw n)
    intro G _
    split_ifs <;> norm_num
  · intro n
    exact pmfMean_markov_sq (terminalLaw n) (fun G => normalizedLeave n G-sharpConstant) ε hε
  · simpa only [zero_div,expectation,pmfMean] using sharp_terminal_leave_l2.div_const (ε^2)

theorem sharp_terminal_leave_expectation :
    Tendsto (fun n => expectation n (fun G => (G.card : ℝ))/normalization n)
      atTop (𝓝 sharpConstant) := by
  have hmean : Tendsto (fun n => expectation n (normalizedLeave n)) atTop (𝓝 sharpConstant) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp sharp_terminal_leave_l2).2 (ε^2) (sq_pos_of_pos hε)] with n hn
    have hh := pmfMean_sq_le (terminalLaw n) (fun G => normalizedLeave n G-sharpConstant)
    rw [pmfMean_sub,pmfMean_const] at hh
    rw [Real.dist_eq]
    apply (sq_lt_sq₀ (abs_nonneg _) hε.le).mp
    rw [sq_abs]
    exact hh.trans_lt hn
  simpa only [expectation_normalizedLeave] using hmean

theorem sharp_terminal_leave :
    Tendsto (fun n => expectation n (fun G =>
      (normalizedLeave n G - sharpConstant) ^ 2)) atTop (𝓝 0) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => probability n (fun G =>
        ε < |normalizedLeave n G - sharpConstant|)) atTop (𝓝 0)) ∧
    Tendsto (fun n => expectation n (fun G => (G.card : ℝ)) / normalization n)
      atTop (𝓝 sharpConstant) :=
  ⟨sharp_terminal_leave_l2,sharp_terminal_leave_probability,sharp_terminal_leave_expectation⟩

end SharpTerminalLeave
end
end

end OAI
