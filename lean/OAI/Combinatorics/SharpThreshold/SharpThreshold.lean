import OAI.Combinatorics.SharpThreshold.GraphQuantile
import OAI.Combinatorics.SharpThreshold.Probability
import OAI.Combinatorics.SharpThreshold.Russo
import OAI.Combinatorics.SharpThreshold.ThresholdODE
import OAI.Combinatorics.SharpThreshold.ThresholdConstants

namespace OAI

noncomputable section
namespace Problem313

/-- The entire threshold-width deduction, with the variance estimate as its only
additional quantitative hypothesis. -/
theorem graphQuantile_width_of_variance_bound {n : ℕ} {f : GraphConfig n → Bool}
    {C ε : ℝ} (hC : 0 ≤ C)
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f)
    (hε : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ))
    (hvariance : ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      graphVariance p f ≤ C * totalInfluence p f) :
    graphQuantile (1 - ε) f - graphQuantile ε f ≤
      (4 * C) * Real.log (1 / (2 * ε)) := by
  have hεone : ε < 1 := by linarith
  have hother0 : 0 < 1 - ε := by linarith
  have hother1 : 1 - ε < 1 := by linarith
  have ha := graphQuantile_mem_Ioo hmono hnt hε hεone
  have hb := graphQuantile_mem_Ioo hmono hnt hother0 hother1
  have hab : graphQuantile ε f ≤ graphQuantile (1 - ε) f := by
    exact (graphQuantile_strictMonoOn hmono hnt
      ⟨hε.le, hεone.le⟩ ⟨hother0.le, hother1.le⟩ (by linarith)).le
  have hrange : ∀ p ∈ Set.Icc (graphQuantile ε f) (graphQuantile (1 - ε) f),
      p ∈ Set.Ioo (0 : ℝ) 1 := by
    intro p hp
    exact ⟨ha.1.trans_le hp.1, hp.2.trans_lt hb.2⟩
  have hlog : graphQuantile (1 - ε) f - graphQuantile ε f ≤
      2 * C * Real.log ((1 - ε) / ε) := by
    apply logistic_width_of_hasDerivAt
      (μ := fun p => graphMean p f) (μ' := fun p => totalInfluence p f)
      hab hε hεone (continuous_graphMean f).continuousOn
    · intro p hp
      exact graphMean_mem_Ioo (hrange p hp).1 (hrange p hp).2 hnt
    · intro p hp
      exact hasDerivAt_graphMean hmono p
    · intro p hp
      have hv := hvariance p (hrange p (Set.Ioo_subset_Icc_self hp))
      simpa only [graphVariance_eq_mean_mul] using hv
    · exact graphMean_graphQuantile hmono hnt hε.le hεone.le
    · exact graphMean_graphQuantile hmono hnt hother0.le hother1.le
  exact threshold_log_conversion C ε
    (graphQuantile (1 - ε) f - graphQuantile ε f) hC hε hεhalf hlog

/-- The logarithmic-square threshold-width bound follows from the variance bound. -/
theorem sharp_threshold_width_of_variance_bound
    (hvariance : ∀ (n : ℕ) (f : GraphConfig n → Bool) (p : ℝ),
      2 ≤ n → VertexInvariant f → 0 < p → p < 1 →
      graphVariance p f ≤ ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) *
        totalInfluence p f) :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (ε : ℝ),
      2 ≤ n → VertexInvariant f → IncreasingGraphProperty f →
      NontrivialGraphProperty f → 0 < ε → ε < (1 / 2 : ℝ) →
      graphQuantile (1 - ε) f - graphQuantile ε f ≤
        ((2 : ℝ) ^ 19 / (Real.log (n : ℝ)) ^ 2) *
          Real.log (1 / (2 * ε)) := by
  intro n f ε hn hinvariant hmono hnt hε hεhalf
  have h := graphQuantile_width_of_variance_bound
    (C := (2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2)
    (by positivity) hmono hnt hε hεhalf
    (fun p hp => hvariance n f p hn hinvariant hp.1 hp.2)
  convert h using 1; ring

end Problem313

end

end OAI
