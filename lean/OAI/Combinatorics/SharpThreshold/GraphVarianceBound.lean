import OAI.Combinatorics.SharpThreshold.Probability
import OAI.Combinatorics.SharpThreshold.FourierVariance
import OAI.Combinatorics.SharpThreshold.FourierDirichlet
import OAI.Combinatorics.SharpThreshold.BlockSize
import OAI.Combinatorics.SharpThreshold.VarianceReduction
import OAI.Combinatorics.SharpThreshold.GraphBlockAverage

namespace OAI

noncomputable section

namespace Problem313

/-- The graph-level variance reduction, with the two spectral identities and
large-scale block capture supplied explicitly. No symmetry is needed after
these inputs have been obtained. -/
theorem graphVariance_bound_of_spectral_inputs {n : ℕ}
    (f : GraphConfig n → Bool) (p : ℝ) (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1)
    (hvariance : graphVariance p f =
      ∑ S : Finset (GraphEdge n) with S.Nonempty,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2)
    (hdirichlet : (∑ S : Finset (GraphEdge n), (S.card : ℝ) *
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) =
      p * (1 - p) * totalInfluence p f)
    (hcapture : 16 ≤ Real.log (n : ℝ) →
      (∑ S : Finset (GraphEdge n) with S.Nonempty ∧
          (S.card : ℝ) ≤ (Real.sqrt (p * (1 - p)) *
            Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) * totalInfluence p f) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  classical
  have hbias : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
  have hsigma : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.2 hbias
  have hsigma_sq : Real.sqrt (p * (1 - p)) ^ 2 ≤ 1 / 4 := by
    rw [Real.sq_sqrt hbias.le]
    nlinarith [sq_nonneg (p - 1 / 2)]
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  apply variance_bound_of_fourier_inputs
    (BiasedFourier.coeff p (fun x => boolReal (f x)))
    (graphVariance p f) (Real.sqrt (p * (1 - p)))
    (totalInfluence p f) (Real.log (n : ℝ))
    hsigma hsigma_sq (totalInfluence_nonneg hp.le hp1.le f) hlog hvariance
  · simpa only [Real.sq_sqrt hbias.le] using hdirichlet
  · intro ht
    refine ⟨(⌊Real.sqrt (n : ℝ)⌋₊ : ℝ), ?_, log_sqrt_block_lower n hn ht, hcapture ht⟩
    have hm := (sqrt_block_size_bounds n hn ht).1
    exact_mod_cast (by omega : 0 < ⌊Real.sqrt (n : ℝ)⌋₊)

/-- Parseval discharges the variance identity, leaving the Dirichlet and captured-mass inputs. -/
theorem graphVariance_bound_of_dirichlet_capture {n : ℕ}
    (f : GraphConfig n → Bool) (p : ℝ) (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1)
    (hdirichlet : (∑ S : Finset (GraphEdge n), (S.card : ℝ) *
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) =
      p * (1 - p) * totalInfluence p f)
    (hcapture : 16 ≤ Real.log (n : ℝ) →
      (∑ S : Finset (GraphEdge n) with S.Nonempty ∧
          (S.card : ℝ) ≤ (Real.sqrt (p * (1 - p)) *
            Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) * totalInfluence p f) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  exact graphVariance_bound_of_spectral_inputs f p hn hp hp1
    (graphVariance_eq_fourier_sum_nonempty hp hp1 f) hdirichlet hcapture

/-- All spectral and numerical ingredients are discharged; only the graph-specific
large-scale captured-mass estimate remains. -/
theorem graphVariance_bound_of_capture {n : ℕ}
    (f : GraphConfig n → Bool) (p : ℝ) (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1)
    (hcapture : 16 ≤ Real.log (n : ℝ) →
      (∑ S : Finset (GraphEdge n) with S.Nonempty ∧
          (S.card : ℝ) ≤ (Real.sqrt (p * (1 - p)) *
            Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) * totalInfluence p f) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  exact graphVariance_bound_of_dirichlet_capture f p hn hp hp1
    (graph_fourier_dirichlet hp hp1 f) hcapture

/-- The graph variance bound, with all spectral, analytic, counting, and
numerical inputs discharged. -/
theorem variance_influence_bound_core
    (n : ℕ) (f : GraphConfig n → Bool) (p : ℝ)
    (hn : 2 ≤ n) (hf : VertexInvariant f) (hp : 0 < p) (hp1 : p < 1) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  classical
  apply graphVariance_bound_of_capture f p hn hp hp1
  intro ht
  simpa only [Finset.sum_filter] using
    graph_fourier_captured_mass f hn ht hf hp hp1

end Problem313

end

end OAI
