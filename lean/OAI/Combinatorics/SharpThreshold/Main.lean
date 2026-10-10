import OAI.Combinatorics.SharpThreshold.BlockOrbit
import OAI.Combinatorics.SharpThreshold.BlockParameters
import OAI.Combinatorics.SharpThreshold.FiniteParseval
import OAI.Combinatorics.SharpThreshold.FourierAnalysis
import OAI.Combinatorics.SharpThreshold.GraphSupport
import OAI.Combinatorics.SharpThreshold.GraphSymmetry
import OAI.Combinatorics.SharpThreshold.GraphVarianceBound
import OAI.Combinatorics.SharpThreshold.LowDegreeCounting
import OAI.Combinatorics.SharpThreshold.LowDegreeSupport
import OAI.Combinatorics.SharpThreshold.NoiseKernel
import OAI.Combinatorics.SharpThreshold.OrbitInfluence
import OAI.Combinatorics.SharpThreshold.ProductReindex
import OAI.Combinatorics.SharpThreshold.ProductRestriction
import OAI.Combinatorics.SharpThreshold.QuantileAnalysis
import OAI.Combinatorics.SharpThreshold.RestrictionMass
import OAI.Combinatorics.SharpThreshold.SharpThreshold

namespace OAI

noncomputable section

namespace Problem313

theorem variance_influence_bound :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (p : ℝ), 2 ≤ n → VertexInvariant f → 0 < p → p < 1 → graphVariance p f ≤ ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  exact variance_influence_bound_core

theorem sharp_threshold_width :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (ε : ℝ), 2 ≤ n → VertexInvariant f → IncreasingGraphProperty f → NontrivialGraphProperty f → 0 < ε → ε < (1 / 2 : ℝ) → graphQuantile (1 - ε) f - graphQuantile ε f ≤ ((2 : ℝ) ^ 19 / (Real.log (n : ℝ)) ^ 2) * Real.log (1 / (2 * ε)) := by
  exact sharp_threshold_width_of_variance_bound variance_influence_bound

end Problem313

end

end OAI
