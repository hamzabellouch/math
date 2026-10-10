import OAI.Analysis.MetricEntropy.DimensionRatio
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace OAI

/-!
# Entropy-ratio convergence and growing ambient dimension

For fixed degree and pivot count, the explicit rational entropy bound tends
to zero. The dimension conclusions use the actual cardinality lower bound
from the construction, together with the fact that a prime field has at
least two elements.
-/

open Filter Topology

namespace MetricEntropyDuality

/-- An asymptotic upper bound for the entropy ratio. -/
noncomputable def entropyRatioBound (h s r : ℕ) : ℝ :=
  2 * (h : ℝ) ^ 2 * s / ((r : ℝ) + h - 1) + 2 / (r : ℝ)

theorem tendsto_entropyRatioBound_zero (h s : ℕ) :
    Tendsto (entropyRatioBound h s) atTop (𝓝 0) := by
  have hr : Tendsto (fun r : ℕ => (r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun r : ℕ => (r : ℝ) + h - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ)
        (tendsto_atTop_add_const_right atTop (h : ℝ) hr)
  change Tendsto
    (fun r : ℕ => 2 * (h : ℝ) ^ 2 * s / ((r : ℝ) + h - 1) + 2 / (r : ℝ))
    atTop (𝓝 0)
  simpa only [zero_add] using
    (hden.const_div_atTop (2 * (h : ℝ) ^ 2 * s)).add
      (hr.const_div_atTop (2 : ℝ))

/-- Eventual two-sided estimates suffice; no monotonicity of the actual
entropy ratios is required. -/
theorem tendsto_zero_of_le_entropyRatioBound {h s : ℕ} {f : ℕ → ℝ}
    (hbound : ∀ᶠ r in atTop, 0 ≤ f r ∧ f r ≤ entropyRatioBound h s r) :
    Tendsto f atTop (𝓝 0) :=
  squeeze_zero' (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)
    (tendsto_entropyRatioBound_zero h s)

/-- A construction indexed only by positive ranks supplies the needed
eventual entropy estimates directly. -/
theorem tendsto_zero_of_positive_rank_bound {h s : ℕ} {f : ℕ → ℝ}
    (hbound : ∀ r, 0 < r → 0 ≤ f r ∧ f r ≤ entropyRatioBound h s r) :
    Tendsto f atTop (𝓝 0) :=
  tendsto_zero_of_le_entropyRatioBound
    ((eventually_ge_atTop (1 : ℕ)).mono fun r hr => hbound r hr)

theorem tendsto_formDimension_atTop {h : ℕ} (hh : 0 < h) :
    Tendsto (fun r : ℕ => formDimension r h) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  exact (eventually_ge_atTop (1 : ℕ)).mono fun r hr => rank_le_formDimension hr hh

/-- Actual ambient dimensions dominate the rank, even when the chosen
primes and dimensions fluctuate with it. -/
theorem tendsto_ambientDimension_atTop {h : ℕ} (hh : 0 < h)
    {p n : ℕ → ℕ} (hp : ∀ r, 0 < r → 2 ≤ p r)
    (hn : ∀ r, 0 < r → p r ^ formDimension r h ≤ n r) :
    Tendsto n atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  exact (eventually_ge_atTop (1 : ℕ)).mono fun r hr =>
    rank_le_ambientDimension hr hh (hp r hr) (hn r hr)

/-- Primality supplies the field-size condition in the concrete sequence. -/
theorem tendsto_ambientDimension_atTop_of_prime {h : ℕ} (hh : 0 < h)
    {p n : ℕ → ℕ} (hp : ∀ r, 0 < r → (p r).Prime)
    (hn : ∀ r, 0 < r → p r ^ formDimension r h ≤ n r) :
    Tendsto n atTop atTop :=
  tendsto_ambientDimension_atTop hh (fun r hr => (hp r hr).two_le) hn

end MetricEntropyDuality

end OAI
