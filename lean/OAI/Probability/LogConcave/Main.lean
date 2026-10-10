import Mathlib
import OAI.Probability.LogConcave.JetEstimates.ClosedWireLintegralBound
import OAI.Probability.LogConcave.JetEstimates.Reindex
import OAI.Probability.LogConcave.LowerBounds.HardEigenOutput
import OAI.Probability.LogConcave.OraclePrograms.NoisyCenterSquaredError
import OAI.Probability.LogConcave.Sampling.MatrixColor
import OAI.Probability.LogConcave.OraclePrograms.DampingCoefficient
import OAI.Probability.LogConcave.Sampling.HarmonicMeanTaylorRms
import OAI.Probability.LogConcave.Dynamics.StationaryIntegral
import OAI.Probability.LogConcave.Numerics.TaylorRemainderRms
import OAI.Probability.LogConcave.OraclePrograms.ShiftInvariant
import OAI.Probability.LogConcave.OraclePrograms.MeanTreeBase
import OAI.Probability.LogConcave.OraclePrograms.PairDistBounds
import OAI.Probability.LogConcave.OraclePrograms.SampleCorrect
import OAI.Probability.LogConcave.Sampling.MixingEnvelope

namespace OAI

/-! Subpolynomial upper bounds and logarithmic lower bounds for exact first-order sampling, with optimal dimension exponent zero. -/

section

noncomputable section
namespace LogConcaveSampling
open Filter MeasureTheory
open scoped Topology ENNReal

lemma CanSample.queryComplexity_le {d q : ℕ} (hq : CanSample d q) :
    (queryComplexity d).toENNReal≤ENNReal.ofReal (q:ℝ) := by
  have hle : queryComplexity d≤(q:ℕ∞) := sInf_le ⟨q,hq,rfl⟩
  simpa only [ENat.toENNReal_coe,ENNReal.ofReal_natCast] using ENat.toENNReal_mono hle

theorem source_subpolynomial_upper :
    ∀ ε : ℝ,0<ε → ∃ C : ℝ,∀ d : ℕ,2≤d →
      (queryComplexity d).toENNReal≤ENNReal.ofReal (C*(d:ℝ)^ε) := by
  intro ε hε
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp (eventually_subpolynomial_sampler hε)
  let C : ℝ := (10*2^d₀:ℕ)+1
  have hC : 1≤C := by dsimp [C]; have := (Nat.cast_nonneg (10*2^d₀) : (0:ℝ)≤_); linarith
  refine ⟨C,?_⟩
  intro d hd
  have hd1 : (1:ℝ)≤d := by exact_mod_cast (by omega : 1≤d)
  have hp : 1≤(d:ℝ)^ε := Real.one_le_rpow hd1 hε.le
  by_cases hlarge : d₀≤d
  · obtain ⟨q,hq,hqbound⟩ := hd₀ d hlarge
    exact hq.queryComplexity_le.trans (ENNReal.ofReal_le_ofReal
      (hqbound.trans (by nlinarith)))
  · have hsmall : d≤d₀ := by omega
    have hpow : (10*2^d:ℕ)≤10*2^d₀ := by gcongr
    have hq : ((10*2^d:ℕ):ℝ)≤C := by dsimp [C]; exact_mod_cast (by omega : 10*2^d≤10*2^d₀+1)
    exact (finite_dimension_sampler d).queryComplexity_le.trans
      (ENNReal.ofReal_le_ofReal (hq.trans (by nlinarith)))

theorem source_exponent_zero : ExponentBound 0 := by
  refine ⟨le_rfl,?_⟩
  intro ε hε
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp (eventually_subpolynomial_sampler hε)
  refine ⟨d₀,?_⟩
  intro d hd
  obtain ⟨q,hq,hqbound⟩ := hd₀ d hd
  simpa only [zero_add] using hq.queryComplexity_le.trans (ENNReal.ofReal_le_ofReal hqbound)

theorem source_gammaStar_zero : gammaStar=0 := by
  apply le_antisymm
  · exact csInf_le ⟨0,fun _ h => h.1⟩ source_exponent_zero
  · exact le_csInf ⟨0,source_exponent_zero⟩ (fun _ h => h.1)

theorem exact_source_main :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d →
      (queryComplexity d).toENNReal ≤ ENNReal.ofReal (C * (d : ℝ) ^ ε)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ENNReal.ofReal (c * Real.log (d : ℝ)) ≤ (queryComplexity d).toENNReal) ∧
    gammaStar = 0 := by
  exact ⟨source_subpolynomial_upper,LowerBound.source_logarithmic_lower,source_gammaStar_zero⟩

end LogConcaveSampling

end

end

end OAI
