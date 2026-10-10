import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Lyapunov.DerivativeGrowth
import OAI.Dynamics.StandardMap.Lyapunov.PlaneLyapunov

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma ae_standardLyapunov_spectrum (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, LyapunovSpectrumAt k z (standardLyapunov k hk z) := by
  filter_upwards [ae_standardLyapunov_rate k hk] with z hz
  refine ⟨standardLyapunov_nonneg k hk z, ?_⟩
  rcases eq_or_lt_of_le (standardLyapunov_nonneg k hk z) with hzero | hpos
  · refine Or.inl ⟨hzero.symm, ?_⟩
    intro v hv
    apply PlaneLyapunov.all_growth_zero (standardDerivativeProduct k z)
      (standardDerivativeProduct_area k z) _ v hv
    simpa only [← hzero] using hz
  · refine Or.inr ⟨hpos, ?_⟩
    exact PlaneLyapunov.positive_flag (standardDerivativeProduct k z)
      (standardDerivativeProduct_area k z) (9*growthBase k)
      (mul_pos (by norm_num) (by have := growthBase_ge_four k hk; linarith))
      (standardDerivativeProduct_step_lower k hk z) hpos hz

theorem actual_positive_lyapunov :
    ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, k₀ ≤ k →
      ∃ L : Torus → ℝ, Measurable L ∧ Integrable L area ∧
        (∀ z, L (standardMap k z) = L z) ∧
        (∀ᵐ z ∂area, LyapunovSpectrumAt k z (L z)) ∧
        (∀ᵐ z ∂area, Tendsto
          (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
          atTop (𝓝 (L z))) ∧ 0 < area {z | 0 < L z} := by
  obtain ⟨K, hK, hdef⟩ := eventually_meanDeficit_small (1 / 8 : ℝ) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro k hk
  have hk0 : 0 ≤ k := hK.le.trans hk
  exact ⟨standardLyapunov k hk0, measurable_standardLyapunov k hk0,
    integrable_standardLyapunov k hk0, standardLyapunov_invariant k hk0,
    ae_standardLyapunov_spectrum k hk0, ae_standardLyapunov_rate k hk0,
    positive_standardLyapunov_of_deficit k hk0 (hdef k hk)⟩

end StandardMapEntropy

end
end

end OAI
