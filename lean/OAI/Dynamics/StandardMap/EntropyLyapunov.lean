import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Lyapunov.ActualLyapunov

namespace OAI

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped ENNReal Topology

def PositiveLargestLyapunov (k : ℝ) : Prop :=
  ∃ E : Set Torus, MeasurableSet E ∧ 0 < area E ∧
    ∀ z ∈ E, ∃ l : ℝ, 0 < l ∧ LyapunovSpectrumAt k z l ∧
      Tendsto
        (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
        atTop (𝓝 l)

lemma positiveLargestLyapunov_of_ae_spectrum (k : ℝ) (L : Torus → ℝ)
    (hL : Measurable L)
    (hspec : ∀ᵐ z ∂area, LyapunovSpectrumAt k z (L z))
    (hrate : ∀ᵐ z ∂area, Tendsto
      (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 (L z)))
    (hpos : 0 < area {z | 0 < L z}) : PositiveLargestLyapunov k := by
  classical
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp (hspec.and hrate))
  refine ⟨{z | 0 < L z} \ N,
    (measurableSet_lt measurable_const hL).diff hNmeas, ?_, ?_⟩
  · simpa only [measure_sdiff_null hNnull] using hpos
  · intro z hz
    have hzgood : LyapunovSpectrumAt k z (L z) ∧ Tendsto
        (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
        atTop (𝓝 (L z)) := by
      by_contra hbad
      exact hz.2 (hNsub hbad)
    exact ⟨L z, hz.1, hzgood.1, hzgood.2⟩

theorem main_entropy_complete :
    ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, k₀ ≤ k →
      0 < metricEntropy area (standardMap k) ∧
      PositiveLargestLyapunov k ∧
      (0 < metricEntropy area (standardMap k) ↔ PositiveLargestLyapunov k) := by
  obtain ⟨K₁, hK₁, hEntropy⟩ := main_entropy
  obtain ⟨K₂, hK₂, hLyapunov⟩ := actual_positive_lyapunov
  refine ⟨max K₁ K₂, lt_of_lt_of_le hK₁ (le_max_left _ _), ?_⟩
  intro k hk
  have hEnt := hEntropy k ((le_max_left K₁ K₂).trans hk)
  obtain ⟨L, hL, _hLint, _hLinv, hspec, hrate, hpos⟩ :=
    hLyapunov k ((le_max_right K₁ K₂).trans hk)
  have hLyap : PositiveLargestLyapunov k :=
    positiveLargestLyapunov_of_ae_spectrum k L hL hspec hrate hpos
  exact ⟨hEnt, hLyap, ⟨fun _ => hLyap, fun _ => hEnt⟩⟩

end StandardMapEntropy

end OAI
