import OAI.Probability.InvariantIsing.Magnetic.MagneticSpectralContinuity
import OAI.Probability.InvariantIsing.Spectral.MeasureVariationalContinuity

namespace OAI

/-! Compact spectral weak convergence preserves the finite-field magnetic value. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical
namespace InvariantIsing

theorem measureMagnetic_tendsto_weak {A : Type*} [Fintype A]
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    {K : ℝ} (hK : 0 < K) (he : e ≤ K) (hes : ∀ k, es k ≤ K)
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ∈ Icc (-K) (es k))
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Icc (-K) e)
    (γ b : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) :
    Tendsto (fun k => (finiteMagneticFunctional (measureR (μs k : Measure ℝ) (es k)) γ b).toReal)
      atTop (𝓝 (finiteMagneticFunctional (measureR (μ : Measure ℝ) e) γ b).toReal) := by
  have hf0 := measureVariational_ne_top_bot (μ : Measure ℝ) hK he hμ
  have hf := finiteMagneticFunctional_ne_top_bot _ γ b hγ hγsum hf0.1 hf0.2
  have hR := continuous_measureR (μ : Measure ℝ) hK he hμ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [measureR_uniform_weak μs μ es e hweak hedge hK he hes hs hμ ε hε] with k hk
  have hfk0 := measureVariational_ne_top_bot (μs k : Measure ℝ) hK (hes k) (hs k)
  have hfk := finiteMagneticFunctional_ne_top_bot _ γ b hγ hγsum hfk0.1 hfk0.2
  have hRk := continuous_measureR (μs k : Measure ℝ) hK (hes k) (hs k)
  have hl := finiteMagneticFunctional_spectral_le_add γ b _ _ hRk hR ε (fun x hx => (hk x hx).le)
  have hr := finiteMagneticFunctional_spectral_le_add γ b _ _ hR hRk ε
    (fun x hx => by simpa only [abs_sub_comm] using (hk x hx).le)
  rw [← EReal.coe_toReal hfk.1 hfk.2, ← EReal.coe_toReal hf.1 hf.2,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hl hr
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end InvariantIsing

end

end OAI
