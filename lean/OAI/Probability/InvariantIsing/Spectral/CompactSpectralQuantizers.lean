import OAI.Probability.InvariantIsing.Spectral.SpectralBallQuantizer
import OAI.Probability.InvariantIsing.Spectral.SpectralQuantizationWeak

namespace OAI

/-! Concrete finite quantizations of a compactly supported spectral law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace InvariantIsing

theorem exists_compact_spectral_quantizers
    (μ : ProbabilityMeasure ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x∈K) (a : ℝ) (ha : a∈K) :
    ∃ n : ℕ → ℕ, ∃ c r : (k : ℕ) → Fin (n k) → ℝ,
      (∀ k i, c k i∈K) ∧
      (∀ k i, 0 < r k i ∧ r k i < (1 : ℝ)/(k+1)) ∧
      (∀ k i, (μ : Measure ℝ) (frontier (ball (c k i) (r k i)))=0) ∧
      (∀ k, K ⊆ ⋃ i, ball (c k i) (r k i)) ∧
      (∀ k, ∀ᵐ x ∂(μ : Measure ℝ),
        dist (spectralBallQuantizer (c k) (r k) a x) x ≤ (1 : ℝ)/(k+1)) ∧
      (∀ k x, spectralBallQuantizer (c k) (r k) a x∈K) ∧
      Tendsto (fun k => μ.map (spectralBallQuantizer (c k) (r k) a)) atTop (𝓝 μ) := by
  have hex (k : ℕ) := spectral_null_boundary_cover (μ : Measure ℝ) K hK ((1 : ℝ)/(k+1)) (by positivity)
  choose n c r hc hr hn hb using hex
  have hclose (k : ℕ) : ∀ᵐ x ∂(μ : Measure ℝ),
      dist (spectralBallQuantizer (c k) (r k) a x) x ≤ (1 : ℝ)/(k+1) := by
    filter_upwards [hμ] with x hx
    exact spectralBallQuantizer_close (c k) (r k) a _ x (fun i => (hr k i).2.le) (hb k hx)
  refine ⟨n,c,r,hc,?_,hn,hb,hclose,?_,?_⟩
  · intro k i
    exact ⟨lt_trans (by positivity : (0:ℝ) < ((1:ℝ)/(k+1))/2) (hr k i).1,(hr k i).2⟩
  · intro k x
    exact spectralBallQuantizer_mem (c k) (r k) a K (hc k) ha x
  · exact spectral_quantization_weak μ (fun k => spectralBallQuantizer (c k) (r k) a)
      (fun k => measurable_spectralBallQuantizer _ _ _)
      (fun k => (1:ℝ)/(k+1)) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hclose

end InvariantIsing

end

end OAI
