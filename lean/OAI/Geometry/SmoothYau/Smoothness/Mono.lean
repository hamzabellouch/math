import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ProductFrequencyTop

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
namespace YauCounterexamples
open Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] [CompactSpace M] in
lemma ChartJetBound.mono {N : ℕ} {f : M → ℂ} {C D : ℝ}
    (h : A.ChartJetBound N f C) (hCD : C ≤ D) : A.ChartJetBound N f D :=
  fun i j hj y => (h i j hj y).trans hCD

theorem eventually_positive_factor_of_jets
    (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
    (N P : ℕ) (hN : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ) - N))
    (b s : ℕ → M → ℝ)
    (hb : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (b n))
    (hsmooth : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (s n))
    (hdata : ∀ᶠ n in atTop,
      A.ChartJetBound (2 * (k + 1)) (fun x => ((b n x - 1 : ℝ) : ℂ))
        (inverseFrequency n ^ (P + 8)) ∧
      A.ChartJetBound (2 * (k + 1)) (fun x => ((s n x - 1 : ℝ) : ℂ))
        (inverseFrequency n ^ (P + 8))) :
    ∀ᶠ n in atTop, ∃ u : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
      (∀ x, weightedLaplacian g (b n) u x =
        sphereFrequency n * b n x ^ 3 * u x ^ 5 - sphereFrequency n * s n x * u x) ∧
      A.ChartJetBound N (fun x => ((u x - 1 : ℝ) : ℂ)) (inverseFrequency n ^ P) := by
  have ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  obtain ⟨D, hD, hDbound⟩ := A.exists_jet_sobolev_constant (k + 1)
  obtain ⟨C, hC, hCbound⟩ := A.exists_chart_jet_constant N hN
  obtain ⟨he, hδ, hΛe, hΛδ, hratio, hpos⟩ := positive_factor_rates P D hD
  have hnorms : ∀ᶠ n in atTop,
      ‖A.realOfSmooth _ ht (fun x => b n x - 1) ((hb n).sub contMDiff_const)‖ ≤
        D * inverseFrequency n ^ (P + 8) ∧
      ‖A.realOfSmooth _ ht (fun x => s n x - 1) ((hsmooth n).sub contMDiff_const)‖ ≤
        D * inverseFrequency n ^ (P + 8) := by
    filter_upwards [hdata] with n hn
    have hpow : 0 ≤ inverseFrequency n ^ (P + 8) :=
      pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) _
    constructor
    · exact hDbound ⟨_, Complex.ofRealCLM.contMDiff.comp ((hb n).sub contMDiff_const)⟩ _ hpow hn.1
    · exact hDbound ⟨_, Complex.ofRealCLM.contMDiff.comp ((hsmooth n).sub contMDiff_const)⟩ _ hpow hn.2
  have hex := A.eventually_positive_factor hd B ht b s hb hsmooth sphereFrequency
    (fun n => D * inverseFrequency n ^ (P + 8)) (fun n => inverseFrequency n ^ (P + 4))
    sphereFrequency_atTop he hδ hΛe hΛδ hratio hpos hnorms
  filter_upwards [hex, eventual_output_rate P C] with n hn hr
  obtain ⟨u, hu, hup, hueq, h, hnorm, hv⟩ := hn
  refine ⟨u, hu, hup, hueq, ?_⟩
  have heq : A.representative (2 * ((k + 1 : ℕ) : ℝ)) h.val =
      fun x => ((u x - 1 : ℝ) : ℂ) := by
    ext x
    rw [← A.ofReal_realValue, hv]
  have hout := (hCbound h.val).mono A
    ((mul_le_mul_of_nonneg_left hnorm hC.le).trans hr)
  simpa only [heq] using hout
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
