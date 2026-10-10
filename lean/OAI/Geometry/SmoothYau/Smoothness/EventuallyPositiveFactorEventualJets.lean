import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ProductFrequencyTop
import OAI.Geometry.SmoothYau.Smoothness.Mono

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
open Set Filter Function
open scoped Topology ContDiff Manifold
namespace YauCounterexamples
open Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem eventually_positive_factor_of_eventual_jets
    (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
    (N P : ℕ) (hN : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ)-N))
    (b s : ℕ → M → ℝ)
    (hsmooth : ∀ᶠ n in atTop,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b n) ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s n))
    (hdata : ∀ᶠ n in atTop,
      A.ChartJetBound (2*(k+1)) (fun x => ((b n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) ∧
      A.ChartJetBound (2*(k+1)) (fun x => ((s n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8))) :
    ∀ᶠ n in atTop, ∃ v : M → ℝ,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
      (∀ x, weightedLaplacian g (b n) v x =
        sphereFrequency n*b n x^3*v x^5-sphereFrequency n*s n x*v x) ∧
      A.ChartJetBound N (fun x => ((v x-1:ℝ):ℂ)) (inverseFrequency n^P) := by
  classical
  let Good (n : ℕ) := ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b n) ∧
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s n)
  let b' (n : ℕ) : M → ℝ := if Good n then b n else fun _ => 1
  let s' (n : ℕ) : M → ℝ := if Good n then s n else fun _ => 1
  have hb' (n : ℕ) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b' n) := by
    by_cases hn : Good n
    · simpa [b', hn] using hn.1
    · simp only [b', ite_eq_right hn]
      exact contMDiff_const
  have hs' (n : ℕ) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s' n) := by
    by_cases hn : Good n
    · simpa [s', hn] using hn.2
    · simp only [s', ite_eq_right hn]
      exact contMDiff_const
  have hdata' : ∀ᶠ n in atTop,
      A.ChartJetBound (2*(k+1)) (fun x => ((b' n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) ∧
      A.ChartJetBound (2*(k+1)) (fun x => ((s' n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) := by
    filter_upwards [hsmooth,hdata] with n hn hj
    change Good n at hn
    simpa only [b',s',ite_eq_left hn] using hj
  have h := A.eventually_positive_factor_of_jets hd B N P hN b' s' hb' hs' hdata'
  filter_upwards [hsmooth,h] with n hn hv
  change Good n at hn
  simpa only [b',s',ite_eq_left hn] using hv
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
