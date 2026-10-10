import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingMeasureLimits
import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitWindowMeasures

namespace OAI

/-!
# Small corrections commuting with the averaging dynamics

The correcting element may change with the sample and the averaging
length may grow arbitrarily fast. Commutation transports the correction
outside the entire window. The compact-observable estimate then controls
it uniformly over all starting points, without an ergodic-element premise.
-/

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology BoundedContinuousFunction

namespace DukePrimeDegree

variable {G X I : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [TopologicalSpace X] [LocallyCompactSpace X]
  [T2Space X] [MetrizableSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]
  {l : Filter I} [NeBot l]

omit [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G] [LocallyCompactSpace X]
  [T2Space X] [MetrizableSpace X] [SigmaCompactSpace X] in
/-- Exact transport of the correction through a finite orbit window. -/
lemma orbitWindowProbability_commuting_smul
    (ν : ProbabilityMeasure X) (T : X → X) (hT : Measurable T)
    (a : G) (hcomm : Function.Commute T (fun x => a • x)) (N : ℕ) :
    orbitWindowProbability (ν.map (fun x => a • x)) T hT N =
      (orbitWindowProbability ν T hT N).map (fun x => a • x) := by
  apply Subtype.ext
  exact (orbitWindowMeasure_map (ν : Measure X) T hT T hT
    (fun x => a • x) (continuous_const_smul a).measurable hcomm.symm N).symm

omit [NeBot l] [LocallyCompactSpace X] [T2Space X] [MetrizableSpace X]
  [SigmaCompactSpace X] in
/-- This estimate is independent of the rate of growth of the window
length, because compact observables have a global translation modulus. -/
theorem commuting_corrections_window_integral_tendsto_zero
    (ν : I → ProbabilityMeasure X) (T : X → X) (hT : Measurable T)
    (a : I → G) (ha : Tendsto a l (𝓝 1))
    (hcomm : ∀ i, Function.Commute T (fun x => a i • x))
    (N : I → ℕ) (f : CompactlySupportedContinuousMap X ℝ) :
    Tendsto (fun i =>
      (∫ x, f x ∂(orbitWindowProbability ((ν i).map (fun y => a i • y)) T hT (N i) : Measure X)) -
      ∫ x, f x ∂(orbitWindowProbability (ν i) T hT (N i) : Measure X))
      l (𝓝 0) := by
  have hh := integral_compact_observable_varying_smul
    (fun i => orbitWindowProbability (ν i) T hT (N i)) f a 1 ha
  have he (i : I) :
      (∫ x, f x ∂(orbitWindowProbability ((ν i).map (fun y => a i • y)) T hT (N i) : Measure X)) =
      ∫ x, f (a i • x) ∂(orbitWindowProbability (ν i) T hT (N i) : Measure X) := by
    rw [orbitWindowProbability_commuting_smul (ν i) T hT (a i) (hcomm i),
      ProbabilityMeasure.toMeasure_map]
    exact integral_map (continuous_const_smul (a i)).measurable.aemeasurable
      f.continuous.aestronglyMeasurable
  simpa only [he, one_smul] using hh

omit [NeBot l] [LocallyCompactSpace X] [T2Space X] [MetrizableSpace X]
  [SigmaCompactSpace X] in
/-- If the original window has the desired compact-observable limit,
the corrected initial law has the same limit. -/
theorem commuting_corrections_preserve_window_integral_limit
    (ν : I → ProbabilityMeasure X) (T : X → X) (hT : Measurable T)
    (a : I → G) (ha : Tendsto a l (𝓝 1))
    (hcomm : ∀ i, Function.Commute T (fun x => a i • x))
    (N : I → ℕ) (f : CompactlySupportedContinuousMap X ℝ) (c : ℝ)
    (hlim : Tendsto (fun i =>
      ∫ x, f x ∂(orbitWindowProbability (ν i) T hT (N i) : Measure X)) l (𝓝 c)) :
    Tendsto (fun i =>
      ∫ x, f x ∂(orbitWindowProbability ((ν i).map (fun y => a i • y)) T hT (N i) : Measure X))
      l (𝓝 c) := by
  have hh := (commuting_corrections_window_integral_tendsto_zero ν T hT a ha hcomm N f).add hlim
  simpa only [sub_add_cancel, zero_add] using hh

end DukePrimeDegree

end

end OAI
