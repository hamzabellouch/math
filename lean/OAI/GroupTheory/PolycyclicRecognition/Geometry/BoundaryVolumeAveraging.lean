import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryVolumeComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryPublishedMetricAveraging

namespace OAI

/-! # Averaging the constructed boundary volume comparison -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

variable {G U W P N D ES : Type*} {S : Type} [Group G] [Group S] [Group U] [Group N]
  [TopologicalSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
  [SecondCountableTopology S]
  [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  [ChartedSpace ES S] [LieGroup (𝓘(ℝ, ES)) ⊤ S] [SimplyConnectedSpace S]
  {actS : G →* Equiv.Perm S} {actT : G →* Equiv.Perm U}
  {αS αT : W →L[ℝ] ℝ} {height : G →* Multiplicative W} {f : P → G → G}
  (C : BoundaryVolumeComparison actS actT αS αT height f)

/-- No metric or doubling condition on the boundary is assumed: the existing
published metric input and nilpotent exponential inputs supply them. -/
theorem BoundaryVolumeComparison.averaged_trace [SFinite C.targetMeasure]
    (metricInput : GeodesicMetricExistenceInput)
    (dynkin : NilpotentDynkinExpansionInput ES S)
    (haar : NilpotentExponentialHaarInput ES S)
    (Exp : GroupLieAlgebra (𝓘(ℝ, ES)) S → S) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, ES)) S))
    (hcont : ∀ x, Continuous (actS x))
    (ι : N →* G) (π : N →* S) (hπ : Function.Surjective π)
    (hact : ∀ n x, actS (ι n) x = π n * x)
    (d : D → G) {L : ℝ}
    (hleaf : ∀ p n j,
      |C.targetRate * αT (height (f p (ι n * d j))).toAdd -
        C.targetRate * αT (height (f p (d j))).toAdd| ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p j j₀,
      |(C.targetRate * αT (height (f p (d j))).toAdd -
          C.targetRate * αT (height (f p (d j₀))).toAdd) -
        (C.sourceRate * αS (height (d j)).toAdd -
          C.sourceRate * αS (height (d j₀)).toAdd)| ≤ B := by
  let : C.sourceMeasure.IsHaarMeasure := C.sourceHaar
  have hfin : C.sourceMeasure (C.window : Set S) ≠ ⊤ := C.window.isCompact.measure_ne_top
  have hpos : C.sourceMeasure (C.window : Set S) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior C.sourceMeasure C.window.interior_nonempty).ne'
  let c := (C.sourceMeasure (C.window : Set S)).toReal
  have hc : 0 < c := ENNReal.toReal_pos hpos hfin
  have hsource (j : D) : C.sourceMeasure (actS (d j) '' (C.window : Set S)) =
      ENNReal.ofReal (c * Real.exp (C.sourceRate * αS (height (d j)).toAdd)) := by
    rw [C.source_volume, ← ENNReal.ofReal_toReal hfin,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    exact mul_comm _ _
  exact boundary_averaged_trace_of_published_metric metricInput dynkin haar Exp hExp hnil
    C.sourceMeasure C.targetMeasure actS hcont ι π hπ hact C.boundary f
    (fun x => C.targetRate * αT (height x).toAdd) d
    (fun j => C.sourceRate * αS (height (d j)).toAdd) C.window C.window.isCompact
    hc C.constant_pos hsource C.mass hleaf

end PolycyclicRecognition

end

end OAI
