import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryImageMass

namespace OAI

/-! # The common boundary window and its actual Haar characters -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory TopologicalSpace Set
open scoped ENNReal

variable {G S U W P : Type*} [Group G] [Group S] [Group U]
  [TopologicalSpace S] [MeasurableSpace S]
  [TopologicalSpace U] [MeasurableSpace U]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm U)
  (αS αT : W →L[ℝ] ℝ) (height : G →* Multiplicative W) (f : P → G → G)

/-- The measures, common window, and estimates produced by the compact
boundary shadows. These data are constructed below, not published inputs. -/
structure BoundaryVolumeComparison where
  boundary : P → S ≃ₜ U
  window : PositiveCompacts S
  sourceMeasure : Measure S
  targetMeasure : Measure U
  sourceHaar : sourceMeasure.IsHaarMeasure
  targetHaar : targetMeasure.IsHaarMeasure
  sourceRate : ℝ
  targetRate : ℝ
  sourceRate_pos : 0 < sourceRate
  targetRate_pos : 0 < targetRate
  source_volume : ∀ g E, sourceMeasure (actS g '' E) =
    ENNReal.ofReal (Real.exp (sourceRate * αS (height g).toAdd)) * sourceMeasure E
  target_volume : ∀ g E, targetMeasure (actT g '' E) =
    ENNReal.ofReal (Real.exp (targetRate * αT (height g).toAdd)) * targetMeasure E
  constant : ℝ
  constant_pos : 0 < constant
  mass : ∀ p x,
    ENNReal.ofReal (Real.exp (targetRate * αT (height (f p x)).toAdd)) ≤
      ENNReal.ofReal constant * targetMeasure
        (boundary p '' (actS x '' (window : Set S))) ∧
    targetMeasure (boundary p '' (actS x '' (window : Set S))) ≤
      ENNReal.ofReal constant *
        ENNReal.ofReal (Real.exp (targetRate * αT (height (f p x)).toAdd))
  traceBound : ℝ
  traceBound_nonneg : 0 ≤ traceBound
  equal_set_trace : ∀ p x y,
    actS x '' (window : Set S) =
      actS y '' (window : Set S) →
    |targetRate * αT (height (f p x)).toAdd - targetRate * αT (height (f p y)).toAdd| ≤ traceBound


end PolycyclicRecognition

end

end OAI
