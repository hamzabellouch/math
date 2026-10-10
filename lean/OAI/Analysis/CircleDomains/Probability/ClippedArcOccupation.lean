import OAI.Analysis.CircleDomains.Probability.SimpleArcOccupation
import OAI.Analysis.CircleDomains.Topology.RectifiableSubarcs
import OAI.Analysis.CircleDomains.Probability.PathPortionMeasure

namespace OAI

/-! A path that is injective only on a retained parameter interval has
exact Hausdorff occupation on that portion. Constant tails add no mass. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_portion_occupation
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) {a b : PathTime} (hab : a < b)
    (hinj : InjOn γ.val (Icc a b)) :
    pathPortionOccupation γ a b = (μH[1] : Measure X).restrict (γ.val '' Icc a b) := by
  let β := affineRectifiablePath γ hab
  have hβ : Injective β.val := by
    intro s t h
    exact (affinePathTime_strictMono hab).injective
      (hinj (affinePathTime_mem_Icc hab.le s) (affinePathTime_mem_Icc hab.le t) h)
  have hrange : range β.val = γ.val '' Icc a b := by
    change range (γ.val ∘ affinePathTime a b) = _
    rw [range_comp, range_affinePathTime hab]
  change ((pathLengthMeasure γ).restrict (Icc a b)).map γ.val = _
  rw [← pathOccupation_affine γ hab, simple_arc_occupation β hβ, hrange]

theorem clipped_simple_arc_occupation
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) {a b : PathTime} (hab : a < b)
    (hinj : InjOn γ.val (Icc a b)) :
    pathOccupation (clippedPath γ hab.le) =
      (μH[1] : Measure X).restrict (γ.val '' Icc a b) := by
  rw [pathOccupation_clipped γ hab.le, simple_arc_portion_occupation γ hab hinj]

end CircleDomainRigidity

end

end OAI
