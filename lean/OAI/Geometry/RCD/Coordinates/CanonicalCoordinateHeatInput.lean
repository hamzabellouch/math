import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.CanonicalLocalLower

namespace OAI

/-! # Heat bounds for the coordinate construction -/

open MeasureTheory TopologicalSpace

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_coordinateBounds :
    HasCoordinateHeatBounds (hausdorff n X) (hX.canonicalHeatKernel hn p) where
  estimates ε hε _ := by
    obtain ⟨C,B,hC,hB,hupper⟩ := hX.canonicalHeatKernel_gaussian_upper hn p hε
    exact ⟨C,B,hC,hB,fun t ht x y =>
      ⟨hX.canonicalHeatKernel_nonneg hn p t x y,hupper t ht x y⟩⟩
  localLower := hX.canonicalHeatKernel_local_lower hn p

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
