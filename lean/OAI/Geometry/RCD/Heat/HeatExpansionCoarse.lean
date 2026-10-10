import OAI.Geometry.RCD.Transport.DimensionalExpansionZero
import OAI.Geometry.RCD.Metric.CoarseEvolutionBound

namespace OAI

/-! # The two-time estimate with a simple exponential coefficient -/

open MeasureTheory TopologicalSpace
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.heat_two_time_expansion
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N) (p : X)
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {rf : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ rf)
    (hg0 : 0 ≤ g) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hgm : ∫x, g x ∂hausdorff n X = 1)
    {rg : ℝ} (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ rg)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic s f)
      (heatMeasure (hausdorff n X) hX.quadratic t g)).toReal ≤
      Real.exp (-K*(s+t))*
        ((wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic 0 f)
          (heatMeasure (hausdorff n X) hX.quadratic 0 g)).toReal+
          2*N*(Real.sqrt s-Real.sqrt t)^2) := by
  have hh := hX.heat_dimensional_expansion K n hn hK hN p f g C
    hf0 hfC hfm hfs hg0 hgC hgm hgs hs ht (b := 1) zero_le_one
  simp only [mul_one] at hh
  have hN0 : 0 ≤ N := (Nat.cast_nonneg n).trans hN
  have hb := gronwallBound_one_le (d := (wassersteinSq
      (heatMeasure (hausdorff n X) hX.quadratic 0 f)
      (heatMeasure (hausdorff n X) hX.quadratic 0 g)).toReal)
    (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hK (add_nonneg hs.le ht.le)))
    (show 0 ≤ 2*N*(Real.sqrt s-Real.sqrt t)^2 by positivity)
  rw [show -(K*(s+t)) = -K*(s+t) by ring] at hb
  exact hh.trans (hb.trans_eq (mul_comm _ _))

end RegularPointCoordinates

end

end OAI
