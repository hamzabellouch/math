import OAI.Geometry.RCD.Heat.HeatReverseEntropy
import OAI.Geometry.RCD.Transport.EntropyGapUpper

namespace OAI

/-! # The regularized Hamilton inequality against integrable weights

The affine entropy bound cancels by the proved heat mass conservation
and self-adjointness. No pointwise gradient estimate is assumed.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem heat_hamilton_weighted
    (f w : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (hw0 : 0≤w) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) (hw : ∀ᵐ x ∂hausdorff n X, |w x|≤B)
    (hwi : Integrable w (hausdorff n X)) {T ε : ℝ} (hT : 0<T) (hε : 0<ε) :
    T*Real.exp (-2*|K| * T)*
      (∫ x, w x*localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic T hT f)
        (heatSobolev (hausdorff n X) hX.quadratic T hT f) x /
        (ε+heatAt (hausdorff n X) hX.quadratic T f x) ∂hausdorff n X) ≤
      ∫ x, w x*(ε+heatAt (hausdorff n X) hX.quadratic T f x)*
        (Real.log (ε+A)-Real.log (ε+heatAt (hausdorff n X) hX.quadratic T f x)) ∂hausdorff n X := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  have hfr : ∀ᵐ x ∂μ, f x∈Icc 0 (A:ℝ) := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hf] with x hx hy
    exact ⟨hx,(le_abs_self _).trans hy⟩
  have hur : ∀ᵐ x ∂μ, heatAt μ Q T f x∈Icc 0 (A:ℝ) := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q T f hf0),
      heatAt_abs_le_const μ Q T A f hf] with x hx hy
    exact ⟨hx,(le_abs_self _).trans hy⟩
  have hmass : (∫ x, heatAt μ Q T w x ∂μ) = ∫ x, w x ∂μ :=
    hX.conservative K n hn p w hw0 hwi T hT.le
  have hgap := entropy_gap_upper μ f (heatAt μ Q T f) w (heatAt μ Q T w) hε A
    hfr hur (heatAt_nonneg μ Q T w hw0) hwi (heatAt_integrable μ Q T w hwi)
    hmass (heatAt_inner μ Q T w f)
  exact (hX.heat_reverse_entropy hn p f w hf0 hw0 A B hf hw hT hε).trans hgap

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
