import OAI.Geometry.RCD.Heat.HeatAverageTwoTimeDual
import OAI.Geometry.RCD.Harmonic.AverageQuadraticError

namespace OAI

/-! # Pointwise two-time transport duality for continuous heat representatives -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.heat_pointwise_two_time_dual
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (hK : K ≤ 0) {dN : ℝ} (hNdim : (n:ℝ) ≤ dN)
    (f g : Lp ℝ 2 (hausdorff n X)) {φ ψ : X → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hf : φ =ᵐ[hausdorff n X] f) (hg : ψ =ᵐ[hausdorff n X] g)
    (M N : ℝ) (hM : ∀ x, |φ x| ≤ M) (hN : ∀ x, |ψ x| ≤ N)
    {c : ℝ} (hc0 : 0 ≤ c) (hd : ∀ x y, ψ x-φ y ≤ c*dist x y^2)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ U V : X → ℝ, Continuous U → Continuous V →
      (heatAt (hausdorff n X) hX.quadratic s g : X → ℝ) =ᵐ[hausdorff n X] U →
      (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V →
      ∀ x y, U x-V y ≤ c*Real.exp (-K*(s+t))*
        (dist x y^2+2*dN*(Real.sqrt s-Real.sqrt t)^2) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsUnifLocDoublingMeasure μ := hX.locDoubling K n hn
  let : μ.IsOpenPosMeasure := hX.openPos K n
  intro U V hU hV heU heV
  have ha := hX.heat_average_two_time_dual K n hn hK hNdim f g hφ hψ hf hg M N hM hN hc0 hd hs ht
  have hb := quadratic_comparison_of_average_bound_add _ _ U V
    ((Lp.memLp _).locallyIntegrable (by norm_num)) ((Lp.memLp _).locallyIntegrable (by norm_num))
    hU hV heU heV (c*Real.exp (-K*(s+t)))
    (c*Real.exp (-K*(s+t))*(2*dN*(Real.sqrt s-Real.sqrt t)^2)) (by
      intro x y r hr
      simpa only [mul_add] using ha x y r hr)
  intro x y
  simpa only [mul_add] using hb x y

end RegularPointCoordinates

end OAI
