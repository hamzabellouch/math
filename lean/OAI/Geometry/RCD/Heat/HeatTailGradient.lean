import OAI.Geometry.RCD.Heat.BoundedHeatOrder

namespace OAI

/-! # One gradient bound for an entire smoothed heat tail

The outer heat time is fixed and positive. Markov contraction bounds its
input at every parameter value, including before the tail equals heat.
-/

open MeasureTheory TopologicalSpace
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem heatTail_gradient_bound (f : Lp ℝ 2 (hausdorff n X))
    (A : ℝ≥0) (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A)
    {a : ℝ} (ha : 0<a) :
    ∃ L : ℝ≥0, ∀ s : ℝ, ∀ᵐ x ∂hausdorff n X,
      SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatTail (hausdorff n X) hX.quadratic a ha f s) x≤L := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let L : ℝ≥0 := ⟨Real.sqrt ((A:ℝ)^2/(2*a*Real.exp (-2 * |K| * a))),Real.sqrt_nonneg _⟩
  refine ⟨L,?_⟩
  intro s
  let g := heatAt μ Q (s-a) f
  have hg : ∀ᵐ x ∂μ, |g x|≤A := heatAt_abs_le_const μ Q (s-a) A f hf
  have hLip := hX.boundedHeat_lipschitz hn p g ⟨A,hg⟩ a ha A hg
  have hrep := hX.boundedHeat_represents hn p g ⟨A,hg⟩ a ha
  exact SobolevSpace.minimalSlope_le_lipschitz μ Q
    (heatSobolev μ Q a ha g) hLip hrep

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
