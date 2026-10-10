import OAI.Geometry.RCD.Heat.BoundedHeatComplement
import OAI.Geometry.RCD.Heat.KernelHeatTimeMonotone

namespace OAI

/-! # The Li--Yau time monotonicity also holds for the bounded complement

The complement is obtained through its actual L2 truncations, so no
constant L2 function or finite total ambient measure is required.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem kernelHeat_complement_monotone (hK : K ≤ 0)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) (x : X) :
    MonotoneOn (fun t => Real.exp ((n:ℝ)*(Real.log t+|K| * t))*
      ((A:ℝ)-kernelHeat (hausdorff n X) hX.quadratic hk t f x)) (Ioi 0) := by
  obtain ⟨g,hg0,hgA,hlim⟩ := bounded_heat_complement_sequence
    (hausdorff n X) hX.quadratic hk p f A hf0 hf
  intro a ha b hb hab
  have hl := (hlim a ha x).const_mul (Real.exp ((n:ℝ)*(Real.log a+|K| * a)))
  have hr := (hlim b hb x).const_mul (Real.exp ((n:ℝ)*(Real.log b+|K| * b)))
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun k =>
    hX.kernelHeat_time_monotone hn p hK hk (g k) (hg0 k) A (hgA k) ha hab x)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
