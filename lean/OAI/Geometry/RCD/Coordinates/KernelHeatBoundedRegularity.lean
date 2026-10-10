import OAI.Geometry.RCD.Heat.KernelHeatL2Representation
import OAI.Geometry.RCD.Heat.BoundedHeatOrder

namespace OAI

/-! # Bounded heat regularity for the canonical kernel representative -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem kernelHeat_bounded_regularity {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hC : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C) (t : ℝ) (ht : 0 < t) :
    LipschitzWith ⟨Real.sqrt ((C:ℝ)^2/(2*t*Real.exp (-2 * |K| * t))),Real.sqrt_nonneg _⟩
      (kernelHeat (hausdorff n X) hX.quadratic hk t f) ∧
      ∀ x, |kernelHeat (hausdorff n X) hX.quadratic hk t f x| ≤ C := by
  have hf : HasBoundedAmplitude f := ⟨C,hC⟩
  have he : hX.boundedHeat hn p f hf t ht = kernelHeat (hausdorff n X) hX.quadratic hk t f :=
    hX.boundedHeat_unique hn p f hf t ht
      (kernelHeat_continuous (hausdorff n X) hX.quadratic hk ht f)
      (kernelHeat_represents_L2 (hausdorff n X) hX.quadratic hk ht f).symm
  rw [← he]
  exact ⟨hX.boundedHeat_lipschitz hn p f hf t ht C hC,
    hX.boundedHeat_abs_le hn p f hf t ht C hC⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
