import OAI.Geometry.RCD.Coordinates.KernelHeatBoundedRegularity

namespace OAI

/-! # The sharp Lipschitz bound for the actual kernel representative -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.kernel_heat_sharp_lipschitz {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (hf : φ =ᵐ[hausdorff n X] f)
    (M : ℝ) (hM : ∀ x, |φ x|≤M) {t : ℝ} (ht : 0<t) :
    LipschitzWith (L*⟨Real.exp (-K*t),(Real.exp_pos _).le⟩)
      (kernelHeat (hausdorff n X) hX.quadratic hk t f) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let := hX.openPos K n
  obtain ⟨U,hU,heU⟩ := hX.heat_lipschitz K n hn f hφ hf M hM ht.le
  have he : U=kernelHeat μ Q hk t f := Measure.eq_of_ae_eq
    (heU.symm.trans (kernelHeat_represents_L2 μ Q hk ht f).symm)
    hU.continuous (kernelHeat_continuous μ Q hk ht f)
  exact he ▸ hU

end RegularPointCoordinates

end

end OAI
