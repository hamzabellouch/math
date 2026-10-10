import OAI.Analysis.FiniteFactor.CrossedProduct.EventLossAssembly
import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionDiagonal

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- The actual source E_j has an eventual fixed positive lower bound for
any nontrivial invariant projection of the original algebra. The threshold
may depend on p; the positive lower bound does not. -/
theorem sourceProjectionEvent_eventually_positive
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (hr : SourceRationalIndependent θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    ∀ᶠ j : ℕ in atTop, Real.exp (-82)/2 ≤ (sourceBiasedLaw j).real (sourceProjectionEvent p j) := by
  have hdiag := sourceProjection_strict_diagonal θ hθ hr hp hproj hp0 hp1 hinv
  have hm : Measurable (fun x => (sourceCentralCoefficient p x).re) :=
    Complex.continuous_re.measurable.comp (sourceCentralCoefficient_measurable p)
  have hpos0 : ∀ᵐ x ∂sourceBaseMeasure, 0 < (sourceCentralCoefficient p x).re :=
    hdiag.mono fun _ h => h.1
  have hpos1 : ∀ᵐ x ∂sourceBaseMeasure, 0 < 1-(sourceCentralCoefficient p x).re :=
    hdiag.mono fun _ h => sub_pos.mpr h.2.1
  have ht0 : Tendsto (fun j => (sourceBiasedLaw j).real (sourceDiagonalLossSet p j false)) atTop (𝓝 0) :=
    sourceBiased_positive_endpoint_loss _ hm hpos0 false
  have ht1 : Tendsto (fun j => (sourceBiasedLaw j).real (sourceDiagonalLossSet p j true)) atTop (𝓝 0) :=
    sourceBiased_positive_endpoint_loss _ (measurable_const.sub hm) hpos1 true
  have ht := (sourceFutureBoundary_loss_tendsto.add ht0).add ht1
  simp only [zero_add] at ht
  have he := ht.eventually (gt_mem_nhds (half_pos (Real.exp_pos (-82))))
  filter_upwards [he] with j hj
  have hh := sourceProjectionEvent_mass_losses p j
  linarith

end
end FiniteFactor

end OAI
