import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseChart
import OAI.Geometry.Immersion.ClosedSurface.LocalMean

namespace OAI

/-! The mean geometry for an actual linear good phase: the coefficient
margin is transported exactly, and the pullback operator is constant. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean

lemma pullbackField_linearPhaseChart {ξ : Base} (hξ : ξ ≠ 0) {U : Set Base} (hU : IsOpen U)
    (x : Base) : pullbackField (linearPhaseChart ξ hξ U hU) x =
      pullback (phaseEquiv ξ hξ).toContinuousLinearMap := by
  change pullback (fderiv ℝ (phaseEquiv ξ hξ) x) = _
  rw [ContinuousLinearEquiv.fderiv]

theorem linear_phase_local_bounds {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base} (hU : IsOpen U) {ξ : Base} (hξ : ξ ≠ 0)
    (hImm : ∀ x ∈ U, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ U, Good (realSecondTensor F x) ξ)
    {ψ : Base → ℝ} (hψ : ContDiff ℝ ∞ ψ) (Q : PhaseMean.Tensor →L[ℝ] ℝ)
    {s r ρ R : ℝ} {reference : Base → PhaseMean.Tensor}
    (hmargin : ∀ x ∈ U, ρ + ‖Q‖*r ≤ Q (reference x) ∧ Q (reference x) ≤ R - ‖Q‖*r) :
    LocalBounds U (linearPhaseChart ξ hξ U hU).target s r ρ R reference
      (F ∘ (linearPhaseChart ξ hξ U hU).symm) ψ (fun _ => Q)
      (linearPhaseChart ξ hξ U hU) (linearPhaseChart ξ hξ U hU).symm := by
  have hsm := linearPhaseChart_smooth ξ hξ U hU
  refine {
    openU := hU
    smoothF := hF.comp hsm.2
    domain := linearPhaseChart_modeDomain hF hU hξ hImm hgood
    smoothPsi := hψ.contDiffOn
    smoothQ := contDiffOn_const
    smoothChi := hsm.1.contDiffOn
    smoothInv := hsm.2.contDiffOn
    chiInto := fun x hx => (linearPhaseChart ξ hξ U hU).map_source hx
    invInto := fun x hx => (linearPhaseChart ξ hξ U hU).map_target hx
    smoothPullback := ?_
    margin := ?_
  }
  · have he : pullbackField (linearPhaseChart ξ hξ U hU) =
        fun _ => pullback (phaseEquiv ξ hξ).toContinuousLinearMap :=
      funext (pullbackField_linearPhaseChart hξ hU)
    rw [he]
    exact contDiffOn_const
  · intro x hx
    exact hmargin _ ((linearPhaseChart ξ hξ U hU).map_target hx)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
