import OAI.Geometry.SurfaceImmersion.Atlas.PhaseReparametrization
import OAI.Geometry.Immersion.ClosedSurface.AtlasPhases

namespace OAI

/-! The explicit restricted linear chart used for a nonzero phase covector. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def linearPhaseChart (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U) :
    OpenPartialHomeomorph Base Base where
  toFun := phaseEquiv ξ hξ
  invFun := (phaseEquiv ξ hξ).symm
  source := U
  target := (phaseEquiv ξ hξ) '' U
  map_source' := fun x hx => ⟨x,hx,rfl⟩
  map_target' := by
    rintro y ⟨x,hx,rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  left_inv' := fun x _ => (phaseEquiv ξ hξ).symm_apply_apply x
  right_inv' := fun x _ => (phaseEquiv ξ hξ).apply_symm_apply x
  open_source := hU
  open_target := (phaseEquiv ξ hξ).isOpenMap U hU
  continuousOn_toFun := (phaseEquiv ξ hξ).continuous.continuousOn
  continuousOn_invFun := (phaseEquiv ξ hξ).symm.continuous.continuousOn

@[simp] lemma linearPhaseChart_source (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U) :
    (linearPhaseChart ξ hξ U hU).source = U := rfl

@[simp] lemma linearPhaseChart_target (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U) :
    (linearPhaseChart ξ hξ U hU).target = (phaseEquiv ξ hξ) '' U := rfl

@[simp] lemma linearPhaseChart_apply (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U)
    (x : Base) : linearPhaseChart ξ hξ U hU x = phaseEquiv ξ hξ x := rfl

@[simp] lemma linearPhaseChart_symm_apply (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U)
    (x : Base) : (linearPhaseChart ξ hξ U hU).symm x = (phaseEquiv ξ hξ).symm x := rfl

lemma linearPhaseChart_smooth (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U) :
    ContDiff ℝ ∞ (linearPhaseChart ξ hξ U hU) ∧
      ContDiff ℝ ∞ (linearPhaseChart ξ hξ U hU).symm :=
  ⟨(phaseEquiv ξ hξ).contDiff,(phaseEquiv ξ hξ).symm.contDiff⟩

lemma linearPhaseChart_phase (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U)
    (x : Base) : (linearPhaseChart ξ hξ U hU x).1 = phaseLinear ξ x := rfl

lemma linearPhaseChart_modeDomain {F : RealModes.RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base} (hU : IsOpen U) {ξ : Base} (hξ : ξ ≠ 0)
    (hImm : ∀ x ∈ U, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ U, Good (RealModes.realSecondTensor F x) ξ) :
    RealModes.RealModeDomain (F ∘ (linearPhaseChart ξ hξ U hU).symm)
      (linearPhaseChart ξ hξ U hU).target :=
  RealModes.realModeDomain_phase hF hU hξ hImm hgood

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
