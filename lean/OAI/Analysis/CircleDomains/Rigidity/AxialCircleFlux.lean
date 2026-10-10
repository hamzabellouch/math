import OAI.Analysis.CircleDomains.Rigidity.CircleProjectionFlux
import OAI.Analysis.CircleDomains.Rigidity.AxialLineDifferentiation

namespace OAI

/-! A common notation for the two axial circle fluxes. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def axialCircleIncrement (i : Fin 2) (F : ℂ → ℂ) (c : ℂ) (r y : ℝ) : ℝ :=
    (complexPlaneCoordinates.symm (F (complexCoordinateLine i y (axialChord i c r y).2))) i-
      (complexPlaneCoordinates.symm (F (complexCoordinateLine i y (axialChord i c r y).1))) i
 def axialCircleFlux (i : Fin 2) (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
    ∫ y in (transverseCoordinate i c-r)..(transverseCoordinate i c+r), axialCircleIncrement i F c r y

 theorem axialCircleIncrement_zero (F : ℂ → ℂ) (c : ℂ) (r y : ℝ) :
    axialCircleIncrement 0 F c r y = horizontalCircleIncrement F c r y := by
  change (F (complexCoordinateLine 0 y (axialChord 0 c r y).2)).re-
    (F (complexCoordinateLine 0 y (axialChord 0 c r y).1)).re = _
  simp [horizontalCircleIncrement,axialChord,axialSwap,horizontalChord,
    complexCoordinateLine,realCoordinateLine,horizontalCirclePoint,quadrantSign,
    Complex.equivRealProdCLM_symm_apply,Complex.mk_eq_add_mul_I,sub_eq_add_neg]

 theorem axialCircleIncrement_one (F : ℂ → ℂ) (c : ℂ) (r y : ℝ) :
    axialCircleIncrement 1 F c r y = verticalCircleIncrement F c r y := by
  change (F (complexCoordinateLine 1 y (axialChord 1 c r y).2)).im-
    (F (complexCoordinateLine 1 y (axialChord 1 c r y).1)).im = _
  simp [verticalCircleIncrement,axialChord,axialSwap,horizontalChord,
    complexCoordinateLine,realCoordinateLine,verticalCirclePoint,quadrantSign,
    Complex.equivRealProdCLM_symm_apply,Complex.mk_eq_add_mul_I,sub_eq_add_neg]

 theorem axialCircleFlux_add {F : ℂ → ℂ} (hF : Measurable F) (c : ℂ) {r B : ℝ}
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hb : ∀ z ∈ closedBall c r, ‖F z‖ ≤ B) :
    axialCircleFlux 0 F c r+axialCircleFlux 1 F c r = quadrantFlux F c r := by
  simpa only [axialCircleFlux,transverseCoordinate,ite_true,Fin.zero_eta,Fin.isValue,
    show ¬ (1 : Fin 2) = 0 by decide,ite_false,axialCircleIncrement_zero,axialCircleIncrement_one,
    horizontalCircleFlux,verticalCircleFlux] using circle_projection_flux hF c hr hB hb

end CircleDomainRigidity

end

end OAI
