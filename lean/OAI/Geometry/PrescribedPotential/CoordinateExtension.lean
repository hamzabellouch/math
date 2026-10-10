import Mathlib
import OAI.Geometry.PrescribedPotential.CoordinateBalls
import OAI.Geometry.PrescribedPotential.CoordinatePotential

namespace OAI

/-! Coordinate Extension. -/

section

 

noncomputable section
open Set Metric Filter Topology
open scoped ContDiff
namespace Anticanonical.SourceSmooth
open EllipticKernel
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace CoordinateBall
variable (p : CoordinateBall A)

def coordExtension (φ : SmoothRealFunction A) : Coordinates d → ℝ :=
  p.extension φ ∘ (coordinateEquiv d).symm

lemma coordExtension_smooth (φ : SmoothRealFunction A) :
    ContDiff ℝ ∞ (p.coordExtension φ) := by
  exact (p.extension_smooth φ).comp
    ((coordinateEquiv d).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff

lemma coordExtension_apply (φ : SmoothRealFunction A) (z : EC d) :
    p.coordExtension φ (coordinateEquiv d z) = p.extension φ z := by
  simp only [coordExtension, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

lemma coordExtension_eventuallyEq (φ : SmoothRealFunction A) {z : EC d}
    (hz : z ∈ closedBall p.center (3*p.radius)) :
    p.coordExtension φ =ᶠ[𝓝 (coordinateEquiv d z)] φ.localExpression p.index := by
  have he := (p.extension_eventuallyEq φ hz).comp_tendsto
    ((coordinateEquiv d).symm.continuousAt.tendsto)
  simpa only [coordExtension, SmoothRealFunction.localExpression, Function.comp_def,
    ComplexAtlas.euclideanChart_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply, coordinateEquiv, PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp] using he

lemma coordExtension_hessian (φ : SmoothRealFunction A) {z : EC d}
    (hz : z ∈ closedBall p.center (3*p.radius)) :
    PotentialKaehler.potentialMatrix (p.coordExtension φ) (coordinateEquiv d z) =
      φ.hessian p.index (coordinateEquiv d z) :=
  PotentialKaehler.potentialMatrix_congr (p.coordExtension_eventuallyEq φ hz)
end CoordinateBall
end Anticanonical.SourceSmooth

end
end

end OAI
