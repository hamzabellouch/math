import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapConnectingArc

namespace OAI

/-! A smooth change of the longitudinal coordinate, leaving the
transverse coordinate fixed. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def axisParameterCoordinates (e : ℝ ≃ₜ ℝ) : Base ≃ₜ Base where
  toFun x := ![x 0,e.symm (x 1)]
  invFun x := ![x 0,e (x 1)]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using continuous_apply (0:Fin 2)
    · change Continuous (fun x : Base => e.symm (x 1))
      exact e.symm.continuous.comp (continuous_apply (1:Fin 2))
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using continuous_apply (0:Fin 2)
    · change Continuous (fun x : Base => e (x 1))
      exact e.continuous.comp (continuous_apply (1:Fin 2))

lemma axisParameterCoordinates_smooth {e : ℝ ≃ₜ ℝ}
    (he : ContDiff ℝ ∞ e.symm) : ContDiff ℝ ∞ (axisParameterCoordinates e) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simpa [axisParameterCoordinates] using contDiff_apply ℝ ℝ (0:Fin 2)
  · change ContDiff ℝ ∞ (fun x : Base => e.symm (x 1))
    simpa only [Function.comp_def] using he.comp (contDiff_apply ℝ ℝ (1:Fin 2))

lemma axisParameterCoordinates_inverse_smooth {e : ℝ ≃ₜ ℝ}
    (he : ContDiff ℝ ∞ e) : ContDiff ℝ ∞ (axisParameterCoordinates e).symm := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simpa [axisParameterCoordinates] using contDiff_apply ℝ ℝ (0:Fin 2)
  · change ContDiff ℝ ∞ (fun x : Base => e (x 1))
    simpa only [Function.comp_def] using he.comp (contDiff_apply ℝ ℝ (1:Fin 2))

lemma axisParameterCoordinates_axis (e : ℝ ≃ₜ ℝ) (t : ℝ) :
    axisParameterCoordinates e (crosscapAxis (e t)) = crosscapAxis t := by
  ext i
  fin_cases i <;> simp [axisParameterCoordinates,crosscapAxis_apply]

lemma axisParameterCoordinates_inverse_apply (e : ℝ ≃ₜ ℝ) (x : Base) :
    (axisParameterCoordinates e).symm x = ![x 0,e (x 1)] := rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
