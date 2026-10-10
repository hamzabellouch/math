import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GaussianLine

namespace OAI

/-! Normalized Gaussian variance and energy on the real line. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace ContinuumCoulomb
open LeanBlast.KLS

theorem gaussianLine_expectation {freq : ℝ} (hf : 0 < freq) (f : ℝ → ℝ) :
    (∫ x : Space 1, f (gaussianLineEquiv x)
      ∂potentialMeasure (fun x : Space 1 => freq*‖x‖^2)) =
      ∫ z : ℝ, verticalMode freq z^2*f z := by
  rw [integral_potentialMeasure]
  have hw (x : Space 1) : Real.exp (-(freq*‖x‖^2)) =
      Real.exp (-freq*(gaussianLineEquiv x)^2) := by
    rw [gaussianLine_norm_sq]
    congr 1
    ring
  have hp : potentialPartition (fun x : Space 1 => freq*‖x‖^2) =
      Real.sqrt (Real.pi/freq) := by
    unfold potentialPartition
    simp_rw [hw]
    rw [gaussianLine_integral (fun z => Real.exp (-freq*z^2)),integral_gaussian]
  rw [hp]
  simp_rw [hw]
  rw [gaussianLine_integral (fun z => Real.exp (-freq*z^2)*f z),← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    rw [verticalMode_square hf]
    ring

/-- The exact weighted Poincare constant for compact smooth real functions. -/
theorem gaussian_scalar_poincare_smooth {freq : ℝ} (hf : 0 < freq)
    (f : ℝ → ℝ) (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (2*freq)*((∫ z : ℝ, verticalMode freq z^2*f z^2) -
      (∫ z : ℝ, verticalMode freq z^2*f z)^2) ≤
        ∫ z : ℝ, verticalMode freq z^2*(deriv f z)^2 := by
  let F : Space 1 → ℝ := fun x => f (gaussianLineEquiv x)
  have hF : IsTestFunction F := ⟨hs.comp gaussianLineEquiv.contDiff,
    hc.comp_homeomorph gaussianLineEquiv.toHomeomorph⟩
  let _ := isProbabilityMeasure_potentialMeasure (gaussian_weight_integrable hf)
  have h := gaussian_poincare_test hf F hF.1 hF.2
  rw [variance_eq_integral_sq_sub_sq _ (hF.integrable _) (hF.integrable_sq _)] at h
  change (2*freq)*((∫ x : Space 1, f (gaussianLineEquiv x)^2 ∂_) -
    (∫ x : Space 1, f (gaussianLineEquiv x) ∂_)^2) ≤
    (∫ x : Space 1, ‖gradient F x‖^2 ∂_) at h
  simp_rw [show ∀ x, ‖gradient F x‖^2 = (deriv f (gaussianLineEquiv x))^2 from
    gaussianLine_gradient_sq (hs.differentiable (by simp))] at h
  rw [gaussianLine_expectation hf (fun z => f z^2),gaussianLine_expectation hf f,
    gaussianLine_expectation hf (fun z => deriv f z^2)] at h
  exact h

end ContinuumCoulomb

end

end OAI
