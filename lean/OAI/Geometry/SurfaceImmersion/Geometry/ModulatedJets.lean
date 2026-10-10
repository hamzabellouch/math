import OAI.Geometry.SurfaceImmersion.Geometry.JetVariations

namespace OAI

/-! Exact removal of the fast phase from arbitrary ordered directional jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates

def phase (τ : ℝ) (φ : Base → ℝ) (p : Base) : ℂ :=
  Complex.exp (Complex.I / (τ : ℂ) * (φ p : ℂ))

def amplitudeDerivative (τ : ℝ) (φ : Base → ℝ) (v : Base) (Z : Base → ℂ) : Base → ℂ :=
  fun p => fderiv ℝ Z p v + (Complex.I / (τ : ℂ) * (fderiv ℝ φ p v : ℂ)) * Z p

def amplitudeJet (τ : ℝ) (φ : Base → ℝ) : List Base → (Base → ℂ) → Base → ℂ
  | [], Z => Z
  | v :: w, Z => amplitudeDerivative τ φ v (amplitudeJet τ φ w Z)

lemma phase_smooth {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ : ℝ) :
    ContDiff ℝ ∞ (phase τ φ) :=
  ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hφ)).cexp)

lemma amplitudeDerivative_smooth {φ : Base → ℝ} {Z : Base → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (τ : ℝ) (v : Base) :
    ContDiff ℝ ∞ (amplitudeDerivative τ φ v Z) := by
  have hdZ := (hZ.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := v))
  have hdφ := (hφ.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := v))
  exact hdZ.add ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hdφ)).mul hZ)

lemma amplitudeJet_smooth {φ : Base → ℝ} {Z : Base → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (τ : ℝ) (w : List Base) :
    ContDiff ℝ ∞ (amplitudeJet τ φ w Z) := by
  induction w with
  | nil => exact hZ
  | cons v w ih => exact amplitudeDerivative_smooth hφ ih τ v

lemma derivative_phase_product {φ : Base → ℝ} {Z : Base → ℂ} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (v : Base) :
    fderiv ℝ (fun q => phase τ φ q * Z q) p v =
      phase τ φ p * amplitudeDerivative τ φ v Z p := by
  have hp := ((Complex.ofRealCLM.hasFDerivAt.comp p hφ.hasFDerivAt).const_mul
    (Complex.I / (τ : ℂ))).cexp
  have h := hp.mul hZ.hasFDerivAt
  have hfun : ((fun x => Complex.exp (Complex.I / (τ : ℂ) *
      (Complex.ofRealCLM ∘ φ) x)) * Z) = (fun q => phase τ φ q * Z q) := rfl
  rw [← hfun, h.fderiv]
  simp only [amplitudeDerivative, phase, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    Function.comp_def]
  ring

/-- Differentiating the oscillation changes its amplitude but preserves the
single phase factor, in every ordered coordinate word. -/
theorem iterated_phase_product {φ : Base → ℝ} {Z : Base → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (τ : ℝ) (w : List Base) :
    iteratedDirectional w (fun p => phase τ φ p * Z p) =
      fun p => phase τ φ p * amplitudeJet τ φ w Z p := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    rw [iteratedDirectional, ih]
    funext p
    exact derivative_phase_product (hφ.differentiable (by simp) p)
      ((amplitudeJet_smooth hφ hZ τ w).differentiable (by simp) p) τ v

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
