import OAI.Geometry.SurfaceImmersion.Geometry.ConjugatedVariationBounds

namespace OAI

/-! Scaling each oscillatory amplitude independently. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

lemma amplitudeDerivative_real_smul {Z : Base → ℂ} (hZ : ContDiff ℝ ∞ Z)
    (φ : Base → ℝ) (τ c : ℝ) (v : Base) :
    amplitudeDerivative τ φ v (fun p => c • Z p) =
      fun p => c • amplitudeDerivative τ φ v Z p := by
  funext p
  have hd := congrArg (fun L : Base →L[ℝ] ℂ => L v)
    (((hZ.differentiable (by simp) p).hasFDerivAt.const_smul c).fderiv)
  change fderiv ℝ (fun q => c • Z q) p v = c • fderiv ℝ Z p v at hd
  change fderiv ℝ (fun q => c • Z q) p v + _ = _
  rw [hd]
  simp only [amplitudeDerivative, Complex.real_smul]
  ring

lemma amplitudeJet_real_smul {φ : Base → ℝ} {Z : Base → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (τ c : ℝ) (w : List Base) :
    amplitudeJet τ φ w (fun p => c • Z p) = fun p => c • amplitudeJet τ φ w Z p := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [amplitudeJet, ih]
    exact amplitudeDerivative_real_smul (amplitudeJet_smooth hφ hZ τ w) φ τ c v

def scaleDirections (H : DirectionFields) (c : Fin 3 → ℝ) : DirectionFields :=
  fun j p => c j • H j p

lemma scaleDirections_smooth {H : DirectionFields} (hH : ∀ j, ContDiff ℝ ∞ (H j))
    (c : Fin 3 → ℝ) : ∀ j, ContDiff ℝ ∞ (scaleDirections H c j) :=
  fun j => ContDiff.const_smul (c j) (hH j)

lemma amplitudeData_scale (G : Base → Space) {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) (c : Fin 3 → ℝ) :
    amplitudeData G φ (scaleDirections H c) τ =
      scaleJets (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) := by
  funext i w a p
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (scaleJets_base (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) w a p).symm
  · rw [scaleJets_succ]
    change amplitudeJet τ (φ j) (w.map coordinateVector) (fun q => c j • H j q a) p = _
    rw [amplitudeJet_real_smul (hφ j) (contDiff_pi.mp (hH j) a)]
    rfl

lemma conjugatedVariation_scale (e : Expression) (G : Base → Space)
    {φ : Fin 3 → Base → ℝ} {H : DirectionFields}
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j)) (hH : ∀ j, ContDiff ℝ ∞ (H j))
    (τ : ℝ) (c : Fin 3 → ℝ) (i : Fin 3) (z : Base × ℝ) :
    conjugatedVariation e G φ (scaleDirections H c) τ i z =
      (c 0 * (if 1 ≤ i then c 1 else 1) * (if 2 ≤ i then c 2 else 1)) •
        conjugatedVariation e G φ H τ i z := by
  rw [conjugatedVariation_eq e G hφ (scaleDirections_smooth hH c),
    conjugatedVariation_eq e G hφ hH, amplitudeData_scale G hφ hH τ c]
  have h := evalComplex_scaleJets (fun j => e.variations_degree i j) G
    (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) z
  fin_cases i <;> simpa [Complex.real_smul] using h

lemma scaleDirections_inverse (H : DirectionFields) (C : Fin 3 → ℝ) (hC : ∀ j, C j ≠ 0) :
    scaleDirections (scaleDirections H (fun j => (C j)⁻¹)) C = H := by
  funext j p
  simp only [scaleDirections, smul_smul, mul_inv_cancel₀ (hC j), one_smul]

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
