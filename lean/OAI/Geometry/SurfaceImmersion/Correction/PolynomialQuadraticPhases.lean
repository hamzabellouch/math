import OAI.Geometry.SurfaceImmersion.Geometry.RealQuadraticVariation

namespace OAI

/-! Exact zero- and double-phase terms of the polynomial Hessian. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

def pairPhases (φ ψ : Base → ℝ) : Fin 3 → Base → ℝ := ![φ, ψ, 0]
def pairDirections (H K : Base → Fin 4 → ℂ) : DirectionFields := ![H, K, 0]
def starField (H : Base → Fin 4 → ℂ) : Base → Fin 4 → ℂ := fun p a => star (H p a)

lemma starField_smooth {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (starField H) := by
  apply contDiff_pi.mpr
  intro a
  exact Complex.conjCLE.contDiff.comp (contDiff_pi.mp hH a)

lemma complexJet_starField {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) :
    complexJet (starField H) = starDirectionJets (complexJet H) := by
  funext w a p
  exact congrFun (directional_clm Complex.conjCLE.toContinuousLinearMap
    (contDiff_pi.mp hH a) (w.map coordinateVector)) p

lemma phase_star (τ : ℝ) (φ : Base → ℝ) (p : Base) :
    star (phase τ φ p) = phase τ (fun q => -φ q) p := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul, map_div₀,
    Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  congr 1
  ring

lemma starField_phase (τ : ℝ) (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) :
    starField (fun p => phase τ φ p • H p) =
      fun p => phase τ (fun q => -φ q) p • starField H p := by
  funext p a
  simp only [starField, Pi.smul_apply, smul_eq_mul, star_mul', phase_star]

lemma pair_oscillatoryData (G : Base → Space) (φ ψ : Base → ℝ)
    (H K : Base → Fin 4 → ℂ) (τ : ℝ) :
    oscillatoryData G (pairPhases φ ψ) (pairDirections H K) τ =
      pairJetData G (complexJet (fun p => phase τ φ p • H p))
        (complexJet (fun p => phase τ ψ p • K p)) := by
  funext i w a p
  fin_cases i
  · rfl
  · rfl
  · rfl
  · change iteratedDirectional (w.map coordinateVector)
      (fun p => phase τ (fun _ => 0) p * (0 : ℂ)) p = 0
    simp only [mul_zero, iteratedDirectional_zero]

lemma quadraticComplex_phase_factor (e : Expression) (G : Base → Space) (φ ψ : Base → ℝ)
    (H K : Base → Fin 4 → ℂ) (τ : ℝ) (z : Base × ℝ) :
    quadraticComplex e G (complexJet (fun p => phase τ φ p • H p))
        (complexJet (fun p => phase τ ψ p • K p)) z =
      (phase τ φ z.1 * phase τ ψ z.1) *
        conjugatedVariation e G (pairPhases φ ψ) (pairDirections H K) τ 1 z := by
  have he : phaseProduct (pairPhases φ ψ) τ 1 z.1 = phase τ φ z.1 * phase τ ψ z.1 := by
    simp [phaseProduct, pairPhases]
  rw [quadraticComplex, ← pair_oscillatoryData, conjugatedVariation, ← he, ← mul_assoc,
    mul_inv_cancel₀ (phaseProduct_ne_zero _ _ _ _), one_mul]

/-- The coefficient of the zero phase is precisely the mixed phase Hessian;
all remaining self-interaction has phase twice the original phase. -/
theorem half_second_variation_oscillation (e : Expression) (G : Base → Space)
    {φ : Base → ℝ} {H : Base → Fin 4 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H) (τ : ℝ) (z : Base × ℝ) :
    (1 / 2 : ℝ) * (e.variations 1).eval
      ![G, realField (fun p => phase τ φ p • H p), realField (fun p => phase τ φ p • H p), 0] z =
      ((phase τ φ z.1 ^ 2) *
        conjugatedVariation e G (pairPhases φ φ) (pairDirections H H) τ 1 z).re / 4 +
      (conjugatedVariation e G (pairPhases φ (fun p => -φ p))
        (pairDirections H (starField H)) τ 1 z).re / 4 := by
  have hosc : ContDiff ℝ ∞ (fun p => phase τ φ p • H p) := (phase_smooth hφ τ).smul hH
  rw [half_second_variation_real e G hosc]
  have he : starDirectionJets (complexJet (fun p => phase τ φ p • H p)) =
      complexJet (fun p => phase τ (fun q => -φ q) p • starField H p) := by
    rw [← complexJet_starField hosc, starField_phase]
  rw [he, quadraticComplex_phase_factor, quadraticComplex_phase_factor, phase_neg_inv,
    mul_inv_cancel₀ (show phase τ φ z.1 ≠ 0 from Complex.exp_ne_zero _), one_mul, ← pow_two, add_div]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
