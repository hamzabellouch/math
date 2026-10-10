import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanCoefficient
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteQuadraticVariation

namespace OAI

/-! Bilinear form underlying the polynomial zero-phase correction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

lemma starDirectionJets_add (J K : DirectionJets) :
    starDirectionJets (J + K) = starDirectionJets J + starDirectionJets K := by
  funext w a p
  exact star_add _ _

lemma quadraticComplex_opposite_phases (e : Expression) (G : Base → Space)
    {φ : Base → ℝ} {H K : Base → Fin 4 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hK : ContDiff ℝ ∞ K) (τ : ℝ) (z : Base × ℝ) :
    quadraticComplex e G (complexJet (fun p => phase τ φ p • H p))
      (starDirectionJets (complexJet (fun p => phase τ φ p • K p))) z =
      conjugatedVariation e G (pairPhases φ (fun p => -φ p)) (pairDirections H (starField K)) τ 1 z := by
  have hsm : ContDiff ℝ ∞ (fun p => phase τ φ p • K p) := (phase_smooth hφ τ).smul hK
  rw [← complexJet_starField hsm, starField_phase, quadraticComplex_phase_factor,
    phase_neg_inv, mul_inv_cancel₀ (show phase τ φ z.1 ≠ 0 from Complex.exp_ne_zero _), one_mul]

namespace Perturbation

def quadraticMeanPair {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : Base → ℝ) (H K : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) : ℝ :=
  ∑ l, ε ^ (l.val + 1) *
    (quadraticComplex (P l) G (complexJet (fun p => phase τ φ p • H p))
      (starDirectionJets (complexJet (fun p => phase τ φ p • K p))) (p, t)).re / 4

lemma quadraticMeanPair_add_left {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H K : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (L : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ (fun x => H x + K x) L τ t p =
      quadraticMeanPair P ε G φ H L τ t p + quadraticMeanPair P ε G φ K L τ t p := by
  have he : (fun x => phase τ φ x • (H x + K x)) =
      fun x => phase τ φ x • H x + phase τ φ x • K x := by funext x; exact smul_add _ _ _
  simp only [quadraticMeanPair, he, complexJet_add (H := fun p => phase τ φ p • H p) (K := fun p => phase τ φ p • K p)
    ((phase_smooth hφ τ).smul hH)
    ((phase_smooth hφ τ).smul hK), quadraticComplex_add_left, Complex.add_re, mul_add, add_div,
    Finset.sum_add_distrib]

lemma quadraticMeanPair_add_right {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H K : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (L : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ L (fun x => H x + K x) τ t p =
      quadraticMeanPair P ε G φ L H τ t p + quadraticMeanPair P ε G φ L K τ t p := by
  have he : (fun x => phase τ φ x • (H x + K x)) =
      fun x => phase τ φ x • H x + phase τ φ x • K x := by funext x; exact smul_add _ _ _
  simp only [quadraticMeanPair, he, complexJet_add (H := fun p => phase τ φ p • H p) (K := fun p => phase τ φ p • K p)
    ((phase_smooth hφ τ).smul hH)
    ((phase_smooth hφ τ).smul hK), starDirectionJets_add, quadraticComplex_add_right,
    Complex.add_re, mul_add, add_div, Finset.sum_add_distrib]

lemma quadraticMeanPair_self {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) {H : Base → Fin 4 → ℂ}
    (hH : ContDiff ℝ ∞ H) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ H H τ t p = quadraticMeanCoefficient P ε G φ H τ t p := by
  simp only [quadraticMeanPair, quadraticComplex_opposite_phases _ G hφ hH,
    quadraticMeanCoefficient, conjugated, Complex.re_sum, Complex.real_smul,
    Finset.sum_div, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
