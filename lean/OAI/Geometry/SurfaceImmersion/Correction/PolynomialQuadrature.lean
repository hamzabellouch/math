import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanPair
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateQuadraticExpansion

namespace OAI

/-! The polynomial Hessian has the same two-quadrature zero-mode identity
as the metric Hessian. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

lemma complexJet_const_smul {H : Base → Fin 4 → ℂ}
    (hH : ContDiff ℝ ∞ H) (c : ℂ) :
    complexJet (fun p => c • H p) = c • complexJet H := by
  funext w a p
  exact congrFun (directional_clm (c • ContinuousLinearMap.id ℝ ℂ)
    (contDiff_pi.mp hH a) (w.map coordinateVector)) p

lemma starDirectionJets_const_smul (J : DirectionJets) (c : ℂ) :
    starDirectionJets (c • J) = star c • starDirectionJets J := by
  funext w a p
  simp only [starDirectionJets,Pi.smul_apply,smul_eq_mul,star_mul']

lemma half_second_variation_quadrature (e : Expression) (G : Base → Space)
    {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (z : Base × ℝ) :
    (1 / 2 : ℝ) * (e.variations 1).eval ![G,realField H,realField H,0] z +
      (1 / 2 : ℝ) * (e.variations 1).eval
        ![G,realField (fun p => Complex.I • H p),realField (fun p => Complex.I • H p),0] z =
      2 * (quadraticComplex e G (complexJet H)
        (starDirectionJets (complexJet H)) z).re / 4 := by
  have hI : ContDiff ℝ ∞ (fun p => Complex.I • H p) :=
    (contDiff_const (c := Complex.I)).smul hH
  rw [half_second_variation_real e G hH,half_second_variation_real e G hI,
    complexJet_const_smul hH,starDirectionJets_const_smul,
    quadraticComplex_smul_left,quadraticComplex_smul_right,
    quadraticComplex_smul_left,quadraticComplex_smul_right]
  simp only [Complex.star_def,Complex.conj_I]
  simp only [← mul_assoc,Complex.I_mul_I,neg_mul,mul_neg,neg_neg,one_mul,
    Complex.neg_re]
  ring

namespace Perturbation

lemma polynomial_quadrature_sum {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {φ : Base → ℝ} {H : Base → Fin 4 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H) (τ t : ℝ) (x : Base) :
    (∑ l, ε^(l.val+1) * ((1/2 : ℝ) * ((P l).variations 1).eval
      ![G,realField (fun p => phase τ φ p • H p),realField (fun p => phase τ φ p • H p),0] (x,t))) +
    (∑ l, ε^(l.val+1) * ((1/2 : ℝ) * ((P l).variations 1).eval
      ![G,realField (fun p => phase τ φ p • (Complex.I • H p)),
        realField (fun p => phase τ φ p • (Complex.I • H p)),0] (x,t))) =
    2 * quadraticMeanCoefficient P ε G φ H τ t x := by
  rw [← quadraticMeanPair_self P ε G hφ hH]
  unfold quadraticMeanPair
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have he : (fun p => phase τ φ p • (Complex.I • H p)) =
      fun p => Complex.I • (phase τ φ p • H p) := by
    funext p
    exact smul_comm _ _ _
  rw [he,← mul_add]
  rw [half_second_variation_quadrature (P l) G
    (H := fun p => phase τ φ p • H p) ((phase_smooth hφ τ).smul hH)]
  ring

lemma real_mode_coordinates (τ : ℝ) (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) :
    realField (fun p => phase τ φ p • H p) =
      QuadraticMean.displacement τ (coordinatePhase φ) (coordinateAmplitude H) ∘
        planeCoordinateIsometry := by
  funext x a
  simp only [realField,QuadraticMean.displacement,QuadraticMean.realMode,
    QuadraticMean.realPart,Function.comp_apply,coordinatePhase,coordinateAmplitude,
    planeCoordinateIsometry.symm_apply_apply,Pi.smul_apply,smul_eq_mul,coordinate_phase_value]

theorem coordinate_polynomial_quadrature {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} {H : Base → Fin 4 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H) (τ t : ℝ) :
    coordinateQuadraticPolynomial P ε G
        (QuadraticMean.displacement τ (coordinatePhase φ) (coordinateAmplitude H)) t +
      coordinateQuadraticPolynomial P ε G
        (QuadraticMean.displacement τ (coordinatePhase φ)
          (coordinateAmplitude (fun p => Complex.I • H p))) t =
      (2 : ℝ) • (fun y k => quadraticMeanCoefficient (P k) ε G φ H τ t
        (planeCoordinateIsometry.symm y)) := by
  ext y k
  have hh := polynomial_quadrature_sum (P k) ε G hφ hH τ t
    (planeCoordinateIsometry.symm y)
  simp only [real_mode_coordinates,coordinateQuadraticPolynomial,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul] at hh ⊢
  exact hh

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
