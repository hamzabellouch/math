import OAI.Geometry.SurfaceImmersion.Geometry.RealQuadraticVariation
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialDiagonalVariations

namespace OAI

/-! Exact algebra of the real second variation, including its unused
third direction slot. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma second_diagonal_eq_pair (e : Expression) {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (z : Base × ℝ) :
    (e.variations 1).eval (diagonalFamily G H) z =
      (e.variations 1).eval ![G,H,H,0] z := by
  have hd : DegreeIn 2 (e.variations 1) 0 := by simpa using e.variations_degree 1 2
  have hh := hd.eval_scaleSlot (diagonalFamily_smooth hG hH) 0 z
  have hf : scaleSlot (diagonalFamily G H) 2 0 = ![G,H,H,0] := by
    funext i p
    fin_cases i
    · rfl
    · rfl
    · rfl
    · simp [scaleSlot]
  rw [hf, pow_zero, one_mul] at hh
  exact hh.symm

lemma real_second_variation_add_left (e : Expression) (G : Base → Space)
    {H K : Base → Space} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (J : Base → Space) (z : Base × ℝ) :
    (e.variations 1).eval ![G,(fun x => H x + K x),J,0] z =
      (e.variations 1).eval ![G,H,J,0] z + (e.variations 1).eval ![G,K,J,0] z := by
  have hj : (fun w a p => (jet (fun x => H x + K x) w a p : ℂ)) =
      (fun w a p => (jet H w a p : ℂ)) + (fun w a p => (jet K w a p : ℂ)) := by
    funext w a p
    simp only [jet_add hH hK, Complex.ofReal_add, Pi.add_apply]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, ← quadraticComplex_real_fields, ← quadraticComplex_real_fields,
    ← quadraticComplex_real_fields, hj, quadraticComplex_add_left]

lemma real_second_variation_add_right (e : Expression) (G : Base → Space)
    (J : Base → Space) {H K : Base → Space} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (z : Base × ℝ) :
    (e.variations 1).eval ![G,J,(fun x => H x + K x),0] z =
      (e.variations 1).eval ![G,J,H,0] z + (e.variations 1).eval ![G,J,K,0] z := by
  have hj : (fun w a p => (jet (fun x => H x + K x) w a p : ℂ)) =
      (fun w a p => (jet H w a p : ℂ)) + (fun w a p => (jet K w a p : ℂ)) := by
    funext w a p
    simp only [jet_add hH hK, Complex.ofReal_add, Pi.add_apply]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, ← quadraticComplex_real_fields, ← quadraticComplex_real_fields,
    ← quadraticComplex_real_fields, hj, quadraticComplex_add_right]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
