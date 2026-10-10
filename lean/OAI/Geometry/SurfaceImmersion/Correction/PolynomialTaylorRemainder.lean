import OAI.Geometry.SurfaceImmersion.Correction.PolynomialDiagonalVariations

namespace OAI

/-! The weighted cubic estimate for the actual higher-jet polynomial map. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open MixedExpression ParameterTaylor SmoothParameterIntegral WeightedEstimates

lemma affinePolynomial_apply (e : Expression) (G H : Base → Space) (θ : ℝ) (z : Base × ℝ) :
    e.affinePolynomial G H θ z = e.eval (fun p => G p + z.2 • H p) (z.1, θ) := by
  rw [affinePolynomial, ofExpression_eval, varyBase_base]
  rfl

def taylorRemainder (e : Expression) (G H : Base → Space) (θ : ℝ) (p : Base) : ℝ :=
  e.eval (fun q => G q + H q) (p, θ) - e.eval G (p, θ) - e.variation G H (p, θ) -
    (1 / 2 : ℝ) * (e.variations 1).eval (diagonalFamily G H) (p, θ)

lemma cubicRemainder_affine {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    cubicRemainder (e.affinePolynomial G H θ) = e.taylorRemainder G H θ := by
  funext p
  unfold cubicRemainder taylorRemainder
  rw [affinePolynomial_first he hG hH, affinePolynomial_second he hG hH]
  simp only [affinePolynomial_apply, one_smul, zero_smul, add_zero, varyBase_zero]
  rw [e.first_variation_eval isOpen_univ he (diagonalFamily_smooth hG hH) (p, θ) (Set.mem_univ _)]
  rfl

theorem taylorRemainder_eq_integral {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) (p : Base) :
    e.taylorRemainder G H θ p =
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ 2 / 2) *
        (e.variations 2).eval (varyBase (diagonalFamily G H) H t) (p, θ) := by
  rw [← cubicRemainder_affine he hG hH θ]
  rw [cubicRemainder_eq_integral (affinePolynomial_smooth he hG hH θ), affinePolynomial_third he hG hH]
  rfl

theorem weighted_taylorRemainder {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ)
    {U : Set Base} (hU : IsOpen U) {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (m : ℕ)
    (hb : ∀ j ≤ m, ∀ p ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j
        (fun z : Base × ℝ => (e.variations 2).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ))
        (p, t)‖ ≤ M) :
    WeightedBound U s m (M / 2) (e.taylorRemainder G H θ) := by
  rw [← cubicRemainder_affine he hG hH θ]
  apply weighted_cubicRemainder (affinePolynomial_smooth he hG hH θ) hU hs hM m
  simpa only [affinePolynomial_third he hG hH] using hb

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
