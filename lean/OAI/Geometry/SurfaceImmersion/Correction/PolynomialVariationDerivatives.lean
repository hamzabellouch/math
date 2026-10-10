import OAI.Geometry.SurfaceImmersion.Correction.PolynomialVariationBounds

namespace OAI

/-! The second and third mixed polynomials differentiate the preceding actual
variation; these are not independent formal symbols. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma eval_differentiate_ofExpression (e : Expression) (j : Fin 3)
    (G : Fin 4 → Base → Space) (z : Base × ℝ) :
    ((ofExpression e).differentiate j).eval G z = e.variation (G 0) (G j.succ) z := by
  induction e with
  | coeff c => exact differentiate_coeff_eval c j G z
  | atom w a e ih =>
    simp only [ofExpression, differentiate, ↓reduceIte, eval, ofExpression_eval,
      Expression.variation, ih]
  | add e f ihe ihf => simp only [ofExpression, differentiate, eval, Expression.variation, ihe, ihf]

namespace Expression

theorem second_variation_hasDerivAt {O : Set LowJet} (hO : IsOpen O)
    {e : Expression} (he : e.SmoothCoeffs O) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (z : Base × ℝ) (hQ : lowJet (G 0) z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => e.variation (fun p => G 0 p + s • G 2 p) (G 1) z)
      ((e.variations 1).eval G z) 0 := by
  have hd := differentiate_hasDerivAt hO hG
    (e.variations_smoothCoeffs hO he 0) 1 z hQ
  simp only [show (1 : Fin 3).succ = (2 : Fin 4) by decide] at hd
  have heq : (fun s : ℝ => (e.variations 0).eval (varyBase G (G 2) s) z) =
      (fun s : ℝ => e.variation (fun p => G 0 p + s • G 2 p) (G 1) z) := by
    funext s
    change ((ofExpression e).differentiate 0).eval (varyBase G (G 2) s) z = _
    rw [eval_differentiate_ofExpression, varyBase_base, Fin.succ_zero_eq_one,
      varyBase_other _ _ _ (by decide : (1 : Fin 4) ≠ 0)]
  rw [heq] at hd
  exact hd

theorem third_variation_hasDerivAt {O : Set LowJet} (hO : IsOpen O)
    {e : Expression} (he : e.SmoothCoeffs O) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (z : Base × ℝ) (hQ : lowJet (G 0) z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => (e.variations 1).eval (varyBase G (G 3) s) z)
      ((e.variations 2).eval G z) 0 := by
  exact differentiate_hasDerivAt hO hG (e.variations_smoothCoeffs hO he 1) 2 z hQ

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
