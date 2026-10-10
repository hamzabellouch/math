import OAI.Geometry.SurfaceImmersion.Correction.PolynomialAffineDerivative
import OAI.Geometry.SurfaceImmersion.Geometry.ParameterTaylorRemainder
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialVariationBounds

namespace OAI

/-! The first three actual parameter derivatives of a polynomial along a
map variation are its mixed variations with all directions equal. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ParameterTaylor SmoothPeriodicCalculus

def diagonalFamily (G H : Base → Space) : Fin 4 → Base → Space :=
  Fin.cases G (fun _ => H)

lemma diagonalFamily_smooth {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) :
    ∀ i, ContDiff ℝ ∞ (diagonalFamily G H i) := by
  intro i
  refine Fin.cases hG (fun _ => hH) i

lemma diagonalFamily_succ (G H : Base → Space) (j : Fin 3) : diagonalFamily G H j.succ = H := rfl

lemma diagonal_angleDerivative {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {e : MixedExpression} (he : e.SmoothCoeffs Set.univ) (j : Fin 3) (θ : ℝ) (z : Base × ℝ) :
    angleDerivative (fun x : Base × ℝ => e.eval (varyBase (diagonalFamily G H) H x.2) (x.1, θ)) z =
      (e.differentiate j).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ) := by
  have hs := eval_varyBase_joint_smooth (diagonalFamily_smooth hG hH) hH he θ
  have hd := differentiate_hasDerivAt_at isOpen_univ (diagonalFamily_smooth hG hH) he j z.2
    (z.1, θ) (Set.mem_univ _)
  simp only [diagonalFamily_succ] at hd
  exact (angle_hasDerivAt hs z.1 z.2).unique hd

namespace Expression

def affinePolynomial (e : Expression) (G H : Base → Space) (θ : ℝ) : Base × ℝ → ℝ :=
  fun z => (ofExpression e).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ)

lemma affinePolynomial_smooth {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    ContDiff ℝ ∞ (e.affinePolynomial G H θ) :=
  eval_varyBase_joint_smooth (diagonalFamily_smooth hG hH) hH (smoothCoeffs_ofExpression he) θ

lemma affinePolynomial_first {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    parameterJet 1 (e.affinePolynomial G H θ) =
      fun z => (e.variations 0).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ) := by
  funext z
  exact diagonal_angleDerivative hG hH (smoothCoeffs_ofExpression he) 0 θ z

lemma affinePolynomial_second {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    parameterJet 2 (e.affinePolynomial G H θ) =
      fun z => (e.variations 1).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ) := by
  change angleDerivative (parameterJet 1 (e.affinePolynomial G H θ)) = _
  rw [affinePolynomial_first he hG hH]
  funext z
  exact diagonal_angleDerivative hG hH (e.variations_smoothCoeffs isOpen_univ he 0) 1 θ z

lemma affinePolynomial_third {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    parameterJet 3 (e.affinePolynomial G H θ) =
      fun z => (e.variations 2).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ) := by
  change angleDerivative (parameterJet 2 (e.affinePolynomial G H θ)) = _
  rw [affinePolynomial_second he hG hH]
  funext z
  exact diagonal_angleDerivative hG hH (e.variations_smoothCoeffs isOpen_univ he 1) 2 θ z

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
