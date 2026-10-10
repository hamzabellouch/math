import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTensorPullback

namespace OAI

/-! Positional cutoffs of the actual finite tensor polynomial. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def cutoffTensorPolynomial {n : ℕ} (χ : Base → ℝ)
    (P : Fin 3 → Fin n → Expression) : Fin 3 → Fin n → Expression :=
  fun k r => (Expression.coeff (fun z => χ (lowPosition z.1))).mul (P k r)

lemma cutoffTensorPolynomial_smooth {n : ℕ} {χ : Base → ℝ}
    (hχ : ContDiff ℝ ∞ χ) {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k r, (P k r).SmoothCoeffs univ) (k : Fin 3) (r : Fin n) :
    (cutoffTensorPolynomial χ P k r).SmoothCoeffs univ :=
  Expression.smoothCoeffs_mul
    ((hχ.comp (lowPosition.contDiff.comp contDiff_fst)).contDiffOn) (hP k r)

lemma cutoffTensorPolynomial_eval {n : ℕ} (χ : Base → ℝ)
    (P : Fin 3 → Fin n → Expression) (G : Base → Space) (z t : ℝ) (x : Base) :
    coordinatePolynomialValue (cutoffTensorPolynomial χ P) z G t (planeCoordinateIsometry x) =
      χ x • coordinatePolynomialValue P z G t (planeCoordinateIsometry x) := by
  ext k
  simp only [coordinatePolynomialValue,cutoffTensorPolynomial,Expression.eval_mul,
    Expression.eval,lowPosition_lowJet,LinearIsometryEquiv.symm_apply_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
