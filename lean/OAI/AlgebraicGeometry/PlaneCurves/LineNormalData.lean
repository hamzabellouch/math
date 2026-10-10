import OAI.AlgebraicGeometry.PlaneCurves.MovingLines
import OAI.AlgebraicGeometry.PlaneCurves.SquareNormal

namespace OAI

/-!
# Nested derivatives and normal data for moving lines
-/

section

/-! The actual outer polynomial derivative is the Y partial derivative under
our proved two-variable coordinate-ring isomorphism. -/
noncomputable section
namespace Nagata.Workers.W14
open Nagata.W18

 theorem pderiv_one_innerPolynomial {K : Type*} [CommRing K] (P : Polynomial K) :
    MvPolynomial.pderiv (1 : Fin 2)
      (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (0 : Fin 2)) P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial n a =>
    simp [Polynomial.eval₂_monomial]

 theorem pderiv_one_nestedToBivariate {K : Type*} [CommRing K]
    (H : Polynomial (Polynomial K)) :
    MvPolynomial.pderiv (1 : Fin 2) (nestedToBivariate H) =
      nestedToBivariate H.derivative := by
  induction H using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial n a =>
    simp [nestedToBivariate, Polynomial.eval₂_monomial, Polynomial.derivative_monomial,
      pderiv_one_innerPolynomial]
    ring

 theorem planePolynomialEval_nestedToBivariate
    (H : Polynomial (Polynomial ℂ)) (p : ℂ × ℂ) :
    Nagata.Workers.W28.planePolynomialEval (nestedToBivariate H) p =
      Nagata.W06.LineArrangement.planeEval H p.1 p.2 := by
  unfold Nagata.Workers.W28.planePolynomialEval
  rw [← Nagata.W18.nestedEvaluation_eq_polynomialEvaluation]
  change (Polynomial.evalRingHom p.1) (H.eval (Polynomial.C p.2)) =
    H.eval₂ (Polynomial.evalRingHom p.1) p.2
  simpa using
    (Polynomial.eval₂_at_apply (p := H) (Polynomial.evalRingHom p.1) (Polynomial.C p.2)).symm

 theorem planePolynomialEval_pderiv_one_nestedToBivariate
    (H : Polynomial (Polynomial ℂ)) (p : ℂ × ℂ) :
    Nagata.Workers.W28.planePolynomialEval
      (MvPolynomial.pderiv 1 (nestedToBivariate H)) p =
      Nagata.W06.LineArrangement.planeEval H.derivative p.1 p.2 := by
  rw [pderiv_one_nestedToBivariate, planePolynomialEval_nestedToBivariate]

end Nagata.Workers.W14

end
end

section

/-! All geometric inputs to selected-line specialization, certified at the
actual k²+n marked points. -/
noncomputable section
namespace Nagata.Workers.W14
open Nagata.W06.LineArrangement Nagata.Workers.W28

/-- The component containing an ordered mark; all additional marks are on zero. -/
def orderedLineIndex (k n : ℕ) (hk : 0 < k) (i : Fin (k*k+n)) : Fin k :=
  Sum.elim (fun p : Fin k × Fin k => p.1) (fun _ : Fin n => ⟨0,hk⟩)
    ((configurationIndexEquiv k n).symm i)

def orderedLineScalar (k n : ℕ) (hk : 0 < k) (i : Fin (k*k+n)) : ℂ :=
  ((orderedLineIndex k n hk i).val : ℂ)

theorem orderedAffinePoint_graph (k n : ℕ) (hk : 0 < k) (i : Fin (k*k+n)) :
    orderedAffinePoint k n i = ((orderedAffinePoint k n i).1,
      (orderedLineScalar k n hk i)^2 - orderedLineScalar k n hk i *
        (orderedAffinePoint k n i).1) := by
  unfold orderedAffinePoint orderedLineScalar orderedLineIndex
  cases (configurationIndexEquiv k n).symm i with
  | inl p => rfl
  | inr t => simp [mixedPoint, extraPoint]

theorem orderedLine_graph_injective (k n : ℕ) (hk : 0 < k) :
    Function.Injective (fun i : Fin (k*k+n) => ((orderedAffinePoint k n i).1,
      (orderedLineScalar k n hk i)^2 - orderedLineScalar k n hk i *
        (orderedAffinePoint k n i).1)) := by
  simpa only [← orderedAffinePoint_graph] using orderedAffinePoint_injective k n

theorem orderedLine_restriction_zero (k n : ℕ) (hk : 0 < k) (i : Fin (k*k+n)) :
    Nagata.W04.ReducibleSquare.lineRestriction (orderedLineScalar k n hk i)
      (Nagata.Workers.W24.homogeneousLineUnion ℂ k) = 0 :=
  Nagata.Workers.W24.lineRestriction_union_zero k (orderedLineIndex k n hk i)

theorem lineMark_actual_partial (k n : ℕ) (i : Fin (k*k+n)) :
    planePolynomialEval (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom 2
      (Nagata.Workers.W24.homogeneousLineUnion ℂ k))) (orderedAffinePoint k n i) =
      lineMarkYDerivative k n i := by
  rw [Nagata.Workers.W24.directChart_union_eq_nestedToBivariate,
    planePolynomialEval_pderiv_one_nestedToBivariate]
  rfl

theorem markedPoint_actual_partial_ne_zero (k : ℕ) (i s : Fin k) :
    planePolynomialEval (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom 2
      (Nagata.Workers.W24.homogeneousLineUnion ℂ k))) (markedPoint ℂ k i s) ≠ 0 := by
  rw [Nagata.Workers.W24.directChart_union_eq_nestedToBivariate,
    planePolynomialEval_pderiv_one_nestedToBivariate]
  exact partialY_lineUnion_at_mark k i s

theorem extraPoint_actual_partial_ne_zero (k : ℕ) (hk : 0 < k) (t : ℕ) :
    planePolynomialEval (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom 2
      (Nagata.Workers.W24.homogeneousLineUnion ℂ k))) (extraPoint ℂ k t) ≠ 0 := by
  rw [Nagata.Workers.W24.directChart_union_eq_nestedToBivariate,
    planePolynomialEval_pderiv_one_nestedToBivariate]
  exact (extraPoint_nonsingular_certificate k hk t).2

theorem orderedLine_partial_ne_zero (k n : ℕ) (hk : 0 < k) (i : Fin (k*k+n)) :
    planePolynomialEval (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom 2
      (Nagata.Workers.W24.homogeneousLineUnion ℂ k)))
      ((orderedAffinePoint k n i).1, (orderedLineScalar k n hk i)^2 -
        orderedLineScalar k n hk i * (orderedAffinePoint k n i).1) ≠ 0 := by
  rw [← orderedAffinePoint_graph, lineMark_actual_partial]
  exact lineMarkYDerivative_ne_zero k n hk i

theorem lineMark_actual_gradient_velocity (k n : ℕ) (hk : 0 < k)
    (displacement : Fin (k*k+n) → ℂ) (i : Fin (k*k+n)) :
    polynomialGradient (Nagata.W27.directChartHom 2
      (Nagata.Workers.W24.homogeneousLineUnion ℂ k)) (orderedAffinePoint k n i)
      (lineMarkVelocity k n displacement i) = displacement i := by
  change _ * 0 + _ * (displacement i / lineMarkYDerivative k n i) = displacement i
  rw [mul_zero, zero_add, lineMark_actual_partial]
  exact mul_div_cancel₀ _ (lineMarkYDerivative_ne_zero k n hk i)

end Nagata.Workers.W14

end
end

end OAI
