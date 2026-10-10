import OAI.RepresentationTheory.RestrictedTilting.AssociatedNumerator
import OAI.RepresentationTheory.RestrictedTilting.XChartLineEval
import OAI.RepresentationTheory.RestrictedTilting.ClearedPolynomial

namespace OAI

namespace FiberFunctorProof
open scoped BigOperators
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
local notation "N" => associatedSectionsSubmodule k ι ρ
local notation "W" => associatedNumeratorLinear k ι ρ P hP d hd

lemma associatedNumerator_line_eval (a : kˣ) (f : N) (i : ι) :
    (linePolynomial k (W f i)).eval (a : k) = (a : k)^d *
      regularVectorEvaluation k ι (diagonalTorus k a) f.val i := by
  rw [linePolynomial_eval]
  change planeLineEval k a (W f i) = _
  have h := congrArg (chartLineEval k a) (associatedNumeratorLinear_spec k ι ρ P hP d hd f i)
  rw [chartLineEval_algebraMap, map_mul, map_pow, chartLineEval_coordinate] at h
  simpa only [ite_true, congrFun (associatedXChart_line k ι ρ a f) i] using h

 

lemma associatedNumerator_line_unipotent (t : k) (f : N) (i : ι) :
    Polynomial.X^(2*d) * linePolynomial k
      (W (associatedSectionsRepresentation k ι ρ (unipotent k t) f) i) =
      ∑ j, clearedLineAction k (P i j) t d * linePolynomial k (W f j) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.finite_singleton (0 : k)).infinite_compl.mono
  intro a ha
  have ha0 : a ≠ 0 := ha
  let u : kˣ := Units.mk0 a ha0
  change Polynomial.eval (u : k) _ = Polynomial.eval (u : k) _
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_finsetSum]
  rw [associatedNumerator_line_eval k ι ρ P hP d hd,
    associatedSections_line_unipotent k ι ρ u t f]
  simp_rw [clearedLineAction_eval k _ t (u : k) d (hd i _) u.ne_zero,
    associatedNumerator_line_eval k ι ρ P hP d hd u f]
  rw [← LinearMap.toMatrix'_mulVec, ← hP]
  simp only [polynomialMatrixEval, Matrix.mulVec, dotProduct,
    Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
end FiberFunctorProof

end OAI
