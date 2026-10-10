import OAI.RepresentationTheory.RestrictedTilting.RationalMatrices
import OAI.RepresentationTheory.RestrictedTilting.LaurentPolynomialSeparation

namespace OAI

namespace FiberFunctorProof
open scoped BigOperators
section
variable {k K ι : Type*} [Field k] [Infinite k] [Field K] [Algebra k K]
  [Fintype ι] [DecidableEq ι]

omit [Infinite k] [Fintype ι] [DecidableEq ι] in
lemma polynomialMatrixEval_base (P : Matrix ι ι (Polynomial k)) (t : k) :
    polynomialMatrixEval P (algebraMap k K t) =
      (polynomialMatrixEval P t).map (algebraMap k K) :=
  (polynomialMatrixEval_map P (Algebra.ofId k K) t).symm

omit [DecidableEq ι] in
lemma polynomial_intertwiner_extension (P B : Matrix ι ι (Polynomial k))
    (C : Matrix ι ι K) (z : K)
    (h : ∀ t : k, C * polynomialMatrixEval B (algebraMap k K t) =
      polynomialMatrixEval P (algebraMap k K t * z) * C) :
    ∀ t : K, C * polynomialMatrixEval B t = polynomialMatrixEval P (t*z) * C := by
  let CP : Matrix ι ι (Polynomial K) := C.map Polynomial.C
  let BP := polynomialMatrixEval B (Polynomial.X : Polynomial K)
  let PP := polynomialMatrixEval P (Polynomial.X * Polynomial.C z)
  let ev (t : K) : Polynomial K →ₐ[k] K := (Polynomial.aeval t).restrictScalars k
  have heC (t : K) : CP.map (ev t) = C := by
    apply Matrix.ext
    intro i j
    exact Polynomial.aeval_C t (C i j)
  have heB (t : K) : BP.map (ev t) = polynomialMatrixEval B t := by
    rw [polynomialMatrixEval_map]
    congr 1
    exact Polynomial.aeval_X t
  have heP (t : K) : PP.map (ev t) = polynomialMatrixEval P (t*z) := by
    rw [polynomialMatrixEval_map]
    congr 1
    change Polynomial.aeval t (Polynomial.X * Polynomial.C z) = t*z
    rw [map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    rfl
  have hid : CP * BP = PP * CP := by
    apply Matrix.ext
    intro i j
    apply polynomial_eq_of_base_evals (k := k)
    intro t
    have hM : (CP * BP).map (ev (algebraMap k K t)) =
        (PP*CP).map (ev (algebraMap k K t)) := by
      rw [Matrix.map_mul, Matrix.map_mul, heC, heB, heP]
      exact h t
    exact congrArg (fun A : Matrix ι ι K => A i j) hM
  intro t
  have he := congrArg (fun A : Matrix ι ι (Polynomial K) => A.map (ev t)) hid
  simpa only [Matrix.map_mul, heC, heB, heP] using he
end
end FiberFunctorProof

end OAI
