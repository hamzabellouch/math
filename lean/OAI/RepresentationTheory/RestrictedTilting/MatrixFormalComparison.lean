import OAI.RepresentationTheory.RestrictedTilting.TorusExtension
import OAI.RepresentationTheory.RestrictedTilting.PolynomialIntertwiner
import OAI.RepresentationTheory.RestrictedTilting.IntertwinerDescent

namespace OAI

namespace FiberFunctorProof
universe u v
variable {k : Type u} [Field k] [Infinite k]
variable {K : Type v} [Field K] [Algebra k K]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

 

theorem matrix_formal_comparison
    (ρ : Representation k (SL2 k) (ι → k)) (hρ : IsRational k ρ)
    (P : Matrix ι ι (Polynomial k)) (x : K) (hx : x ≠ 0)
    (C : Matrix ι ι K) (hC : C.det ≠ 0)
    (h : ∀ t : k, C * (LinearMap.toMatrix' (ρ (unipotent k t))).map (algebraMap k K) =
      polynomialMatrixEval P (algebraMap k K t / x^2) * C) :
    ∃ D : Matrix ι ι k, D.det ≠ 0 ∧ ∀ t : k,
      polynomialMatrixEval P t * D = D * LinearMap.toMatrix' (ρ (unipotent k t)) := by
  let B := rationalUnipotentMatrix k ρ hρ
  have hext : ∀ t : K, C * polynomialMatrixEval B t = polynomialMatrixEval P (t*(x^2)⁻¹)*C := by
    apply polynomial_intertwiner_extension P B C ((x^2)⁻¹)
    intro t
    rw [polynomialMatrixEval_base]
    have hB : polynomialMatrixEval B t = LinearMap.toMatrix' (ρ (unipotent k t)) :=
      eval_rationalUnipotentMatrix k ρ hρ t
    rw [hB]
    simpa only [div_eq_mul_inv] using h t
  let xU : Kˣ := Units.mk0 x hx
  let Q := torusMatrixAt ρ hρ xU
  have hQ : Q.det ≠ 0 := torusMatrixAt_det_ne_zero ρ hρ xU
  apply intertwiner_descent (fun t : k => polynomialMatrixEval P t)
    (fun t : k => LinearMap.toMatrix' (ρ (unipotent k t))) (C*Q)
    (by rw [Matrix.det_mul]; exact mul_ne_zero hC hQ)
  intro t
  have hh := hext (x^2 * algebraMap k K t)
  have hp : (x^2 * algebraMap k K t) * (x^2)⁻¹ = algebraMap k K t := by
    field_simp
  rw [hp] at hh
  rw [← polynomialMatrixEval_base, ← Matrix.mul_assoc, ← hh, Matrix.mul_assoc]
  have hQt := torusMatrixAt_unipotent ρ hρ xU t
  change Q * _ = polynomialMatrixEval B (x^2 * algebraMap k K t) * Q at hQt
  rw [← hQt, Matrix.mul_assoc]

end FiberFunctorProof

end OAI
