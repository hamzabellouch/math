import OAI.Combinatorics.Crossing.PolynomialKernel
import OAI.Combinatorics.Crossing.RankSpecialization
import Mathlib.LinearAlgebra.Basis.Basic

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

def scalarPolynomial (f : W →ₗ[ℝ] ℝ) : PolynomialModule ℝ W →ₗ[ℝ] Polynomial ℝ :=
  equivPolynomial.toLinearMap.comp (PolynomialModule.map ℝ f)

theorem scalarPolynomial_coeff (f : W →ₗ[ℝ] ℝ) (p : PolynomialModule ℝ W) (n : ℕ) :
    (scalarPolynomial f p).coeff n = f (p.coeff n) := rfl

theorem scalarPolynomial_eval (f : W →ₗ[ℝ] ℝ) (p : PolynomialModule ℝ W) (t : ℝ) :
    (scalarPolynomial f p).eval t = f (eval t p) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | single n w =>
    simp [scalarPolynomial, PolynomialModule.map_single, Polynomial.eval_monomial,
      _root_.map_smul, smul_eq_mul, mul_comm]

theorem scalarPolynomial_natDegree_le (f : W →ₗ[ℝ] ℝ) (p : PolynomialModule ℝ W)
    (h : ℕ) (hp : Bounded (h+1) p) : (scalarPolynomial f p).natDegree ≤ h := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [scalarPolynomial_coeff, hp n (by omega), map_zero]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def polynomialColumnMatrix (b : Module.Basis ι ℝ W) (p : κ → PolynomialModule ℝ W) :
    Matrix ι κ (Polynomial ℝ) := fun i j => scalarPolynomial (b.coord i) (p j)

theorem polynomialColumnMatrix_eval
    {W : Type*} [AddCommGroup W] [Module ℝ W] {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℝ W) (p : κ → PolynomialModule ℝ W)
    (t : ℝ) (i : ι) (j : κ) :
    (polynomialColumnMatrix b p i j).eval t = b.repr (eval t (p j)) i :=
  scalarPolynomial_eval (b.coord i) (p j) t

theorem exists_polynomial_minor (b : Module.Basis ι ℝ W) (p : κ → PolynomialModule ℝ W)
    (d : κ → ℕ) (hp : ∀ j, Bounded (d j+1) (p j)) (t : ℝ)
    (hli : LinearIndependent ℝ (fun j => eval t (p j))) :
    ∃ r : κ → ι, Function.Injective r ∧
      let Δ := ((polynomialColumnMatrix b p).submatrix r id).det
      Δ.eval t ≠ 0 ∧ Δ.natDegree ≤ ∑ j, d j := by
  classical
  let A := (polynomialColumnMatrix b p).map (Polynomial.eval t)
  have hA : LinearIndependent ℝ A.col := by
    have hh := hli.map' b.equivFun.toLinearMap (LinearMap.ker_eq_bot.mpr b.equivFun.injective)
    have hcols : A.col = b.equivFun ∘ (fun j => eval t (p j)) := by
      funext j i
      exact polynomialColumnMatrix_eval b p t i j
    rw [hcols]
    exact hh
  obtain ⟨r, hr, hd⟩ := exists_row_minor A hA
  refine ⟨r, hr, ?_, ?_⟩
  · have he := (Polynomial.evalRingHom t).map_det ((polynomialColumnMatrix b p).submatrix r id)
    exact he.trans_ne hd
  · apply natDegree_det_le_column_sum
    intro i j
    exact scalarPolynomial_natDegree_le (b.coord (r i)) (p j) (d j) (hp j)

end Zarankiewicz

end

end OAI
