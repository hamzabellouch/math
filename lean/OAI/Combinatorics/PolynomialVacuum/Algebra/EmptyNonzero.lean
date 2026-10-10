import OAI.Combinatorics.PolynomialVacuum.Algebra.AllSizeInduction
import OAI.Combinatorics.PolynomialVacuum.Algebra.FiniteTranslation

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

 

theorem polynomialVacuum_empty_ne_zero (N : ℕ) :
    polynomialVacuum N (fun _ => Spin.zero)≠0 := by
  induction N with
  | zero => simp [polynomialVacuum,vacuumZero]
  | succ n ih =>
    intro hz
    have hp : (∏ j : Fin n, (X j : MvPolynomial (Fin n) ℂ)) *
        polynomialVacuum n (fun _ => Spin.zero)=0 := by
      apply MvPolynomial.funext
      intro Y
      have he := finite_lastZero (polynomialVacuum (n+1)) (polynomialVacuum n)
        ((polynomialVacuum_at (n+1)).lastZero n rfl)
        (fun _ => Spin.zero) (Fin.snoc Y 0) rfl (by simp)
      rw [hz,map_zero] at he
      simpa [Function.comp_def] using he.symm
    have hprod : (∏ j : Fin n, (X j : MvPolynomial (Fin n) ℂ))≠0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => X_ne_zero j)
    exact ih ((mul_eq_zero.mp hp).resolve_left hprod)

end PolynomialVacuumAlgebra

end OAI
