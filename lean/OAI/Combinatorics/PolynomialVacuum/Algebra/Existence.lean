import OAI.Combinatorics.PolynomialVacuum.Algebra.FiniteTranslation

namespace OAI

namespace PolynomialVacuumAlgebra

 

theorem polynomial_vacuum_is_vacuum : IsPolynomialVacuum polynomialVacuum := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s; rfl
  · intro s; rfl
  · intro N s hs; exact (polynomialVacuum_at N).regular.charge s hs
  · intro N s; exact (polynomialVacuum_at N).regular.homogeneous s
  · intro N s i; exact (polynomialVacuum_at N).regular.degree s i
  · intro N s i hi; exact (polynomialVacuum_at N).regular.plus s i hi
  · intro N s i X hi hX
    exact finite_minus_zero _ (polynomialVacuum_at N).regular.minus s i X hi hX
  · intro n i s X
    exact finite_exchange _ (polynomialVacuum_at (n+2)).regular.exchange i s X
  · intro n s X
    exact finite_cyclic _ ((polynomialVacuum_at (n+1)).cyclic n rfl) s X
  · intro n i s X hX
    exact finite_cup _ _ ((polynomialVacuum_at (n+2)).cups n rfl) i s X hX
  · intro n s X hs hX
    exact finite_lastZero _ _ ((polynomialVacuum_at (n+1)).lastZero n rfl) s X hs hX

theorem polynomial_vacuum_exists : PolynomialVacuumExists :=
  ⟨polynomialVacuum, polynomial_vacuum_is_vacuum⟩

end PolynomialVacuumAlgebra

end OAI
