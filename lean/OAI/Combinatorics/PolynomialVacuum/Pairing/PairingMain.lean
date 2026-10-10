import OAI.Combinatorics.PolynomialVacuum.Separator.Summability
import OAI.Combinatorics.PolynomialVacuum.Pairing.BlockCharge
import OAI.Combinatorics.PolynomialVacuum.Algebra.Existence

namespace OAI

namespace PolynomialVacuumCylinder
open PolynomialVacuumAlgebra

 

theorem physical_separator_pairing : PhysicalSeparatorPairing := by
  refine ⟨polynomialVacuum,AnalyticVacuum.normalizedVacuum,
    polynomial_vacuum_is_vacuum,AnalyticVacuum.actual_analytic_normalization,
    separator_systems_summable,?_⟩
  intro n hn κ hκ
  exact (physical_limit_is_contraction n hn κ).symm.trans
    (physical_limit_equals_separator n hn κ hκ)

end PolynomialVacuumCylinder

end OAI
