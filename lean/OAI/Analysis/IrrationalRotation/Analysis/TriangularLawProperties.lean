import OAI.Analysis.IrrationalRotation.Analysis.TriangularLawMass
import OAI.Analysis.IrrationalRotation.Analysis.TriangularSecondMarginal

namespace OAI

namespace Invariant233.ProductModel

theorem triangularLaw_properties (I : Finset ℕ) : TriangularLawProperties I := by
  exact ⟨Sampling.triangularLaw_finite I, triangularLaw_mass I,
    Sampling.triangularLaw_first_marginal I,
    Sampling.triangularLaw_second_marginal I,
    Sampling.triangularLaw_ordered I,
    fun x => (Sampling.triangular_density_bounds I x).1,
    fun y => (Sampling.triangular_density_bounds I y).2⟩

end Invariant233.ProductModel

end OAI
