import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.FiniteTypeFieldModelEquiv

namespace OAI

namespace SiegelZeros

section
namespace WeightedTorusJets.Geometry

variable {K ι T : Type*} [CommRing K] [CommRing T] [Fintype ι]
  [Algebra K T] [Algebra (MvPolynomial ι K) T] [IsScalarTower K (MvPolynomial ι K) T]

theorem localize_invariantDerivation_log_coordinate (M : Submonoid (MvPolynomial ι K))
    [IsLocalization M T] (c : ι → K) (i : ι) (u : Tˣ)
    (hu : (u : T) = algebraMap (MvPolynomial ι K) T (MvPolynomial.X i)) :
    (↑(u⁻¹) : T) * localizeDerivation M (invariantDerivation c)
      (algebraMap (MvPolynomial ι K) T (MvPolynomial.X i)) = algebraMap K T (c i) := by
  rw [localize_invariantDerivation_X, ← hu]
  rw [mul_comm (algebraMap K T (c i)) (u : T)]
  exact Units.inv_mul_cancel_left u _

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {k F ι : Type*} [Field k] [Field F] [Algebra k F] [Fintype ι]

theorem lift_logarithmicForm (c : ι → k) (f : ι → F) (D : Derivation k F F) :
    D.liftKaehlerDifferential (logarithmicForm c f) =
      ∑ i, algebraMap k F (c i) * (f i)⁻¹ * D (f i) := by
  simp [logarithmicForm]

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
