import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.BothTaylorB
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentInfinity

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
@[simp] lemma mapLinear_single (f : R →ₗ[ℚ] S) (n : ℤ) (r : R) :
    mapLinear f (single n r)=single n (f r) := by
  apply HahnSeries.ext
  funext k
  simp only [mapLinear_coeff,coeff_single]
  split_ifs <;> simp

lemma polynomial_mapLinear (f : R →ₗ[ℚ] S) (p : Polynomial R) :
    mapLinear f (polynomial p)=polynomial (RawShuffle.polynomialMapLinear f p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n r => rw [RawShuffle.polynomialMapLinear_monomial,polynomial_monomial,
      polynomial_monomial,mapLinear_single]
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
