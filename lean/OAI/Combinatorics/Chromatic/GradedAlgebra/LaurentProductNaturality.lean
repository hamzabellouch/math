import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentInfinity

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
variable {R S : Type*} [CommRing R] [CommRing S]
lemma mapRing_mul_polynomial (f : R →+* S) (K : LaurentSeries R) (p : Polynomial R) :
    mapRing f (K*polynomial p)=mapRing f K*polynomial (p.map f) := by
  rw [map_mul,polynomial_map]
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
