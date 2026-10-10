import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentInfinity

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
lemma rat_smul_series (r : ℚ) (x : LaurentSeries R) :
    r • x=C (algebraMap ℚ R r)*x := by
  apply HahnSeries.ext
  funext k
  simp only [HahnSeries.coeff_smul,HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul]
  exact Algebra.smul_def r (x.coeff k)
lemma mapRing_rat_smul (f : R →ₐ[ℚ] S) (r : ℚ) (x : LaurentSeries R) :
    mapRing f.toRingHom (r • x)=r • mapRing f.toRingHom x := by
  apply HahnSeries.ext
  funext k
  simp only [mapRing_coeff,HahnSeries.coeff_smul]
  exact f.toLinearMap.map_smul r (x.coeff k)
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
