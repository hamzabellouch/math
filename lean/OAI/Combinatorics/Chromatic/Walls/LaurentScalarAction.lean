import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentInfinity

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma mapLinear_scalar_mul (f : R →ₗ[ℚ] R) (q : LaurentSeries ℚ) (p : LaurentSeries R) :
    mapLinear f (mapRing (algebraMap ℚ R) q*p)=
      mapRing (algebraMap ℚ R) q*mapLinear f p := by
  apply HahnSeries.ext
  funext k
  rw [mapLinear_coeff,coeff_mul,
    coeff_mul_right' p.isPWO_support (by
      intro n hn
      change f (p.coeff n)≠0 at hn
      exact fun h=>hn (h ▸ f.map_zero))]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  change f (algebraMap ℚ R (q.coeff ij.1)*p.coeff ij.2)=
    algebraMap ℚ R (q.coeff ij.1)*f (p.coeff ij.2)
  rw [←Algebra.smul_def,←Algebra.smul_def,f.map_smul]
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
