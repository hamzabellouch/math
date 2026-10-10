import Mathlib
import OAI.Combinatorics.Chromatic.Walls.HNSpanning

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {A B σ : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

lemma mapLinear_scalar_mul (l : A →ₗ[ℚ] B) (p : MvPolynomial σ ℚ) (f : MvPolynomial σ A) :
    mapLinear l (map (algebraMap ℚ A) p*f)=map (algebraMap ℚ B) p*mapLinear l f := by
  classical
  ext m
  simp only [coeff_mapLinear,coeff_mul,coeff_map,map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simpa only [Algebra.smul_def] using l.map_smul (p.coeff x.1) (f.coeff x.2)

end ElementaryPositivity.CenterCalculus

end

end OAI
