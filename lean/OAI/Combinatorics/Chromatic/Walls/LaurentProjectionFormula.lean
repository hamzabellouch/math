import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentInfinity

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {K A B : Type*} [CommSemiring K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

lemma mapLinear_projection (T : A →ₗ[K] B) (ι : B →+* A)
    (hT : ∀ b x,T (ι b*x)=b*T x) (P : LaurentSeries B) (X : LaurentSeries A) :
    mapLinear T (mapRing ι P * X)=P*mapLinear T X := by
  apply HahnSeries.ext
  funext k
  have hP : (mapRing ι P).support⊆P.support := HahnSeries.support_map_subset P ι.toZeroHom
  have hX : (mapLinear T X).support⊆X.support := HahnSeries.support_map_subset X ⟨T,T.map_zero⟩
  rw [mapLinear_coeff,coeff_mul_left' P.isPWO_support hP,
    coeff_mul_right' X.isPWO_support hX,map_sum]
  apply Finset.sum_congr rfl
  intro xy hxy
  exact hT _ _

end ElementaryPositivity.LaurentAtInfinity

end

end OAI
