import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentInfinity

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
variable {R : Type*} [CommRing R]

lemma map_quotient_eq_zero_iff (J : Ideal R) (x : LaurentSeries R) :
    mapRing (Ideal.Quotient.mk J) x=0 ↔ ∀ k,x.coeff k∈J := by
  constructor
  · intro h k
    have he:=congrArg (fun f : LaurentSeries (R⧸J)=>f.coeff k) h
    simpa only [mapRing_coeff,HahnSeries.coeff_zero,Pi.zero_apply,Ideal.Quotient.eq_zero_iff_mem] using he
  · intro h
    apply HahnSeries.ext
    funext k
    simpa only [mapRing_coeff,HahnSeries.coeff_zero,Pi.zero_apply,Ideal.Quotient.eq_zero_iff_mem] using h k

lemma coeff_mul_mem (J : Ideal R) (x y : LaurentSeries R)
    (hx : ∀ k,x.coeff k∈J) (k : ℤ) : (x*y).coeff k∈J := by
  apply (map_quotient_eq_zero_iff J (x*y)).mp _ k
  rw [map_mul,(map_quotient_eq_zero_iff J x).mpr hx,zero_mul]

lemma polynomial_coeff_mem (J : Ideal R) (p : Polynomial R)
    (hp : ∀ n,p.coeff n∈J) (k : ℤ) : (polynomial p).coeff k∈J := by
  by_cases hk : k≤0
  · obtain ⟨n,hn⟩:=Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hk)
    have he : k=-(n:ℤ) := by omega
    rw [he,polynomial_coeff]
    exact hp n
  · rw [polynomial_coeff_positive p k (lt_of_not_ge hk)]
    exact J.zero_mem
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
