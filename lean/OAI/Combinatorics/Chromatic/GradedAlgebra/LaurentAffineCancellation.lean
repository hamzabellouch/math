import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentInfinity

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R]

noncomputable def affinePolynomial (c : R) : Polynomial R := Polynomial.C c-Polynomial.X

@[simp] lemma polynomial_affinePolynomial (c : R) :
    polynomial (affinePolynomial c)=(affineUnit c : LaurentSeries R) := by
  simp [affinePolynomial]

lemma affineUnit_zpow_cancel (c : R) (e : ℤ) :
    ((affineUnit c)^e : (LaurentSeries R)ˣ).val *
       polynomial ((affinePolynomial c)^(-e).toNat)=
       polynomial ((affinePolynomial c)^e.toNat) := by
  rw [map_pow,map_pow,polynomial_affinePolynomial]
  have hi : e+((-e).toNat : ℤ)=(e.toNat : ℤ) := by omega
  have h : (affineUnit c)^e*(affineUnit c)^(-e).toNat=(affineUnit c)^e.toNat := by
    rw [←zpow_natCast,←zpow_add,hi,zpow_natCast]
  exact congrArg Units.val h

lemma affineProduct_zpow_cancel {ι : Type*} (s : Finset ι) (c : ι → R) (e : ι → ℤ) :
    ((∏ i∈s,(affineUnit (c i))^(e i) : (LaurentSeries R)ˣ).val) *
      polynomial (∏ i∈s,affinePolynomial (c i)^(-(e i)).toNat)=
      polynomial (∏ i∈s,affinePolynomial (c i)^(e i).toNat) := by
  rw [map_prod,map_prod,Units.coe_prod,←Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i hi=>affineUnit_zpow_cancel (c i) (e i)
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
