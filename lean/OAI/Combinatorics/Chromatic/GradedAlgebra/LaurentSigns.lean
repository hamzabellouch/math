import Mathlib

namespace OAI

section
namespace ElementaryPositivity
variable {R : Type*} [CommRing R]
lemma unit_neg_one_inv : (-1 : Rˣ)⁻¹=(-1 : Rˣ) := by
  apply Units.ext
  simp

lemma unit_neg_one_zpow_sub (n m : ℤ) :
    (-1 : Rˣ)^n*(-1 : Rˣ)^m=(-1 : Rˣ)^(n-m) := by
  rw [zpow_sub,←inv_zpow,unit_neg_one_inv]

end ElementaryPositivity

lemma mul_sign_collect {G : Type*} [CommMonoid G] (s t p q r u : G) :
    s*p*q*r*(t*u)=(s*t)*(p*q*r*u) := by ac_rfl

end

end OAI
