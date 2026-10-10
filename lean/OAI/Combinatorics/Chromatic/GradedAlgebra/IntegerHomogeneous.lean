import Mathlib

namespace OAI

section
namespace ElementaryPositivity.Homogeneity
open MvPolynomial
variable {σ R : Type*} [CommRing R]
lemma constantWeight_eq_zero (d : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ=>(1:ℤ)) d=0 ↔ d=0 := by
  classical
  simp only [Finsupp.weight_apply,nsmul_eq_mul,mul_one,Finsupp.sum]
  constructor
  · intro h
    ext i
    by_cases hi : i∈d.support
    · have he := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j∈d.support)=>Int.natCast_nonneg (d j))).mp h i hi
      exact_mod_cast he
    · exact Finsupp.notMem_support_iff.mp hi
  · intro h
    subst d
    simp

lemma constantWeight_component_zero (p : MvPolynomial σ R) :
    weightedHomogeneousComponent (fun _=>(1:ℤ)) 0 p=C (constantCoeff p) := by
  classical
  ext d
  simp only [coeff_weightedHomogeneousComponent,constantWeight_eq_zero,coeff_C]
  by_cases hd : d=0
  · subst d
    rfl
  · simp [hd,Ne.symm hd]
end ElementaryPositivity.Homogeneity

end

end OAI
