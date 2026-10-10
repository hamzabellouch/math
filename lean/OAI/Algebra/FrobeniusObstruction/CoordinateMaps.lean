import Mathlib
import OAI.Algebra.FrobeniusObstruction.LinearChange

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k l : Type*} [Fintype ι] [DecidableEq ι] [CommRing k] [CommRing l]
variable (ell : ℕ)

                                                                             
def mapCoefficients (f : k →+* l) : Ring (ι := ι) (k := k) ell →+*
    Ring (ι := ι) (k := l) ell :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (MvPowerSeries.map f)) (by
    intro p hp
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
    simp only [RingHom.comp_apply, map_sum, map_mul, map_pow, MvPowerSeries.map_X]
    apply Finset.sum_eq_zero
    intro i _
    change _ * coordinate (k := l) ell i ^ ell = 0
    rw [coordinate_pow, mul_zero])

omit [DecidableEq ι] in
@[simp] theorem mapCoefficients_mk (f : k →+* l) (p : Series (ι := ι) (k := k)) :
    mapCoefficients ell f (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPowerSeries.map f p) := rfl

omit [DecidableEq ι] in
@[simp] theorem mapCoefficients_coordinate (f : k →+* l) (i : ι) :
    mapCoefficients ell f (coordinate ell i) = coordinate ell i := by
  simp [coordinate]

omit [DecidableEq ι] in
@[simp] theorem mapCoefficients_monomial (f : k →+* l) (v : Box (ι := ι) ell) :
    mapCoefficients ell f (monomial ell v) = monomial ell v := by
  simp [monomial]

omit [DecidableEq ι] in
@[simp] theorem coefficients_mapCoefficients (f : k →+* l) (x : Ring (ι := ι) (k := k) ell)
    (v : Box (ι := ι) ell) :
    coefficients ell (mapCoefficients ell f x) v = f (coefficients ell x v) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [mapCoefficients_mk, coefficients_apply, quotientCoeff_mk, MvPowerSeries.coeff_map]

                                                                             
def monomialBasis : Module.Basis (Box (ι := ι) ell) k (Ring (ι := ι) (k := k) ell) :=
  (Pi.basisFun k (Box (ι := ι) ell)).map (coefficientEquiv ell).symm

@[simp] theorem monomialBasis_apply (v : Box (ι := ι) ell) :
    monomialBasis (k := k) ell v = monomial ell v := by
  apply coefficients_injective ell
  funext w
  change (coefficientEquiv ell) ((coefficientEquiv ell).symm
    ((Pi.basisFun k (Box (ι := ι) ell)) v)) w = _
  rw [LinearEquiv.apply_symm_apply]
  simp [coefficients_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]

@[simp] theorem monomialBasis_repr (x : Ring (ι := ι) (k := k) ell) (v : Box (ι := ι) ell) :
    (monomialBasis ell).repr x v = coefficients ell x v := by
  simp [monomialBasis, coefficientEquiv]
  rfl

end BoundaryOnly.FormalObstruction.Frobenius

   
                                                                            
                                                                       
                                                                                
  

noncomputable section
open scoped BigOperators

end
end

end OAI
