import Mathlib
import OAI.Combinatorics.Chromatic.Walls.WallUnits

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries
variable {K : Type*} [Field K]
lemma complete_tail (q u : K) (hq : ∀ n : ℕ,1-q^(n+1)≠0) :
    PowerSeries.rescale q (complete q u)=(1+PowerSeries.C (-u)*PowerSeries.X)*complete q u := by
  rw [complete,rescale_inv_of_const_one _ _ (constant_elementary _ _)]
  symm
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by
    rw [←PowerSeries.coeff_zero_eq_constantCoeff,coeff_rescale,pow_zero,one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff,constant_elementary]
    exact one_ne_zero)).mpr
  calc
    ((1+C (-u)*X)*(elementary q (-u))⁻¹)*PowerSeries.rescale q (elementary q (-u))=
        (elementary q (-u))⁻¹*((1+C (-u)*X)*PowerSeries.rescale q (elementary q (-u))) := by ring
    _=(elementary q (-u))⁻¹*elementary q (-u) := by rw [←elementary_tail q (-u) hq]
    _=1 := PowerSeries.inv_mul_cancel _ (by rw [constant_elementary]; exact one_ne_zero)

lemma complete_coeff_recursion (q u : K) (hq : ∀ n : ℕ,1-q^(n+1)≠0) (n : ℕ) :
    coeff (n+1) (complete q u)*(1-q^(n+1))=u*coeff n (complete q u) := by
  have h:=congrArg (coeff (n+1)) (complete_tail q u hq)
  rw [add_mul,one_mul,map_add,mul_assoc,coeff_C_mul,coeff_succ_X_mul,coeff_rescale] at h
  linear_combination -h

lemma complete_coeff_zero (q u : K) : coeff 0 (complete q u)=1 := by
  rw [complete,coeff_zero_eq_constantCoeff,PowerSeries.constantCoeff_inv,constant_elementary,inv_one]
end ElementaryPositivity.WallUnits
namespace ElementaryPositivity.WallUnits
open PowerSeries
variable {K : Type*} [Field K]
lemma elementaryCoeff_eq_complete (q u : K) (hq : ∀ n : ℕ,1-q^(n+1)≠0) (n : ℕ) :
    elementaryCoeff q u n=q^(∑i∈Finset.range n,i)*coeff n (complete q u) := by
  induction n with
  | zero => simp [elementaryCoeff,complete_coeff_zero]
  | succ n ih =>
    have hh : coeff (n+1) (complete q u)=u*coeff n (complete q u)/(1-q^(n+1)) :=
      (eq_div_iff (hq n)).mpr (complete_coeff_recursion q u hq n)
    rw [elementaryCoeff,ih,Finset.sum_range_succ,pow_add,hh]
    ring
end ElementaryPositivity.WallUnits
end
end

end OAI
