import OAI.Dynamics.StandardMap.CappedTests

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
noncomputable def dyadicFine (n : ℕ) (s : DyadicTime) : DyadicTime := (dyadicHalf^[n]) s
lemma dyadicFine_val (n : ℕ) (s : DyadicTime) : (dyadicFine n s:ℝ)=(s:ℝ)/(2:ℝ)^n := by
  induction n with
  | zero => simp [dyadicFine]
  | succ n ih =>
    rw [dyadicFine,Function.iterate_succ_apply']
    rw [dyadicHalf_val,show ((dyadicHalf^[n]) s:ℝ)=(s:ℝ)/(2:ℝ)^n from ih,pow_succ]
    ring
lemma dyadicFine_zero (n : ℕ) : dyadicFine n 0=0 := by
  apply Subtype.ext
  simp only [dyadicFine_val,ZeroMemClass.coe_zero,zero_div]
lemma dyadicFine_add (n : ℕ) (s t : DyadicTime) : dyadicFine n (s+t)=dyadicFine n s+dyadicFine n t := by
  apply Subtype.ext
  simp only [dyadicFine_val,AddSubgroup.coe_add,add_div]
lemma halfIterate_unit (n : ℕ) (d : NonAffineArray) (hu : UnitArray d.val) : UnitArray ((nonaffineHalf^[n]) d).val := by
  induction n with
  | zero => exact hu
  | succ n ih => simpa only [Function.iterate_succ_apply'] using nonaffineHalf_unit _ ih
lemma halfIterate_eval (n : ℕ) (d : NonAffineArray) (hu : UnitArray d.val) (s t : DyadicTime) :
    ((nonaffineHalf^[n]) d).val.val s t=(2:ℝ)^n*d.val.val (dyadicFine n s) (dyadicFine n t) := by
  induction n generalizing s t with
  | zero => simp [dyadicFine]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [nonaffineHalf,dite_eq_left (halfIterate_unit n d hu)]
    change 2*((nonaffineHalf^[n]) d).val.val (dyadicHalf s) (dyadicHalf t)=_
    rw [ih,pow_succ]
    have he (s:DyadicTime) : dyadicFine n (dyadicHalf s)=dyadicFine (n+1) s := by
      exact (Function.iterate_succ_apply _ _ _).symm
    rw [he,he]
    ring
lemma halfIterate_shortfall (n : ℕ) (d : NonAffineArray) (hu : UnitArray d.val) (s t : DyadicTime) :
    arrayShortfall s t ((nonaffineHalf^[n]) d).val=arrayShortfall (dyadicFine n s) (dyadicFine n t) d.val := by
  unfold arrayShortfall
  rw [halfIterate_eval n d hu,dyadicFine_val,dyadicFine_val,←sub_div]
  congr 1
  rw [div_div_eq_mul_div,mul_comm]
lemma shortfall_half_bound (d : NonAffineArray) (hu : UnitArray d.val) :
    arrayShortfall 0 (dyadicInt 1) (nonaffineHalf d).val≤2*arrayShortfall 0 (dyadicInt 1) d.val := by
  have hj := arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) (nonaffineHalf d).val
  have hz := (shortfall_unit_mem (nonaffineHalf d).val (nonaffineHalf_unit d hu) (dyadicInt 1) (dyadicInt 2) (by norm_num)).1
  have he : arrayShortfall 0 (dyadicInt 2) (nonaffineHalf d).val=arrayShortfall 0 (dyadicInt 1) d.val := by
    rw [nonaffineHalf,dite_eq_left hu]
    dsimp only [arrayShortfall,nonaffineHalfOn,arrayHalf]
    simp only [dyadicInt_val,ZeroMemClass.coe_zero,Int.cast_one,Int.cast_ofNat,sub_zero]
    have h0 : dyadicHalf 0=0 := by apply Subtype.ext; norm_num
    have h1 : dyadicHalf (dyadicInt 2)=dyadicInt 1 := by apply Subtype.ext; norm_num
    rw [h0,h1]; ring
  simp only [arrayJ,dyadicMid_zero_two,he] at hj
  linarith
end StandardMapEntropy

end OAI
