import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical

namespace OrdinaryCorrelations.SourceRoughSieveLocal

def avoids (q : ℕ) (x y z : ZMod q) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x+y-z ≠ 0

def badDensity (q : ℕ) [NeZero q] : ℝ :=
  (q:ℝ)⁻¹^3 * ∑ x : ZMod q, ∑ y : ZMod q, ∑ z : ZMod q,
    if avoids q x y z then 0 else 1

lemma sum_nonzero {q : ℕ} [NeZero q] :
    (∑ z : ZMod q, if z ≠ 0 then (1:ℝ) else 0) = q-1 := by
  have he (z : ZMod q) : (if z ≠ 0 then (1:ℝ) else 0) = 1 - (if z=0 then 1 else 0) := by
    split_ifs <;> simp_all
  simp only [he,Finset.sum_sub_distrib]
  simp

lemma sum_avoid_two {q : ℕ} [NeZero q] (a : ZMod q) :
    (∑ z : ZMod q, if z ≠ 0 ∧ z ≠ a then (1:ℝ) else 0) =
      q-2+(if a=0 then 1 else 0) := by
  have he (z : ZMod q) :
      (if z ≠ 0 ∧ z ≠ a then (1:ℝ) else 0) =
      1 - (if z=0 then 1 else 0) - (if z=a then 1 else 0) +
        (if a=0 then 1 else 0) * (if z=0 then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  simp
  ring

lemma sum_identity {q : ℕ} [NeZero q] (x : ZMod q) :
    (∑ y : ZMod q, if y ≠ 0 then (if x+y=0 then (1:ℝ) else 0) else 0) =
      if x ≠ 0 then 1 else 0 := by
  have he : ∀ y : ZMod q, x+y=0 ↔ y=-x := by
    intro y
    constructor
    · intro h; calc y = x+y-x := by ring
                   _ = -x := by rw [h]; simp
    · intro h; rw [h,add_neg_cancel]
  simp only [he]
  rw [Finset.sum_eq_single (-x)]
  · simp
  · intro y _ hy
    simp [hy]
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

lemma good_sum {q : ℕ} [NeZero q] :
    (∑ x : ZMod q, ∑ y : ZMod q, ∑ z : ZMod q,
      if avoids q x y z then (1:ℝ) else 0) =
        (q-1) * ((q-1)*(q-2)+1) := by
  have he (x y : ZMod q) : (∑ z : ZMod q,
      if avoids q x y z then (1:ℝ) else 0) =
      if x≠0 ∧ y≠0 then (q:ℝ)-2+(if x+y=0 then 1 else 0) else 0 := by
    by_cases hx : x=0
    · simp [avoids,hx]
    by_cases hy : y=0
    · simp [avoids,hy]
    have hz (z : ZMod q) : x+y-z ≠ 0 ↔ z ≠ x+y := by
      rw [sub_ne_zero,ne_comm]
    simpa [avoids,hx,hy,hz] using sum_avoid_two (x+y)
  simp_rw [he]
  have hy (x : ZMod q) (hx : x≠0) :
      (∑ y : ZMod q, if x≠0 ∧ y≠0 then (q:ℝ)-2+(if x+y=0 then 1 else 0) else 0) =
      (q-1)*(q-2)+1 := by
    have he' (y : ZMod q) :
        (if x≠0 ∧ y≠0 then (q:ℝ)-2+(if x+y=0 then 1 else 0) else 0) =
        (if y≠0 then (1:ℝ) else 0)*(q-2) +
          (if y≠0 then (if x+y=0 then 1 else 0) else 0) := by
      by_cases hy : y=0 <;> simp [hx,hy]
    simp_rw [he']
    rw [Finset.sum_add_distrib,← Finset.sum_mul,sum_nonzero,sum_identity,ite_eq_left hx]
  have hx (x : ZMod q) :
      (∑ y : ZMod q, if x≠0 ∧ y≠0 then (q:ℝ)-2+(if x+y=0 then 1 else 0) else 0) =
      (if x≠0 then (1:ℝ) else 0) * ((q-1)*(q-2)+1) := by
    by_cases hx : x=0
    · simp [hx]
    · rw [hy x hx,ite_eq_left hx,one_mul]
  simp_rw [hx]
  rw [← Finset.sum_mul,sum_nonzero]

theorem badDensity_formula {q : ℕ} [NeZero q] :
    badDensity q = 4/(q:ℝ) - 6/(q:ℝ)^2 + 3/(q:ℝ)^3 := by
  have he : (∑ x : ZMod q, ∑ y : ZMod q, ∑ z : ZMod q,
      if avoids q x y z then (0:ℝ) else 1) =
      (q:ℝ)^3 - (q-1)*((q-1)*(q-2)+1) := by
    have hp (x y z : ZMod q) : (if avoids q x y z then (0:ℝ) else 1) =
        1 - (if avoids q x y z then 1 else 0) := by split_ifs <;> norm_num
    simp_rw [hp,Finset.sum_sub_distrib]
    rw [good_sum]
    simp
    ring
  have hq : (q:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  rw [badDensity,he]
  field_simp
  ring

theorem badDensity_bounds {q : ℕ} [NeZero q] (hq : 2 ≤ q) :
    0 < badDensity q ∧ badDensity q < 1 ∧
      4/(q:ℝ)-6/(q:ℝ)^2 ≤ badDensity q ∧ badDensity q ≤ 4/(q:ℝ) := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hp : (0:ℝ) < q := by linarith
  have hpow : (0:ℝ) < (q:ℝ)^3 := pow_pos hp _
  have he : badDensity q = (4*(q:ℝ)^2-6*q+3)/(q:ℝ)^3 := by
    rw [badDensity_formula]
    field_simp
  have hquad : 0 ≤ ((q:ℝ)-2)^2 := sq_nonneg _
  have hgood : 0 < ((q:ℝ)-1)*(((q:ℝ)-1)*((q:ℝ)-2)+1) := by
    apply mul_pos (by linarith)
    have : 0 ≤ ((q:ℝ)-1)*((q:ℝ)-2) := mul_nonneg (by linarith) (by linarith)
    linarith
  refine ⟨?_,?_,?_,?_⟩
  · rw [he]
    apply div_pos _ hpow
    nlinarith
  · rw [he,div_lt_one hpow]
    nlinarith
  · rw [badDensity_formula]
    exact le_add_of_nonneg_right (div_nonneg (by norm_num) hpow.le)
  · rw [badDensity_formula]
    have hsmall : 3/(q:ℝ)^3 ≤ 6/(q:ℝ)^2 := by
      apply (div_le_div_iff₀ hpow (sq_pos_of_pos hp)).mpr
      nlinarith [mul_nonneg ((show (0:ℝ) ≤ 2*q-1 by linarith)) (sq_nonneg (q:ℝ))]
    linarith

end OrdinaryCorrelations.SourceRoughSieveLocal

end

end OAI
