import Mathlib
import OAI.Combinatorics.KMedian.Compression.AffineElimination

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def positiveSet {n : ℕ} (z : Fin n → ℤ) : Finset (Fin n) :=
  univ.filter (fun i => 0 < z i)

theorem positiveSet_nonempty {n : ℕ} (z : Fin n → ℤ)
    (hsum : ∑ i, z i=0) (hne : ∃ i, z i ≠ 0) : (positiveSet z).Nonempty := by
  obtain ⟨i,hi⟩ := positive_entry hsum hne
  exact ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩

def ratio {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ) (i : Fin n) : ℚ :=
  (μ.numerator i:ℚ)/(z i:ℚ)

def leastRatio {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) : ℚ :=
  ((positiveSet z).image (ratio μ z)).min' (h.image _)

def pivotSet {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) : Finset (Fin n) :=
  (positiveSet z).filter (fun i => ratio μ z i=leastRatio μ z h)

theorem pivotSet_nonempty {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) : (pivotSet μ z h).Nonempty := by
  obtain ⟨i,hi,he⟩ := mem_image.mp
    (min'_mem ((positiveSet z).image (ratio μ z)) (h.image _))
  exact ⟨i,mem_filter.mpr ⟨hi,he⟩⟩

def computedPivot {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) : Fin n :=
  (pivotSet μ z h).min' (pivotSet_nonempty μ z h)

theorem computedPivot_spec {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) :
    0 < z (computedPivot μ z h) ∧
      ∀ i, 0 < z i → ratio μ z (computedPivot μ z h) ≤ ratio μ z i := by
  have hp := mem_filter.mp (min'_mem (pivotSet μ z h) (pivotSet_nonempty μ z h))
  refine ⟨(mem_filter.mp hp.1).2,?_⟩
  intro i hi
  rw [computedPivot,hp.2]
  exact min'_le _ _ (mem_image_of_mem (ratio μ z)
    (mem_filter.mpr ⟨mem_univ _,hi⟩))

theorem updated_nonneg {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (p : Fin n) (hp : 0 < z p)
    (hmin : ∀ i, 0 < z i → ratio μ z p ≤ ratio μ z i) (i : Fin n) :
    0 ≤ μ.numerator i*z p-μ.numerator p*z i := by
  by_cases hzi : 0 < z i
  · have hqp : (0:ℚ) < z p := by exact_mod_cast hp
    have hqi : (0:ℚ) < z i := by exact_mod_cast hzi
    have hh := (div_le_div_iff₀ hqp hqi).mp (hmin i hzi)
    have hhZ : μ.numerator p*z i ≤ μ.numerator i*z p := by exact_mod_cast hh
    exact sub_nonneg.mpr hhZ
  · have hle : z i ≤ 0 := le_of_not_gt hzi
    exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos (μ.numerator_nonneg p) hle).trans
      (mul_nonneg (μ.numerator_nonneg i) hp.le))

def eliminateAt {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ) (p : Fin n)
    (hp : 0 < z p) (hmin : ∀ i, 0 < z i → ratio μ z p ≤ ratio μ z i)
    (hzsum : ∑ i, z i=0) : IntegerLaw (Fin n) :=
  let b := Vector.ofFn (fun i => μ.numerator i*z p-μ.numerator p*z i)
  { denominator := μ.denominator*z p
    denominator_pos := mul_pos μ.denominator_pos hp
    numerator := fun i => b[i.val]
    numerator_nonneg := by
      intro i
      simp only [b,Vector.getElem_ofFn]
      exact updated_nonneg μ z p hp hmin i
    total := by
      simp only [b,Vector.getElem_ofFn,sum_sub_distrib,← sum_mul,← mul_sum,
        μ.total,hzsum,mul_zero,sub_zero] }

@[simp] theorem eliminateAt_numerator {n : ℕ} (μ : IntegerLaw (Fin n))
    (z : Fin n → ℤ) (p : Fin n) (hp : 0 < z p)
    (hmin : ∀ i, 0 < z i → ratio μ z p ≤ ratio μ z i) (hzsum : ∑ i, z i=0)
    (i : Fin n) : (eliminateAt μ z p hp hmin hzsum).numerator i=
      μ.numerator i*z p-μ.numerator p*z i := by
  simp only [eliminateAt,Vector.getElem_ofFn]

end MetricKMedian.IntegerLaw

end OAI
