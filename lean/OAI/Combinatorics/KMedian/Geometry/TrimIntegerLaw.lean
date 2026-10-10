import Mathlib
import OAI.Combinatorics.KMedian.Compression.AffineKernel

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def trim {n : ℕ} (μ : IntegerLaw (Fin n)) : IntegerLaw (Fin μ.support.card) where
  denominator := μ.denominator
  denominator_pos := μ.denominator_pos
  numerator := let v := Vector.ofFn (fun i => μ.numerator (μ.support.orderEmbOfFin rfl i))
    fun i => v[i.val]
  numerator_nonneg i := by
    simpa only [Vector.getElem_ofFn] using
      μ.numerator_nonneg (μ.support.orderEmbOfFin rfl i)
  total := by
    simp only [Vector.getElem_ofFn]
    calc
      _ = ∑ i : μ.support, μ.numerator i :=
        Equiv.sum_comp (μ.support.orderIsoOfFin rfl).toEquiv _
      _ = ∑ i ∈ μ.support, μ.numerator i := sum_coe_sort μ.support μ.numerator
      _ = ∑ i, μ.numerator i := by
        apply sum_subset (subset_univ _)
        intro i _ hi
        exact not_not.mp (by simpa only [mem_support] using hi)
      _ = _ := μ.total

@[simp] theorem trim_denominator {n : ℕ} (μ : IntegerLaw (Fin n)) :
    μ.trim.denominator=μ.denominator := rfl

@[simp] theorem trim_numerator {n : ℕ} (μ : IntegerLaw (Fin n))
    (i : Fin μ.support.card) :
    μ.trim.numerator i=μ.numerator (μ.support.orderEmbOfFin rfl i) := by
  simp only [trim,Vector.getElem_ofFn]

@[simp] theorem trim_weight {n : ℕ} (μ : IntegerLaw (Fin n))
    (i : Fin μ.support.card) :
    μ.trim.rational.weight i=μ.rational.weight (μ.support.orderEmbOfFin rfl i) := by
  simp only [rational,trim_numerator,trim_denominator]

theorem trim_moment {n : ℕ} (μ : IntegerLaw (Fin n)) (f : Fin n → ℚ) :
    (∑ i, μ.trim.rational.weight i*f (μ.support.orderEmbOfFin rfl i))=
      ∑ i, μ.rational.weight i*f i := by
  simp only [trim_weight]
  calc
    _ = ∑ i : μ.support, μ.rational.weight i*f i :=
      Equiv.sum_comp (μ.support.orderIsoOfFin rfl).toEquiv _
    _ = ∑ i ∈ μ.support, μ.rational.weight i*f i := sum_coe_sort μ.support (fun i => μ.rational.weight i*f i)
    _ = _ := by
      apply sum_subset (subset_univ _)
      intro i _ hi
      have hz : μ.numerator i=0 := not_not.mp (by simpa only [mem_support] using hi)
      simp only [rational,hz,Int.cast_zero,zero_div,zero_mul]

end MetricKMedian.IntegerLaw

end OAI
