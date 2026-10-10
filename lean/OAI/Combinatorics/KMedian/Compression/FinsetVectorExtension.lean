import Mathlib

namespace OAI

namespace MetricKMedian.Compression
open Finset

def extendVector {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ) (i : Fin n) : ℤ :=
  if h : i ∈ s then z ((s.orderIsoOfFin rfl).symm ⟨i,h⟩) else 0

theorem extendVector_at {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (i : Fin s.card) : extendVector s z ((s.orderIsoOfFin rfl) i).val=z i := by
  have hi := ((s.orderIsoOfFin rfl) i).property
  simp only [extendVector,dite_eq_left hi]
  congr 1
  exact (s.orderIsoOfFin rfl).symm_apply_apply i

theorem extendVector_zero {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (i : Fin n) (hi : i ∉ s) : extendVector s z i=0 := dite_eq_right hi

theorem extendVector_sum {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (g : Fin n → ℤ) :
    (∑ i, extendVector s z i*g i)=∑ j, z j*g ((s.orderIsoOfFin rfl) j).val := by
  let e := (s.orderIsoOfFin rfl).toEquiv
  calc
    _ = ∑ i ∈ s, extendVector s z i*g i := by
      symm
      apply sum_subset (subset_univ _)
      intro i _ hi
      rw [extendVector_zero s z i hi,zero_mul]
    _ = ∑ i : s, extendVector s z i.val*g i.val := by
      exact (sum_coe_sort s (fun i => extendVector s z i*g i)).symm
    _ = ∑ j, extendVector s z (e j).val*g (e j).val := (e.sum_comp _).symm
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [show extendVector s z (e j).val=z j from extendVector_at s z j]
      rfl

theorem extendVector_bound {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (H : ℤ) (hH : 0 ≤ H) (hz : ∀ j, |z j| ≤ H) (i : Fin n) :
    |extendVector s z i| ≤ H := by
  by_cases hi : i ∈ s
  · simp only [extendVector,dite_eq_left hi]; exact hz _
  · rw [extendVector_zero s z i hi,abs_zero]; exact hH

end MetricKMedian.Compression

end OAI
