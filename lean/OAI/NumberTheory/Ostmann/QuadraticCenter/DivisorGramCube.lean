import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem sum_powerset_prod_ite {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (P : Finset ι) (f g : ι → R) :
    (∑ s ∈ P.powerset, ∏ p ∈ P, if p ∈ s then f p else g p) =
      ∏ p ∈ P, (f p + g p) := by
  classical
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_ite, Finset.filter_mem_eq_of_subset (Finset.mem_powerset.mp hs)]
  congr 1
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_sdiff]

theorem double_powerset_pair_product {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (P : Finset ι) (a b c d : ι → R) :
    (∑ s ∈ P.powerset, ∑ t ∈ P.powerset,
      ∏ p ∈ P, if p ∈ s then (if p ∈ t then a p else b p)
        else (if p ∈ t then c p else d p)) =
      ∏ p ∈ P, (a p + b p + c p + d p) := by
  classical
  calc
    _ = ∑ s ∈ P.powerset, ∏ p ∈ P,
        ((if p ∈ s then a p else c p) + (if p ∈ s then b p else d p)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [← sum_powerset_prod_ite P (fun p => if p ∈ s then a p else c p)
        (fun p => if p ∈ s then b p else d p)]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hps : p ∈ s <;> simp only [hps, ite_true, ite_false]
    _ = ∑ s ∈ P.powerset, ∏ p ∈ P,
        if p ∈ s then a p + b p else c p + d p := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hps : p ∈ s <;> simp only [hps, ite_true, ite_false]
    _ = _ := by
      rw [sum_powerset_prod_ite]
      apply Finset.prod_congr rfl
      intro p hp
      simp only [add_assoc]

theorem double_powerset_symmetric_gram {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (a b : ι → ℝ) :
    (∑ s ∈ P.powerset, ∑ t ∈ P.powerset,
      ∏ p ∈ P, if p ∈ s then (if p ∈ t then b p else a p)
        else (if p ∈ t then a p else 1)) =
      ∏ p ∈ P, (1 + b p + 2 * a p) := by
  rw [double_powerset_pair_product]
  apply Finset.prod_congr rfl
  intro p hp
  ring

end Ostmann.QuadraticCenter

end OAI
