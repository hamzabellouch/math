import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.NumberTheory.SiegelZeros.Structure.FiberCount

namespace OAI

namespace SiegelZeros


namespace SiegelZerosAwei.W31

open scoped BigOperators

theorem sum_equiv_finset {ι n A : Type*} [Fintype n] [AddCommMonoid A]
    (P : Finset ι) (e : n ≃ P) (f : ι → A) :
    (∑ i, f (e i)) = ∑ a ∈ P, f a := by
  calc
    _ = ∑ a : P, f a := e.sum_comp (fun a : P => f a)
    _ = _ := Finset.sum_coe_sort P f

theorem card_equiv_finset {ι n : Type*} [Fintype n]
    (P : Finset ι) (e : n ≃ P) : P.card = Fintype.card n := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm

def pivotFirstSum (P : Finset MultiIndex) : ℕ := ∑ a ∈ P, a 0

def pivotOtherSum (P : Finset MultiIndex) : ℕ := ∑ a ∈ P, (a 1 + a 2)

theorem reindexed_first_sum {n : Type*} [Fintype n]
    (P : Finset MultiIndex) (e : n ≃ P) :
    (∑ i, (e i : MultiIndex) 0) = pivotFirstSum P :=
  sum_equiv_finset P e (fun a => a 0)

theorem reindexed_other_sum {n : Type*} [Fintype n]
    (P : Finset MultiIndex) (e : n ≃ P) :
    (∑ i, ((e i : MultiIndex) 1 + (e i : MultiIndex) 2)) = pivotOtherSum P :=
  sum_equiv_finset P e (fun a => a 1 + a 2)

theorem reindexed_first_sum_real {n : Type*} [Fintype n]
    (P : Finset MultiIndex) (e : n ≃ P) :
    (∑ i, ((e i : MultiIndex) 0 : ℝ)) = ∑ a ∈ P, (a 0 : ℝ) :=
  sum_equiv_finset P e (fun a => (a 0 : ℝ))

theorem reindexed_other_sum_real {n : Type*} [Fintype n]
    (P : Finset MultiIndex) (e : n ≃ P) :
    (∑ i, (((e i : MultiIndex) 1 : ℝ) + ((e i : MultiIndex) 2 : ℝ))) =
      ∑ a ∈ P, ((a 1 : ℝ) + (a 2 : ℝ)) :=
  sum_equiv_finset P e (fun a => (a 1 : ℝ) + (a 2 : ℝ))

theorem reindexed_first_fiber_card {n : Type*} [Fintype n]
    (P : Finset MultiIndex) (e : n ≃ P) (k : ℕ) :
    (Finset.univ.filter (fun i : n => (e i : MultiIndex) 0 = k)).card =
      (P.filter (fun a => a 0 = k)).card := by
  classical
  simpa only [Finset.sum_boole, Nat.cast_id] using
    sum_equiv_finset P e (fun a => if a 0 = k then (1 : ℕ) else 0)

theorem reindexed_cutoff_iff {n : Type*} [Fintype n]
    (P : Finset MultiIndex) (e : n ≃ P) (H C : ℝ) :
    (∀ i, weight H (e i) ≤ C) ↔ ∀ a ∈ P, weight H a ≤ C := by
  constructor
  · intro h a ha
    simpa only [e.apply_symm_apply] using h (e.symm ⟨a, ha⟩)
  · intro h i
    exact h (e i) (e i).property

theorem sum_equiv_coordinate_image {ι n A : Type*} [Fintype n] [AddCommMonoid A]
    (P : Finset ι) (e : n ≃ P) (coords : ι → MultiIndex)
    (hc : Function.Injective coords) (f : MultiIndex → A) :
    (∑ i, f (coords (e i))) = ∑ a ∈ P.image coords, f a := by
  classical
  rw [sum_equiv_finset P e (fun a => f (coords a))]
  exact (Finset.sum_image (fun _ _ _ _ hab => hc hab)).symm

theorem card_equiv_coordinate_image {ι n : Type*} [Fintype n]
    (P : Finset ι) (e : n ≃ P) (coords : ι → MultiIndex)
    (hc : Function.Injective coords) :
    (P.image coords).card = Fintype.card n := by
  rw [Finset.card_image_of_injective P hc]
  exact card_equiv_finset P e

theorem exists_selected_det_with_exact_sums {K n : Type*}
    [Field K] [Fintype n] [DecidableEq n]
    (rows : MultiIndex → n → K) (P : Finset MultiIndex)
    (hlin : LinearIndepOn K rows (P : Set MultiIndex))
    (hspan : Submodule.span K (rows '' (P : Set MultiIndex)) = ⊤) :
    ∃ e : n ≃ P,
      Matrix.det (fun i j => rows (e i) j) ≠ 0 ∧
      P.card = Fintype.card n ∧
      (∑ i, (e i : MultiIndex) 0) = pivotFirstSum P ∧
      (∑ i, ((e i : MultiIndex) 1 + (e i : MultiIndex) 2)) = pivotOtherSum P := by
  obtain ⟨e, he⟩ := SiegelZerosAwei.W30.selected_equiv_det_ne_zero rows P hlin hspan
  exact ⟨e, he, card_equiv_finset P e, reindexed_first_sum P e, reindexed_other_sum P e⟩

theorem ordered_sum_finset {ι A : Type*} [LinearOrder ι] [AddCommMonoid A]
    {M : ℕ} (P : Finset ι) (hcard : P.card = M) (f : ι → A) :
    (∑ i : Fin M, f (SiegelZerosAwei.W30.orderedIndex P hcard i)) =
      ∑ a ∈ P, f a :=
  sum_equiv_finset P (P.orderIsoOfFin hcard).toEquiv f

theorem ordered_coordinate_image_sum {ι A : Type*} [LinearOrder ι] [AddCommMonoid A]
    {M : ℕ} (P : Finset ι) (hcard : P.card = M) (coords : ι → MultiIndex)
    (hc : Function.Injective coords) (f : MultiIndex → A) :
    (∑ i : Fin M, f (coords (SiegelZerosAwei.W30.orderedIndex P hcard i))) =
      ∑ a ∈ P.image coords, f a :=
  sum_equiv_coordinate_image P (P.orderIsoOfFin hcard).toEquiv coords hc f

theorem ordered_coordinate_pivot_data {ι : Type*} [LinearOrder ι]
    {M : ℕ} (P : Finset ι) (hcard : P.card = M) (coords : ι → MultiIndex)
    (hc : Function.Injective coords) :
    (P.image coords).card = M ∧
    (∑ i : Fin M, (coords (SiegelZerosAwei.W30.orderedIndex P hcard i) 0 : ℝ)) =
      (∑ a ∈ P.image coords, (a 0 : ℝ)) ∧
    (∑ i : Fin M,
      ((coords (SiegelZerosAwei.W30.orderedIndex P hcard i) 1 : ℝ) +
       (coords (SiegelZerosAwei.W30.orderedIndex P hcard i) 2 : ℝ))) =
      (∑ a ∈ P.image coords, ((a 1 : ℝ) + (a 2 : ℝ))) := by
  refine ⟨?_, ordered_coordinate_image_sum P hcard coords hc (fun a => (a 0 : ℝ)),
    ordered_coordinate_image_sum P hcard coords hc (fun a => (a 1 : ℝ) + (a 2 : ℝ))⟩
  rw [Finset.card_image_of_injective P hc, hcard]

theorem ordered_coordinate_fiber_card {ι : Type*} [LinearOrder ι]
    {M : ℕ} (P : Finset ι) (hcard : P.card = M) (coords : ι → MultiIndex)
    (hc : Function.Injective coords) (k : ℕ) :
    (Finset.univ.filter (fun i : Fin M =>
      coords (SiegelZerosAwei.W30.orderedIndex P hcard i) 0 = k)).card =
    ((P.image coords).filter (fun a => a 0 = k)).card := by
  classical
  simpa only [Finset.sum_boole, Nat.cast_id] using
    ordered_coordinate_image_sum P hcard coords hc (fun a => if a 0 = k then (1 : ℕ) else 0)

theorem ordered_total_order_sum {ι : Type*} [LinearOrder ι]
    {M : ℕ} (P : Finset ι) (hcard : P.card = M) (coords : ι → MultiIndex) :
    (∑ i : Fin M,
      ((coords (SiegelZerosAwei.W30.orderedIndex P hcard i) 0 +
        coords (SiegelZerosAwei.W30.orderedIndex P hcard i) 1 +
        coords (SiegelZerosAwei.W30.orderedIndex P hcard i) 2 : ℕ) : ℝ)) =
      (∑ a ∈ P, (coords a 0 : ℝ)) +
      (∑ a ∈ P, ((coords a 1 : ℝ) + (coords a 2 : ℝ))) := by
  rw [ordered_sum_finset P hcard
    (fun a => ((coords a 0 + coords a 1 + coords a 2 : ℕ) : ℝ))]
  simp only [Nat.cast_add, Finset.sum_add_distrib, add_assoc]

theorem ordered_total_order_image_sum {ι : Type*} [LinearOrder ι]
    {M : ℕ} (P : Finset ι) (hcard : P.card = M) (coords : ι → MultiIndex)
    (hc : Function.Injective coords) :
    (∑ i : Fin M,
      ((coords (SiegelZerosAwei.W30.orderedIndex P hcard i) 0 +
        coords (SiegelZerosAwei.W30.orderedIndex P hcard i) 1 +
        coords (SiegelZerosAwei.W30.orderedIndex P hcard i) 2 : ℕ) : ℝ)) =
      (∑ a ∈ P.image coords, (a 0 : ℝ)) +
      (∑ a ∈ P.image coords, ((a 1 : ℝ) + (a 2 : ℝ))) := by
  rw [ordered_coordinate_image_sum P hcard coords hc
    (fun a => ((a 0 + a 1 + a 2 : ℕ) : ℝ))]
  simp only [Nat.cast_add, Finset.sum_add_distrib, add_assoc]

end SiegelZerosAwei.W31


end SiegelZeros

end OAI
