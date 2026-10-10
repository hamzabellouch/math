import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open Finset

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

def totalIncidences (A : ι → Finset α) : ℝ := ∑ i, (A i).card

def columnDegree (A : ι → Finset α) (p : α) : ℝ :=
  ∑ i, if p ∈ A i then 1 else 0

omit [Fintype ι] in
theorem row_eq_indicator_sum (A : ι → Finset α) (i : ι) :
    ((A i).card : ℝ) = ∑ p : α, if p ∈ A i then 1 else 0 := by
  simp

theorem totalIncidences_eq_sum_columns (A : ι → Finset α) :
    totalIncidences A = ∑ p, columnDegree A p := by
  simp only [totalIncidences, row_eq_indicator_sum, columnDegree]
  exact Finset.sum_comm

theorem sum_columns_sq (A : ι → Finset α) :
    ∑ p, columnDegree A p ^ 2 = ∑ i, ∑ j, ((A i ∩ A j).card : ℝ) := by
  simp only [columnDegree, pow_two, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ p : α, ∑ i : ι, ∑ j : ι,
      (if p ∈ A j then (1 : ℝ) else 0) * (if p ∈ A i then 1 else 0)) =
        ∑ i : ι, ∑ j : ι, ∑ p : α,
          (if p ∈ A j then (1 : ℝ) else 0) * (if p ∈ A i then 1 else 0) := by
      rw [Finset.sum_comm]
      congr 1
      ext i
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∑ p : α, (if p ∈ A j then (1 : ℝ) else 0) *
          (if p ∈ A i then 1 else 0)) =
            ∑ p : α, if p ∈ A i ∩ A j then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hi : p ∈ A i <;> by_cases hj : p ∈ A j <;> simp [hi, hj]
        _ = _ := (row_eq_indicator_sum (fun _ : Unit => A i ∩ A j) ()).symm

theorem incidence_second_moment_bound (A : ι → Finset α) (k : ℝ)
    (hk : 0 ≤ k)
    (hinter : ∀ i j, i ≠ j → ((A i ∩ A j).card : ℝ) ≤ k) :
    ∑ p, columnDegree A p ^ 2 ≤
      totalIncidences A + k * (Fintype.card ι : ℝ) ^ 2 := by
  classical
  rw [sum_columns_sq]
  calc
    (∑ i, ∑ j, ((A i ∩ A j).card : ℝ)) ≤
        ∑ i, ∑ j, ((if i = j then ((A i).card : ℝ) else 0) + k) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases h : i = j
      · subst j
        simp only [Finset.inter_self, ite_true]
        linarith
      · simpa [h] using hinter i j h
    _ = totalIncidences A + k * (Fintype.card ι : ℝ) ^ 2 := by
      simp [Finset.sum_add_distrib, totalIncidences, pow_two]
      ring

theorem incidence_cauchy_bound (A : ι → Finset α) (k : ℝ)
    (hk : 0 ≤ k)
    (hinter : ∀ i j, i ≠ j → ((A i ∩ A j).card : ℝ) ≤ k) :
    totalIncidences A ^ 2 ≤ (Fintype.card α : ℝ) *
      (totalIncidences A + k * (Fintype.card ι : ℝ) ^ 2) := by
  calc
    totalIncidences A ^ 2 = (∑ p, columnDegree A p) ^ 2 := by
      rw [totalIncidences_eq_sum_columns]
    _ ≤ (Fintype.card α : ℝ) * ∑ p, columnDegree A p ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := columnDegree A))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (incidence_second_moment_bound A k hk hinter) (by positivity)

theorem totalIncidences_le_twice_card (A : ι → Finset α) (k s : ℝ)
    (hk : 0 ≤ k) (hs : 0 ≤ s)
    (hrow : ∀ i, s ≤ ((A i).card : ℝ))
    (hinter : ∀ i j, i ≠ j → ((A i ∩ A j).card : ℝ) ≤ k)
    (hgap : 2 * k * (Fintype.card α : ℝ) ≤ s ^ 2) :
    totalIncidences A ≤ 2 * (Fintype.card α : ℝ) := by
  have hR : 0 ≤ totalIncidences A := Finset.sum_nonneg (by intros; positivity)
  have hb : (Fintype.card ι : ℝ) * s ≤ totalIncidences A := by
    simpa [totalIncidences] using
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i))
  have hsq : ((Fintype.card ι : ℝ) * s) ^ 2 ≤ totalIncidences A ^ 2 :=
    sq_le_sq₀ (by positivity) hR |>.mpr hb
  have hscaled := mul_le_mul_of_nonneg_right hgap
    (sq_nonneg (Fintype.card ι : ℝ))
  have hcs := incidence_cauchy_bound A k hk hinter
  nlinarith

end Ostmann.QuadraticCenter

end OAI
