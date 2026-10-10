import OAI.NumberTheory.Ostmann.QuadraticCenter.IncidenceBase

namespace OAI

namespace Ostmann.QuadraticCenter
open Finset

theorem descFactorial_le_pow_mul (r lo hi : ℕ) (h : lo ≤ hi) :
    r.descFactorial hi ≤ r ^ (hi - lo) * r.descFactorial lo := by
  rw [← Nat.descFactorial_mul_descFactorial h]
  exact Nat.mul_le_mul_right _ ((Nat.descFactorial_le_pow _ _).trans
    (Nat.pow_le_pow_left (Nat.sub_le _ _) _))

variable {ι α : Type*} [Fintype ι]

theorem card_incident_tuples [DecidableEq α] (A : ι → Finset α) (k : ℕ) :
    Fintype.card (Σ i, Fin k ↪ ↥(A i)) = ∑ i, (A i).card.descFactorial k := by
  classical
  simp [Fintype.card_sigma, Fintype.card_embedding_eq]

theorem small_rows_moment_bound (r : ι → ℕ) (lo hi t : ℕ) (h : lo ≤ hi) :
    (∑ i ∈ Finset.univ.filter (fun i => r i < t), (r i).descFactorial hi) ≤
      t ^ (hi - lo) * ∑ i, (r i).descFactorial lo := by
  classical
  calc
    (∑ i ∈ Finset.univ.filter (fun i => r i < t), (r i).descFactorial hi) ≤
        ∑ i ∈ Finset.univ.filter (fun i => r i < t),
          t ^ (hi - lo) * (r i).descFactorial lo := by
      apply Finset.sum_le_sum
      intro i hi'
      have hir : r i ≤ t := Nat.le_of_lt (Finset.mem_filter.mp hi').2
      exact (descFactorial_le_pow_mul (r i) lo hi h).trans
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hir _))
    _ = t ^ (hi - lo) *
        ∑ i ∈ Finset.univ.filter (fun i => r i < t), (r i).descFactorial lo := by
      rw [Finset.mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (by simp))

theorem high_rows_moment_lower (r : ι → ℕ) (lo hi t mass : ℕ)
    (h : lo ≤ hi)
    (hmass : mass + t ^ (hi - lo) * ∑ i, (r i).descFactorial lo ≤
      ∑ i, (r i).descFactorial hi) :
    mass ≤ ∑ i ∈ Finset.univ.filter (fun i => t ≤ r i), (r i).descFactorial hi := by
  classical
  have hsmall := small_rows_moment_bound r lo hi t h
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun i => r i < t) (f := fun i => (r i).descFactorial hi)
  simp only [not_lt] at hsplit
  omega

variable [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem moment_le_pow_mul_total [Fintype α] [DecidableEq α] (A : ι → Finset α) (n M : ℕ)
    (hmax : ∀ i, (A i).card ≤ M) :
    (∑ i, ((A i).card.descFactorial (n + 1) : ℝ)) ≤
      (M : ℝ) ^ n * totalIncidences A := by
  calc
    (∑ i, ((A i).card.descFactorial (n + 1) : ℝ)) ≤
        ∑ i, (M : ℝ) ^ n * ((A i).card : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hnat : (A i).card.descFactorial (n + 1) ≤ M ^ n * (A i).card := by
        calc
          (A i).card.descFactorial (n + 1) ≤ (A i).card ^ (n + 1) :=
            Nat.descFactorial_le_pow _ _
          _ = (A i).card ^ n * (A i).card := Nat.pow_succ _ _
          _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (hmax i) _)
      exact_mod_cast hnat
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem exists_large_row [Nonempty ι] (A : ι → Finset α)
    (n : ℕ) (k s mass : ℝ) (hk : 0 ≤ k) (hs : 0 ≤ s)
    (hrow : ∀ i, s ≤ ((A i).card : ℝ))
    (hinter : ∀ i j, i ≠ j → ((A i ∩ A j).card : ℝ) ≤ k)
    (hgap : 2 * k * (Fintype.card α : ℝ) ≤ s ^ 2)
    (hmass : mass ≤ ∑ i, ((A i).card.descFactorial (n + 1) : ℝ)) :
    ∃ i, mass ≤ 2 * (Fintype.card α : ℝ) * ((A i).card : ℝ) ^ n := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => (A i).card) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  have htotal := totalIncidences_le_twice_card A k s hk hs hrow hinter hgap
  calc
    mass ≤ ∑ i, ((A i).card.descFactorial (n + 1) : ℝ) := hmass
    _ ≤ ((A i).card : ℝ) ^ n * totalIncidences A :=
      moment_le_pow_mul_total A n (A i).card (fun j => hmax j (Finset.mem_univ _))
    _ ≤ ((A i).card : ℝ) ^ n * (2 * (Fintype.card α : ℝ)) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = _ := by ring

end Ostmann.QuadraticCenter

end OAI
