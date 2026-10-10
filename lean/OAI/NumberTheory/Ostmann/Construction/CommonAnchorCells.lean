import OAI.NumberTheory.Ostmann.Tree.CellGroupExponentialCost

namespace OAI

/-! # Fixing the two anchor-cell indices per depth before the target words -/
namespace Ostmann
open scoped Classical BigOperators

theorem common_bounded_anchor_cells (E : Finset ℕ) (hE : E.Nonempty) (k B : ℕ)
    (anchor : ℕ → (Fin k × Bool) → ℕ)
    (hbound : ∀ a ∈ E, ∀ j, anchor a j ≤ B) :
    ∃ a₀ ∈ E, ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
      E.card ≤ (B + 1) ^ (2 * k) * S.card ∧ ∀ a ∈ S, anchor a = anchor a₀ := by
  let q : ℕ → (Fin k × Bool) → Fin (B + 1) := fun a j =>
    if ha : a ∈ E then ⟨anchor a j, Nat.lt_succ_of_le (hbound a ha j)⟩ else 0
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ
    (fun v => (E.filter (fun a => q a = v)).card) Finset.univ_nonempty
  let S := E.filter (fun a => q a = v)
  have hSE : S ⊆ E := Finset.filter_subset _ _
  have hcard : E.card ≤ (B + 1) ^ (2 * k) * S.card := by
    calc
      E.card = ∑ v : (Fin k × Bool) → Fin (B + 1), (E.filter (fun a => q a = v)).card := by
        simpa using (Finset.card_eq_sum_card_fiberwise (s := E) (t := Finset.univ)
          (fun a _ => Finset.mem_univ (q a)))
      _ ≤ ∑ _v : (Fin k × Bool) → Fin (B + 1), S.card :=
        Finset.sum_le_sum (fun u hu => hv u hu)
      _ = _ := by simp [Fintype.card_prod, Nat.mul_comm]
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    by_contra! hz
    have he : S.card = 0 := Nat.eq_zero_of_le_zero hz
    rw [he, Nat.mul_zero] at hcard
    exact Nat.not_le_of_gt hE.card_pos hcard
  obtain ⟨a₀, ha₀⟩ := hS
  refine ⟨a₀, hSE ha₀, S, hSE, ⟨a₀, ha₀⟩, hcard, ?_⟩
  intro a ha
  have he : q a = q a₀ :=
    (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp ha₀).2.symm
  funext j
  have hj := congrArg Fin.val (congrFun he j)
  simpa only [q, dite_eq_left (hSE ha), dite_eq_left (hSE ha₀)] using hj

/-- The anchor pigeonhole has an absolute exponential rate when its fixed
number of slots is below the bulk scale. -/
theorem anchor_cell_cost (k B : ℕ) (C L z m : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hsize : (2 * k : ℕ) ≤ z)
    (hB : (B + 1 : ℕ) ≤ Real.exp (C * L)) (hm : z * L ≤ 2 * m) :
    (((B + 1) ^ (2 * k) : ℕ) : ℝ) ≤ Real.exp (2 * C * m) := by
  rw [Nat.cast_pow]
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hB (2 * k)).trans
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hsize (mul_nonneg hC hL)
  have hm' := mul_le_mul_of_nonneg_left hm hC
  nlinarith only [hh, hm']

end Ostmann

end OAI
