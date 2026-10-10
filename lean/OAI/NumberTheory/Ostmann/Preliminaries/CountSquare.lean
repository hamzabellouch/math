import OAI.NumberTheory.Ostmann.Preliminaries.CountGrowth
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeBlock
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeBlockUpper

namespace OAI

open scoped Pointwise
namespace Ostmann.Decomposition

def swap (d : Decomposition) : Decomposition where
  A := d.B
  B := d.A
  infinite_A := d.infinite_B
  infinite_B := d.infinite_A
  cutoff := d.cutoff
  prime_iff n hn := by rw [add_comm d.B d.A]; exact d.prime_iff n hn

end Ostmann.Decomposition
namespace Ostmann.Preliminaries
open Filter
open scoped BigOperators

noncomputable def tailElements (A : Set ℕ) (L X : ℕ) : Finset ℕ := by
  classical
  exact (elementsUpTo A X).filter (fun a => L < a)

@[simp] theorem mem_tailElements {A : Set ℕ} {L X a : ℕ} :
    a ∈ tailElements A L X ↔ a ∈ A ∧ a ≤ X ∧ L < a := by
  classical
  simp only [tailElements, Finset.mem_filter, mem_elementsUpTo, and_assoc]

theorem countUpTo_le_tail_card (A : Set ℕ) (L X : ℕ) :
    countUpTo A X ≤ (tailElements A L X).card + (L + 1) := by
  classical
  have hsub : elementsUpTo A X ⊆ tailElements A L X ∪ Finset.range (L + 1) := by
    intro a ha
    obtain ⟨hA, hX⟩ := mem_elementsUpTo.mp ha
    by_cases hL : L < a
    · exact Finset.mem_union.mpr (Or.inl (mem_tailElements.mpr ⟨hA, hX, hL⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_range.mpr (by omega)))
  exact (Finset.card_le_card hsub).trans (by simpa using
    (Finset.card_union_le (tailElements A L X) (Finset.range (L + 1))))

noncomputable def countSieveConstant : ℝ := 96 / (Real.log 2 / 2) ^ 2

theorem countSieveConstant_pos : 0 < countSieveConstant := by
  have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  unfold countSieveConstant
  positivity

theorem residueReciprocalSum_nonneg (S : Set ℕ) (Q : ℕ) :
    0 ≤ residueReciprocalSum S Q := by
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
    (by positivity)

theorem eventually_count_square_le_H (d : Decomposition) :
    ∀ᶠ Q : ℕ in atTop,
      (countUpTo d.A (Q ^ 2) : ℝ) ≤
        countSieveConstant * Q * Real.log Q * residueReciprocalSum d.B Q + Q + d.cutoff + 1 := by
  classical
  filter_upwards [eventually_actual_residue_H_lower d, eventually_ge_atTop 2] with Q hH hQ
  let U := tailElements d.A (Q + d.cutoff) (Q ^ 2)
  have hqr : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hl : 0 < Real.log (Q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hc : 0 < (Real.log 2 / 2) ^ 2 := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    positivity
  have hU : (U.card : ℝ) ≤ countSieveConstant * Q * Real.log Q * residueReciprocalSum d.B Q := by
    by_cases hUn : U.Nonempty
    · have h := hH U hUn
        (fun a ha => (mem_tailElements.mp ha).1)
        (fun a ha => (mem_tailElements.mp ha).2.2)
        (fun a ha => (mem_tailElements.mp ha).2.1)
      have hd : 0 < 96 * (Q : ℝ) * Real.log Q := by positivity
      have hh := (div_le_iff₀ hd).mp h
      have hg : (U.card : ℝ) ≤
          (96 * Q * Real.log Q * residueReciprocalSum d.B Q) / (Real.log 2 / 2) ^ 2 :=
        (le_div_iff₀ hc).mpr (by nlinarith [hh])
      simpa only [countSieveConstant, div_mul_eq_mul_div] using hg
    · have he : U.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hUn)
      rw [he, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg countSieveConstant_pos.le hqr.le) hl.le)
        (residueReciprocalSum_nonneg _ _)
  have hcount : (countUpTo d.A (Q ^ 2) : ℝ) ≤ U.card + ((Q : ℝ) + d.cutoff + 1) := by
    exact_mod_cast countUpTo_le_tail_card d.A (Q + d.cutoff) (Q ^ 2)
  linarith

end Ostmann.Preliminaries

end OAI
