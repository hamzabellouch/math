import OAI.Combinatorics.EditApproximation.Refinement.PhysicalOnlineLocality
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The query scale window has length controlled by the refinement
factor, independently of the number of dyadic scales below N. -/

namespace EditApproximation

open Finset



theorem dyadicQueryWindow_length_le (N C : ℕ) (w a F : ℚ)
    (ha : 1 ≤ a) (hF : 1 ≤ F)
    (hbudget : 128 * a * F ≤ (2 : ℚ) ^ C) :
    (dyadicQueryWindow N w a F).length ≤ C + 1 := by
  let keep : ℕ → Bool := fun e => decide (w / (16 * F) ≤ (2 ^ e : ℕ) ∧
    ((2 ^ e : ℕ) : ℚ) ≤ 8 * a * w)
  let indices := ((List.range (Nat.log 2 N + 1)).filter keep).toFinset
  have hlength : (dyadicQueryWindow N w a F).length = indices.card := by
    simp only [dyadicQueryWindow, dyadicScales, List.filter_map, List.length_map]
    exact (List.toFinset_card_of_nodup
      ((show (List.range (Nat.log 2 N + 1)).Nodup from List.nodup_range).filter keep)).symm
  rw [hlength]
  by_cases hnonempty : indices.Nonempty
  · let first := indices.min' hnonempty
    have hfirst : first ∈ indices := Finset.min'_mem _ _
    have hfirstKeep : w / (16 * F) ≤ (2 ^ first : ℕ) ∧ ((2 ^ first : ℕ) : ℚ) ≤ 8 * a * w :=
      of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hfirst)).2
    have hFpos : 0 < F := lt_of_lt_of_le zero_lt_one hF
    have hwfirst : w ≤ 16 * F * (2 ^ first : ℕ) := by
      nlinarith only [(div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hfirstKeep.1]
    have hsub : indices ⊆ Finset.Icc first (first + C) := by
      intro e he
      have hkeep : w / (16 * F) ≤ (2 ^ e : ℕ) ∧ ((2 ^ e : ℕ) : ℚ) ≤ 8 * a * w :=
        of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp he)).2
      have hmul := mul_le_mul_of_nonneg_left hwfirst (show 0 ≤ 8 * a by positivity)
      have hpower := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℚ) (2 ^ first))
      have hbound : ((2 ^ e : ℕ) : ℚ) ≤ (2 : ℚ) ^ C * (2 ^ first : ℕ) := by
        nlinarith only [hkeep.2, hmul, hpower]
      have hboundN : 2 ^ e ≤ 2 ^ (first + C) := by
        have heq : (2 : ℚ) ^ C * (2 ^ first : ℕ) = ((2 ^ (first + C) : ℕ) : ℚ) := by
          push_cast
          rw [pow_add]
          ring
        rw [heq] at hbound
        exact_mod_cast hbound
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ he,
        (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hboundN⟩
    have hcard := Finset.card_le_card hsub
    have hinterval : (Finset.Icc first (first + C)).card = C + 1 := by rw [Nat.card_Icc]; omega
    rwa [hinterval] at hcard
  · simpa only [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty] using Nat.zero_le (C + 1)

end EditApproximation

end OAI
