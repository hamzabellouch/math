import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryCodeBounds
import OAI.Combinatorics.EditApproximation.Binary.BinaryScaleGrid
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The physical scalar sources locate a dyadic scale by a counted scan.
The scan computes the original first index and works also for absent scales. -/

namespace EditApproximation



@[simp] theorem queryNaturalIndexWithWork_value (a : ℕ) (xs : List ℕ) :
    (queryNaturalIndexWithWork a xs).1 = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    unfold queryNaturalIndexWithWork
    by_cases hab : a = b
    · subst b
      rw [ite_eq_left ((naturalEqualWithWork_value a a).mpr rfl)]
      simp
    · rw [ite_eq_right (fun h => hab ((naturalEqualWithWork_value a b).mp h))]
      simp only [ih, List.idxOf_cons, beq_iff_eq]
      rw [ite_eq_right (Ne.symm hab)]

theorem queryNaturalIndexWithWork_cost (a B : ℕ) (ha : Nat.size a ≤ B)
    (xs : List ℕ) (hx : ∀ b ∈ xs, Nat.size b ≤ B) :
    (queryNaturalIndexWithWork a xs).2 ≤ 1 + xs.length * (8 * B + 4) := by
  induction xs with
  | nil => simp only [queryNaturalIndexWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl]
  | cons b xs ih =>
    have hc := naturalEqualWithWork_cost a b B ha (hx b (by simp))
    have ht := ih (fun c hc => hx c (List.mem_cons_of_mem b hc))
    simp only [queryNaturalIndexWithWork, List.length_cons]
    split <;> dsimp only
    · nlinarith only [hc, Nat.zero_le xs.length, Nat.zero_le B]
    · nlinarith only [hc, ht]



@[simp] theorem queryScaleDispatchWithWork_value (N b : ℕ) :
    (queryScaleDispatchWithWork N b).1 = (dyadicScales N).idxOf b := by
  simp only [queryScaleDispatchWithWork, queryNaturalIndexWithWork_value, dyadicScalesWithWork_value]

theorem dyadicScales_size_bound (N b : ℕ) (hb : b ∈ dyadicScales N) :
    Nat.size b ≤ Nat.size N + 1 := by
  rw [← dyadicScalesWithWork_value N] at hb
  simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.mem_map] at hb
  obtain ⟨e, he, rfl⟩ := hb
  rw [powerTwoWord_value, Nat.size_pow]
  have he' := List.mem_range.mp he
  rw [Nat.size_eq_bits_len] at he'
  omega

theorem queryScaleDispatchWithWork_cost (N b B : ℕ)
    (hN : Nat.size N ≤ B) (hb : Nat.size b ≤ B) :
    (queryScaleDispatchWithWork N b).2 ≤ 20 * (B + 2) ^ 2 := by
  have hs := dyadicScalesWithWork_cost N
  have hl : (dyadicScalesWithWork N).1.length ≤ B + 1 := by
    simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.length_map, List.length_range]
    rw [Nat.size_eq_bits_len]
    omega
  have hi := queryNaturalIndexWithWork_cost b (B + 1) (by omega) (dyadicScalesWithWork N).1
    (fun c hc => (dyadicScales_size_bound N c (by simpa only [dyadicScalesWithWork_value] using hc)).trans (by omega))
  change (dyadicScalesWithWork N).2 + (queryNaturalIndexWithWork b (dyadicScalesWithWork N).1).2 +
    (dyadicScalesWithWork N).1.length + 2 ≤ _
  nlinarith only [hs, hi, hl, hN, Nat.zero_le B]

end EditApproximation

end OAI
