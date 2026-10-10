import OAI.Computability.UniqueGames.Games.RoundingLemmas

namespace OAI

section

/-!
The actual largest-remainder routine on a uniform occurrence distribution.

For `h > 0` occurrences, each weight has numerator one and denominator `h`.
Choosing tolerance `1 / C` gives `Q = C * h`. Every quota is the integer `C`,
so the sorting order is immaterial: there is no deficit to allocate. The exact
output list contains `C` copies of each original occurrence, in original order.

This is a conditional specialization of the rounding algorithm. It does not
assert that a particular preceding matrix reduction produces uniform weights,
nor does it assert a runtime certificate for a general sorting algorithm.
-/

namespace UniqueGamesTheorem.MachineUniformRounding

open scoped BigOperators
open UniqueGamesTheorem.Explicit.Rounding

theorem denominator_uniform (h C : Nat) : denominator h 1 C = C * h := by
  simp [denominator, IntegerRounding,
    UniqueGamesTheorem.Reduction.WeightRounding.ceilQuotient, Nat.mul_comm]

theorem denominator_uniform_eq_ceil (h C : Nat) (hC : 0 < C) :
    C * h = Nat.ceil ((h : ℚ) / (1 / (C : ℚ))) := by
  simpa only [denominator_uniform, Nat.cast_one] using
    denominator_eq_ceil h 1 C (by omega) hC

theorem uniform_mass (h : Nat) : (∑ _ : Fin h, (1 : Nat)) = h := by simp

theorem scaled_quota_uniform (h C : Nat) (hh : 0 < h) :
    (denominator h 1 C : ℚ) * (1 / (h : ℚ)) = C := by
  have hn : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [denominator_uniform]
  push_cast
  field_simp [hn]

theorem floorCount_uniform (h C : Nat) (hh : 0 < h) (i : Fin h) :
    floorCount (C * h) h (fun _ => 1) i = C := by
  simpa [floorCount, Nat.mul_comm] using Nat.mul_div_cancel_left C hh

theorem remainder_uniform (h C : Nat) (i : Fin h) :
    remainder (C * h) h (fun _ => 1) i = 0 := by
  simp [remainder]

theorem deficit_uniform (h C : Nat) (hh : 0 < h) :
    deficit (C * h) h (fun _ : Fin h => 1) = 0 := by
  simp only [deficit, floorCount_uniform h C hh]
  simp [Nat.mul_comm]

theorem incremented_uniform (h C : Nat) (hh : 0 < h) :
    incremented (C * h) h (fun _ : Fin h => 1) = ∅ := by
  simp [incremented, deficit_uniform h C hh]

/-- The concrete largest-remainder multiplicity is precisely `C`. -/
theorem count_uniform (h C : Nat) (hh : 0 < h) (i : Fin h) :
    count (denominator h 1 C) h (fun _ => 1) i = C := by
  rw [denominator_uniform]
  simp [count, floorCount_uniform h C hh, incremented_uniform h C hh]

theorem copies_uniform (h C : Nat) (hh : 0 < h) :
    copies (denominator h 1 C) h (fun _ : Fin h => 1) =
      (List.ofFn fun i : Fin h => List.replicate C i).flatten := by
  simp only [copies, count_uniform h C hh]

theorem copies_uniform_length (h C : Nat) (hh : 0 < h) :
    (copies (denominator h 1 C) h (fun _ : Fin h => 1)).length = C * h := by
  rw [copies_length _ _ _ hh (uniform_mass h), denominator_uniform]

/-- Each normalized rounded weight equals its original uniform weight exactly. -/
theorem normalized_count_uniform (h C : Nat) (hh : 0 < h) (hC : 0 < C)
    (i : Fin h) :
    (count (denominator h 1 C) h (fun _ => 1) i : ℚ) /
      denominator h 1 C = 1 / (h : ℚ) := by
  have hn : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hCn : (C : ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  rw [count_uniform h C hh, denominator_uniform]
  push_cast
  field_simp [hn, hCn]

/-- Therefore every satisfaction predicate has zero rounding error. -/
theorem selected_weights_exact (h C : Nat) (hh : 0 < h) (hC : 0 < C)
    (keep : Fin h → Bool) :
    (∑ i, if keep i then
      (count (denominator h 1 C) h (fun _ => 1) i : ℚ) / denominator h 1 C else 0) =
      ∑ i, if keep i then 1 / (h : ℚ) else 0 := by
  simp_rw [normalized_count_uniform h C hh hC]

end UniqueGamesTheorem.MachineUniformRounding

end

end OAI
