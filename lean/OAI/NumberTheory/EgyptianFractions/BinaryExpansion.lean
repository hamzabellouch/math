import Mathlib

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Binary digits give a short expansion whenever a large power of two
is available as a divisor of the denominator. -/
theorem binary_unit_fraction_list (u M a : ℕ) (huM : u < M)
    (hu : u < 2 ^ (a + 1)) (hdiv : 2 ^ a ∣ M) :
    ∃ l : List ℕ, (∀ d ∈ l, 2 ≤ d) ∧ l.length ≤ a + 1 ∧
      (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = (u : ℚ) / M := by
  let l := u.bitIndices.map (fun i => M / 2 ^ i)
  have hi : ∀ i ∈ u.bitIndices, i ≤ a := by
    intro i hi
    have hp := (Nat.two_pow_le_of_mem_bitIndices hi).trans_lt hu
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hp
    omega
  have hd : ∀ i ∈ u.bitIndices, 2 ^ i ∣ M := by
    intro i h
    exact (Nat.pow_dvd_pow 2 (hi i h)).trans hdiv
  have hM : (M : ℚ) ≠ 0 := by
    exact_mod_cast (show M ≠ 0 by omega)
  refine ⟨l, ?_, ?_, ?_⟩
  · intro d hdmem
    obtain ⟨i, himem, rfl⟩ := List.mem_map.mp hdmem
    have hpow : 2 ^ i ≤ u := Nat.two_pow_le_of_mem_bitIndices himem
    have hp : 0 < 2 ^ i := by positivity
    have hm : 2 ^ i < M := hpow.trans_lt huM
    have hmul := Nat.mul_div_cancel' (hd i himem)
    by_contra hlt
    have hle : M / 2 ^ i ≤ 1 := by omega
    have := Nat.mul_le_mul_left (2 ^ i) hle
    omega
  · change (u.bitIndices.map _).length ≤ _
    rw [List.length_map, ← List.toFinset_card_of_nodup Nat.bitIndices_nodup]
    calc
      u.bitIndices.toFinset.card ≤ (Finset.range (a + 1)).card := by
        apply Finset.card_le_card
        intro i himem
        have := hi i (List.mem_toFinset.mp himem)
        simpa using this
      _ = a + 1 := Finset.card_range _
  · change ((u.bitIndices.map (fun i => M / 2 ^ i)).map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = _
    simp only [List.map_map, Function.comp_def]
    have heq : u.bitIndices.map (fun i => (1 : ℚ) / (M / 2 ^ i : ℕ)) =
        u.bitIndices.map (fun i => (2 : ℚ) ^ i * (M : ℚ)⁻¹) := by
      apply List.map_congr_left
      intro i himem
      have hp : ((2 ^ i : ℕ) : ℚ) ≠ 0 := by positivity
      rw [Nat.cast_div (hd i himem) hp, one_div_div]
      simp [div_eq_mul_inv]
    rw [heq, List.sum_map_mul_right]
    have hsum : (u.bitIndices.map (fun i => (2 : ℚ) ^ i)).sum = (u : ℚ) := by
      have h := congrArg (fun n : ℕ => (n : ℚ)) (Nat.sum_map_two_pow_bitIndices u)
      simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def, Nat.cast_pow, Nat.cast_ofNat] using h
    rw [hsum, div_eq_mul_inv]

end Problem337

end OAI
