import OAI.Computability.DepthThree.LanguageParameters

namespace OAI

namespace DepthThreeLowerBound

theorem cube_lt_iff_lt_hashDimension (d r : ℕ) :
    r ^ 3 < d ^ 2 ↔ r < hashDimension d := by
  by_cases hd : d = 0
  · subst d
    simp
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    constructor
    · intro h
      by_contra hn
      have hle : hashDimension d ≤ r := Nat.le_of_not_gt hn
      have hc := Nat.le_trans (hashDimension_cube_bound d)
        (Nat.pow_le_pow_left hle 3)
      omega
    · intro h
      by_contra hn
      have hc : d ^ 2 ≤ r ^ 3 := Nat.le_of_not_gt hn
      have hr : 0 < r := by
        by_contra hz
        have he : r = 0 := by omega
        have hp : 0 < d ^ 2 := Nat.pow_pos hdpos
        simp only [he, Nat.zero_pow (by decide : 0 < 3)] at hc
        omega
      have hm := hashDimension_minimal hdpos hr hc
      omega

theorem next_sixth_le_iff_lt_independenceOrder (d k : ℕ) (hk : Even k) :
    (k + 2) ^ 6 ≤ d ↔ k < independenceOrder d := by
  have hnext : Even (k + 2) := by
    obtain ⟨a, ha⟩ := hk
    exact ⟨a + 1, by omega⟩
  constructor
  · intro hp
    have hm := independenceOrder_greatest hnext hp
    omega
  · intro hlt
    have ht := independenceOrder_even d
    have hle : k + 2 ≤ independenceOrder d := by
      obtain ⟨a, ha⟩ := hk
      obtain ⟨b, hb⟩ := ht
      omega
    exact Nat.le_trans (Nat.pow_le_pow_left hle 6) (independenceOrder_pow_le d)

theorem cube_search_candidate_le_data {d r : ℕ} (h : r ≤ hashDimension d) : r ≤ d :=
  Nat.le_trans h (hashDimension_le d)

theorem sixth_search_candidate_le_data {d k : ℕ} (h : k ≤ independenceOrder d) : k ≤ d :=
  Nat.le_trans h (independenceOrder_le d)

end DepthThreeLowerBound

end OAI
