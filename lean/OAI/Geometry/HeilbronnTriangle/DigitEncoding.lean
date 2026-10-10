import Mathlib

namespace OAI


namespace Problem355.DigitEncoding

theorem matched_indices {T a b c : ℕ} (ha : a < T) (hc : c < T)
    (h : a + T * b = (T + 1) * c) : a = c ∧ b = c := by
  have h' : a + T * b = c + T * c := by nlinarith
  have hmod := congrArg (fun x : ℕ => x % T) h'
  have hac : a = c := by
    simpa [Nat.add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] using hmod
  subst a
  constructor
  · rfl
  · have hT : 0 < T := Nat.zero_lt_of_lt hc
    nlinarith

theorem no_small_congruent {h τ s t : ℤ} (hs : τ < |s|)
    (hcenter : 2 * |s| < h) (hcong : t ≡ s [ZMOD h]) : τ < |t| := by
  by_contra ht
  have ht' : |t| ≤ τ := le_of_not_gt ht
  obtain ⟨m, hm⟩ := Int.modEq_iff_add_fac.mp hcong
  by_cases hm0 : m = 0
  · simp only [hm0, mul_zero, add_zero] at hm
    subst s
    omega
  · have hmabs : 1 ≤ |m| := by
      have := abs_pos.mpr hm0
      omega
    have hh : 0 < h := lt_of_le_of_lt (by positivity : 0 ≤ 2 * |s|) hcenter
    have hprod : h ≤ |h * m| := by
      rw [abs_mul, abs_of_pos hh]
      nlinarith
    have htri : |s - t| ≤ |s| + |t| := abs_sub s t
    have heq : s - t = h * m := by omega
    rw [heq] at htri
    omega

end Problem355.DigitEncoding

end OAI
