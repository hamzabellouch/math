import Mathlib

namespace OAI

namespace Ostmann.Arithmetic

def reversalNumerator {R : Type*} [CommRing R] (v w Hplus Hminus : R) : R :=
  v * Hminus - w * Hplus

theorem reversalNumerator_coprime {R : Type*} [CommRing R]
    {v w Hplus Hminus : R} (hH : IsCoprime Hplus Hminus)
    (hv : IsCoprime v Hplus) (hw : IsCoprime w Hminus) :
    IsCoprime (reversalNumerator v w Hplus Hminus) Hplus ∧
    IsCoprime (reversalNumerator v w Hplus Hminus) Hminus := by
  constructor
  · simpa only [reversalNumerator, IsCoprime.sub_mul_right_left_iff] using hv.mul_left hH.symm
  · simpa only [reversalNumerator, IsCoprime.mul_sub_right_left_iff] using hw.mul_left hH

theorem integral_reversal_inherited_coprime {R : Type*} [CommRing R]
    {v w Hplus Hminus s u p a : R}
    (hH : IsCoprime Hplus Hminus) (hv : IsCoprime v Hplus)
    (hw : IsCoprime w Hminus)
    (heq : reversalNumerator v w Hplus Hminus = s * u * p)
    (ha : a ∣ Hplus ∨ a ∣ Hminus) : IsCoprime p a ∧ IsCoprime u a := by
  have hN : IsCoprime (reversalNumerator v w Hplus Hminus) a := by
    obtain ⟨hplus,hminus⟩ := reversalNumerator_coprime hH hv hw
    exact ha.elim (fun h => hplus.of_isCoprime_of_dvd_right h)
      (fun h => hminus.of_isCoprime_of_dvd_right h)
  rw [heq] at hN
  exact ⟨hN.of_mul_left_right, hN.of_mul_left_left.of_mul_left_right⟩

theorem integral_reversal_iff {R : Type*} [CommRing R] {s u N : R}
    (h : IsCoprime s u) : (∃ p, N = s * u * p) ↔ s ∣ N ∧ u ∣ N := by
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨⟨u*p, by ring⟩, ⟨s*p, by ring⟩⟩
  · rintro ⟨hs,hu⟩
    exact h.mul_dvd hs hu

theorem prime_square_test {b N s u p : ℤ} (hb : Prime b)
    (hbs : ¬ b ∣ s) (hbu : b ∣ u) (hbu2 : ¬ b*b ∣ u)
    (hN : N = s*u*p) : (¬ b*b ∣ N) ↔ ¬ b ∣ p := by
  obtain ⟨u', hu'⟩ := hbu
  have hbu' : ¬ b ∣ u' := by
    intro h
    obtain ⟨z,rfl⟩ := h
    apply hbu2
    refine ⟨z, ?_⟩
    rw [hu']
    ring
  have hb0 : b ≠ 0 := hb.ne_zero
  rw [hN, hu']
  have heq : s * (b*u') * p = b * (s*u'*p) := by ring
  rw [heq, mul_dvd_mul_iff_left hb0]
  simp only [hb.dvd_mul, hbs, hbu', false_or]

end Ostmann.Arithmetic

end OAI
