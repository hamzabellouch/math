import Mathlib

namespace OAI

namespace Ostmann.Arithmetic.FrequencyPrecision

def product (frequencies : List ℤ) : ℕ := (frequencies.map Int.natAbs).prod

def modulus (frequencies : List ℤ) (depth : ℕ) : ℕ :=
  product frequencies ^ (depth+2)

theorem frequency_dvd_product {frequencies : List ℤ} {s : ℤ}
    (hs : s ∈ frequencies) : s.natAbs ∣ product frequencies :=
  List.dvd_prod (List.mem_map.mpr ⟨s,hs,rfl⟩)

theorem prime_coprime_modulus {p : ℕ} (hp : p.Prime) (frequencies : List ℤ)
    (hn : ∀ s ∈ frequencies, s ≠ 0) (hsize : ∀ s ∈ frequencies, s.natAbs < p)
    (depth : ℕ) : p.Coprime (modulus frequencies depth) := by
  apply Nat.Coprime.pow_right
  apply Nat.coprime_list_prod_right_iff.mpr
  intro n hmem
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hmem
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr (hn s hs)) hd
  exact (not_le.mpr (hsize s hs)) this

theorem cancel_coprime {m u a b : ℤ} (hu : IsCoprime m u)
    (h : u*a ≡ u*b [ZMOD m]) : a ≡ b [ZMOD m] := by
  apply Int.modEq_iff_dvd.mpr
  apply hu.dvd_of_dvd_mul_left
  have hh := Int.modEq_iff_dvd.mp h
  simpa only [mul_sub] using hh

theorem reversal_precision_step {R s u p q : ℤ} (n : ℕ)
    (hs : s ∣ R) (hs0 : s ≠ 0) (hu : IsCoprime u R)
    (h : s*u*p ≡ s*u*q [ZMOD R^(n+1)]) :
    p ≡ q [ZMOD R^n] := by
  have hmod : s*R^n ∣ R^(n+1) := by
    obtain ⟨t,ht⟩ := hs
    refine ⟨t,?_⟩
    rw [pow_succ,ht]
    ring
  have h' : s*(u*p) ≡ s*(u*q) [ZMOD s*R^n] := by
    simpa only [mul_assoc] using h.of_dvd hmod
  have h'' := Int.ModEq.mul_left_cancel' hs0 h'
  exact cancel_coprime hu.pow_right.symm h''

end Ostmann.Arithmetic.FrequencyPrecision

end OAI
