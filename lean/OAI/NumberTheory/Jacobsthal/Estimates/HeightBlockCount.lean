import OAI.NumberTheory.Jacobsthal.Primes.CanonicalTagPrimePartition

namespace OAI

namespace Erdos970


namespace ErdosLargeHeightBlocks

noncomputable def blockCount (C0 : ℤ) (R xi : ℝ) (H : ℕ) : ℕ :=
  max 1 ⌈xi*|(C0 : ℝ)|/(R*(H : ℝ))⌉₊

theorem blockCount_pos (C0 : ℤ) (R xi : ℝ) (H : ℕ) : 0 < blockCount C0 R xi H := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem blockCount_lower (C0 : ℤ) (R xi : ℝ) (H : ℕ) :
    xi*|(C0 : ℝ)|/(R*(H : ℝ)) ≤ (blockCount C0 R xi H : ℝ) := by
  apply (Nat.le_ceil _).trans
  unfold blockCount
  exact_mod_cast le_max_right 1 ⌈xi*|(C0 : ℝ)|/(R*(H : ℝ))⌉₊

theorem blockCount_upper (C0 : ℤ) (R xi : ℝ) (H : ℕ)
    (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) :
    (blockCount C0 R xi H : ℝ) ≤ 1+xi*|(C0 : ℝ)|/(R*(H : ℝ)) := by
  have hx : 0 ≤ xi*|(C0 : ℝ)|/(R*(H : ℝ)) := by positivity
  have hc := Nat.ceil_lt_add_one hx
  rw [blockCount,Nat.cast_max,Nat.cast_one]
  apply max_le <;> linarith

theorem blockCount_source_bound (C0 : ℤ) (R xi Z : ℝ) (H : ℕ)
    (hR : 0 < R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (hH : 0 < H) (hZ : 2 ≤ Z)
    (hsize : max (H : ℝ) (|(C0 : ℝ)|/R)/(H : ℝ) ≤ Z^12) :
    (blockCount C0 R xi H : ℝ) ≤ Z^13 := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hc : |(C0 : ℝ)|/(R*(H : ℝ)) ≤ Z^12 := by
    have h := (div_le_div_of_nonneg_right (le_max_right (H : ℝ) (|(C0 : ℝ)|/R)) hHr.le).trans hsize
    simpa only [div_div] using h
  have hx : xi*|(C0 : ℝ)|/(R*(H : ℝ)) ≤ Z^12 := by
    have h := mul_le_mul_of_nonneg_right hxi1 (show 0 ≤ |(C0 : ℝ)|/(R*(H : ℝ)) by positivity)
    have he : xi*|(C0 : ℝ)|/(R*(H : ℝ))=xi*(|(C0 : ℝ)|/(R*(H : ℝ))) := by ring
    rw [he]
    exact h.trans (by simpa only [one_mul] using hc)
  have hz0 : 0 ≤ Z := by linarith
  have hpow : 1 ≤ Z^12 := one_le_pow₀ (by linarith)
  have hzstep : 1+Z^12 ≤ Z^13 := by
    have hh := mul_le_mul_of_nonneg_right hZ (pow_nonneg hz0 12)
    rw [show Z*Z^12=Z^13 by ring] at hh
    linarith
  calc
    _ ≤ 1+xi*|(C0 : ℝ)|/(R*(H : ℝ)) := blockCount_upper C0 R xi H hR hxi hH
    _ ≤ 1+Z^12 := by linarith
    _ ≤ _ := hzstep

end ErdosLargeHeightBlocks


end Erdos970

end OAI
