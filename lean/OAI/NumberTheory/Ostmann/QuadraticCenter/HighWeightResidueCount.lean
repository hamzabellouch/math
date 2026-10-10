import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem coprime_residue_multiple_card_le (T : Finset ℕ) {L r a X : ℕ}
    (hcop : L.Coprime r) (hres : ∀ n ∈ T, Nat.ModEq L n a)
    (hdiv : ∀ n ∈ T, r ∣ n) (hupper : ∀ n ∈ T, n ≤ X) :
    T.card ≤ X / (L * r) + 1 := by
  classical
  have hc := Finset.card_le_card_of_injOn (s := T) (t := Finset.range (X / (L * r) + 1))
    (fun n : ℕ => n / (L * r)) ?_ ?_
  · simpa only [Finset.card_range] using hc
  · intro n hn
    apply Finset.mem_range.mpr
    exact lt_of_le_of_lt (Nat.div_le_div_right (hupper n hn)) (Nat.lt_succ_self _)
  · intro n hn m hm hquot
    change n / (L * r) = m / (L * r) at hquot
    have hnmL := (hres n hn).trans (hres m hm).symm
    have hnmr : Nat.ModEq r n m :=
      (Nat.modEq_zero_iff_dvd.mpr (hdiv n hn)).trans
        (Nat.modEq_zero_iff_dvd.mpr (hdiv m hm)).symm
    have hnm := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hnmL, hnmr⟩
    change n % (L * r) = m % (L * r) at hnm
    have hnn := Nat.mod_add_div n (L * r)
    have hmm := Nat.mod_add_div m (L * r)
    rw [hnm, hquot] at hnn
    exact hnn.symm.trans hmm

theorem coprime_residue_multiple_card_real_le (T : Finset ℕ) {L r a X : ℕ}
    (hL : 0 < L) (hr : 0 < r) (hcop : L.Coprime r)
    (hres : ∀ n ∈ T, Nat.ModEq L n a) (hdiv : ∀ n ∈ T, r ∣ n)
    (hupper : ∀ n ∈ T, n ≤ 2 * X) (hdensity : L * r ≤ X) :
    (T.card : ℝ) ≤ 3 * (X : ℝ) / ((L : ℝ) * r) := by
  have hcount := coprime_residue_multiple_card_le T hcop hres hdiv hupper
  have hq : 0 < L * r := Nat.mul_pos hL hr
  have hcast : (T.card : ℝ) ≤ ((2 * X / (L * r) : ℕ) : ℝ) + 1 := by exact_mod_cast hcount
  have hfloor : ((2 * X / (L * r) : ℕ) : ℝ) ≤ (2 * (X : ℝ)) / ((L : ℝ) * r) := by
    have hn := Nat.div_mul_le_self (2 * X) (L * r)
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (L : ℝ) * r)).mpr
    exact_mod_cast hn
  have hone : (1 : ℝ) ≤ (X : ℝ) / ((L : ℝ) * r) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (L : ℝ) * r)).mpr
    simp only [one_mul]
    exact_mod_cast hdensity
  calc
    (T.card : ℝ) ≤ (2 * (X : ℝ)) / ((L : ℝ) * r) + 1 := hcast.trans (add_le_add hfloor le_rfl)
    _ ≤ (2 * (X : ℝ)) / ((L : ℝ) * r) + (X : ℝ) / ((L : ℝ) * r) := add_le_add le_rfl hone
    _ = 3 * (X : ℝ) / ((L : ℝ) * r) := by ring

theorem half_divisor_density {L r X : ℕ} (hr : r ^ 2 ≤ 2 * X)
    (hX : 2 * L ^ 2 ≤ X) : L * r ≤ X := by
  have h1 := Nat.mul_le_mul_left (L ^ 2) hr
  have h2 := Nat.mul_le_mul_left X hX
  nlinarith

end Ostmann.QuadraticCenter

end OAI
