import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace OAI

/-! # A primitive integral family after removing its common power of three -/
noncomputable section
namespace PolycyclicRecognition

theorem integerFamily_three_primitive {I : Type} (a : I → ℤ)
    (ha : ∃ i, a i ≠ 0) (h3 : ∀ i, (3 : ℤ) ∣ a i) :
    ∃ k : ℕ, 0 < k ∧ ∃ c : I → ℤ,
      (∀ i, a i = 3 ^ k * c i) ∧ ∃ i, ¬(3 : ℤ) ∣ c i := by
  classical
  obtain ⟨i, hi⟩ := ha
  have hex : ∃ n : ℕ, ¬∀ i, (3 : ℤ) ^ (n + 1) ∣ a i := by
    refine ⟨padicValNat 3 (a i).natAbs, ?_⟩
    intro h
    have hd := h i
    have hd' : (3 : ℕ) ^ (padicValNat 3 (a i).natAbs + 1) ∣ (a i).natAbs := by
      apply Int.natCast_dvd.mp
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hd
    exact pow_succ_padicValNat_not_dvd (p := 3) (Int.natAbs_ne_zero.mpr hi) hd'
  let k := Nat.find hex
  have hnot : ¬∀ i, (3 : ℤ) ^ (k + 1) ∣ a i := Nat.find_spec hex
  have hk : 0 < k := by
    by_contra h
    have he : k = 0 := by omega
    apply hnot
    simpa only [he, zero_add, pow_one] using h3
  have hd : ∀ i, (3 : ℤ) ^ k ∣ a i := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hmin := Nat.find_min hex (show j < Nat.find hex by change j < k; omega)
    have hprev : ∀ i, (3 : ℤ) ^ (j + 1) ∣ a i := not_not.mp hmin
    simpa only [hj] using hprev
  choose c hc using hd
  refine ⟨k, hk, c, hc, ?_⟩
  by_contra h
  have hall : ∀ i, (3 : ℤ) ∣ c i := by simpa only [not_exists, not_not] using h
  apply hnot
  intro j
  obtain ⟨b, hb⟩ := hall j
  refine ⟨b, ?_⟩
  rw [hc j, hb, pow_succ, mul_assoc]

end PolycyclicRecognition

end

end OAI
