import Mathlib

namespace OAI

namespace LargeIndependentSets
open scoped BigOperators

theorem rational_simplex_approximation {J : Type*} [Fintype J] [Nonempty J]
    (q : J → ℝ) (hq : (∀ coordinate, 0 ≤ q coordinate) ∧ ∑ coordinate, q coordinate = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : J → ℚ, ((∀ coordinate, 0 ≤ p coordinate) ∧ ∑ coordinate, p coordinate = 1) ∧
      ∀ b : J → ℝ, (∀ j, 0 ≤ b j ∧ b j ≤ 1) →
        ∑ j, (p j : ℝ) * b j ≤ ∑ j, q j * b j + ε := by
  classical
  let t := ε / ((Fintype.card J : ℝ) + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  have ha (j : J) : ∃ a : ℚ, 0 ≤ a ∧ (a : ℝ) ≤ q j ∧ q j - a < t := by
    by_cases hz : q j = 0
    · exact ⟨0, le_rfl, by simp [hz], by simpa [hz] using ht⟩
    · have hp : 0 < q j := lt_of_le_of_ne (hq.1 j) (Ne.symm hz)
      obtain ⟨a, hal, har⟩ := exists_rat_btwn (show max 0 (q j - t) < q j from
        max_lt hp (sub_lt_self _ ht))
      refine ⟨a, ?_, har.le, ?_⟩
      · exact_mod_cast (le_max_left 0 (q j - t)).trans hal.le
      · have h := (le_max_right 0 (q j - t)).trans_lt hal
        linarith
  choose a ha0 haq hae using ha
  have hsum : ∑ j, (a j : ℝ) ≤ 1 :=
    (Finset.sum_le_sum (fun j _ => haq j)).trans_eq hq.2
  have hsumQ : ∑ j, a j ≤ 1 := by exact_mod_cast hsum
  let i₀ : J := Classical.arbitrary J
  let p : J → ℚ := fun j => a j + if j = i₀ then 1 - ∑ i, a i else 0
  have hp : (∀ coordinate, 0 ≤ p coordinate) ∧ ∑ coordinate, p coordinate = 1 := by
    constructor
    · intro j
      apply add_nonneg (ha0 j)
      split_ifs <;> linarith
    · simp [p, Finset.sum_add_distrib]
  have hdef : 1 - ∑ j, (a j : ℝ) < ε := by
    have he := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hae j).le)
    rw [Finset.sum_sub_distrib, hq.2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
    have hden : (0 : ℝ) < (Fintype.card J : ℝ) + 1 := by positivity
    have hid : t * ((Fintype.card J : ℝ) + 1) = ε := by
      exact div_mul_cancel₀ ε (ne_of_gt hden)
    have hlt : (Fintype.card J : ℝ) * t < ε := by nlinarith
    exact he.trans_lt hlt
  refine ⟨p, hp, ?_⟩
  intro b hb
  have hmain : ∑ j, (a j : ℝ) * b j ≤ ∑ j, q j * b j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (haq j) (hb j).1)
  have hformula : ∑ j, (p j : ℝ) * b j =
      (∑ j, (a j : ℝ) * b j) + (1 - ∑ j, (a j : ℝ)) * b i₀ := by
    have he (j : J) : (p j : ℝ) * b j = (a j : ℝ) * b j +
        if j = i₀ then (1 - ∑ i, (a i : ℝ)) * b i₀ else 0 := by
      by_cases h : j = i₀
      · subst j; simp only [p, ite_true, Rat.cast_add, Rat.cast_sub,
          Rat.cast_one, Rat.cast_sum]; ring
      · simp [p, h]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp
  rw [hformula]
  have hextra := mul_le_mul_of_nonneg_left (hb i₀).2 (sub_nonneg.mpr hsum)
  simp only [mul_one] at hextra
  linarith

end LargeIndependentSets

end OAI
