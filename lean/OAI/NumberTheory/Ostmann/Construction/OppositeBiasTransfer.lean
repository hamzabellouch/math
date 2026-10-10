import Mathlib.Data.Finset.BooleanAlgebra
import OAI.NumberTheory.Ostmann.Preliminaries.TestFunctions

namespace OAI

/-! # Opposite empirical biases from complementary residue supports -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def residueTestMean {ι : Type*} (S : Finset ι) (f : ι → ℝ) : ℝ :=
  (∑ x ∈ S, f x) / S.card

theorem complementary_test_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (hsum : ∑ x, f x = 0) :
    residueTestMean Sᶜ f = -((S.card : ℝ) / Sᶜ.card) * residueTestMean S f := by
  have hsum' := Finset.sum_add_sum_compl S f
  rw [hsum] at hsum'
  have hs0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have hsc0 : (Sᶜ.card : ℝ) ≠ 0 := by exact_mod_cast hSc.card_ne_zero
  unfold residueTestMean
  field_simp
  nlinarith only [hsum']

theorem paired_test_means (S T : Finset ℕ) (f : ℕ → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hsum : (∑ r ∈ S, f r) + (∑ r ∈ T, f r) = 0) :
    residueTestMean T f = -((S.card : ℝ) / T.card) * residueTestMean S f := by
  have hs0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have ht0 : (T.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_ne_zero
  unfold residueTestMean
  field_simp
  nlinarith only [hsum]

theorem complementary_support_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (hSc : Sᶜ.Nonempty)
    (hthird : (Fintype.card ι : ℝ) / 3 ≤ S.card) :
    (1 / 2 : ℝ) ≤ (S.card : ℝ) / Sᶜ.card := by
  have hc : (0 : ℝ) < Sᶜ.card := by exact_mod_cast hSc.card_pos
  have hsplit : (S.card : ℝ) + Sᶜ.card = Fintype.card ι := by
    exact_mod_cast Finset.card_add_card_compl S
  apply (le_div_iff₀ hc).mpr
  linarith

/-- The same orientation gives positive empirical bias on one side and
negative empirical bias on the complementary side. -/
theorem exists_opposite_bias_orientation (u v x y r δ : ℝ)
    (hδ : 0 < δ) (hr : 1 / 2 ≤ r) (hu : δ ≤ |u|) (hv : v = -r * u)
    (hx : |x - u| ≤ δ / 8) (hy : |y - v| ≤ δ / 8) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ δ / 4 ≤ ε * x ∧ δ / 4 ≤ -ε * y := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  by_cases hu0 : 0 ≤ u
  · have hud : δ ≤ u := by simpa only [abs_of_nonneg hu0] using hu
    have hru : δ / 2 ≤ r * u := by
      have hh := mul_le_mul_of_nonneg_right hr hu0
      linarith
    refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · nlinarith
    · rw [hv] at hy'
      nlinarith
  · have hud : u ≤ -δ := by
      rw [abs_of_neg (lt_of_not_ge hu0)] at hu
      linarith
    have hru : r * u ≤ -δ / 2 := by
      have hh := mul_le_mul_of_nonpos_right hr (le_of_lt (lt_of_not_ge hu0))
      linarith
    refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · nlinarith
    · rw [hv] at hy'
      nlinarith

theorem complementary_empirical_bias {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (x y δ : ℝ) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (hsum : ∑ r, f r = 0) (hthird : (Fintype.card ι : ℝ) / 3 ≤ S.card)
    (hδ : 0 < δ) (hbias : δ ≤ |residueTestMean S f|)
    (hx : |x - residueTestMean S f| ≤ δ / 8)
    (hy : |y - residueTestMean Sᶜ f| ≤ δ / 8) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ δ / 4 ≤ ε * x ∧ δ / 4 ≤ -ε * y := by
  exact exists_opposite_bias_orientation _ _ _ _ _ _ hδ
    (complementary_support_ratio S hSc hthird) hbias (complementary_test_mean S f hS hSc hsum) hx hy

end Ostmann

end OAI
