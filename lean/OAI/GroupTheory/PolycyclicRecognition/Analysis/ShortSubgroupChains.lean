import OAI.GroupTheory.PolycyclicRecognition.Algebra.CayleyWordMaps
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialEnergyScales

namespace OAI

/-! # Short strict subgroup chains force superpolynomial growth

This is the counting step for the cyclic-kernel finite-generation argument:
a new conjugate at every window gives a linearly short new subgroup element,
and binary products then give exponentially many points in a quadratic ball.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset Filter
open scoped Topology
variable {G : Type*} [Group G] [DecidableEq G]

def binaryProducts (a : ℕ → G) : ℕ → Finset G
  | 0 => {1}
  | n + 1 => binaryProducts a n ∪ (binaryProducts a n).image (a n * ·)

theorem binaryProducts_mem (H : ℕ → Subgroup G) (hH : ∀ n, H n ≤ H (n + 1))
    (a : ℕ → G) (ha : ∀ n, a n ∈ H (n + 1)) (n : ℕ) :
    ∀ x ∈ binaryProducts a n, x ∈ H n := by
  induction n with
  | zero =>
    intro x hx
    have hx' : x = 1 := by simpa [binaryProducts] using hx
    rw [hx']
    exact (H 0).one_mem
  | succ n ih =>
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact hH n (ih x hx)
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact (H (n + 1)).mul_mem (ha n) (hH n (ih y hy))

theorem binaryProducts_card (H : ℕ → Subgroup G) (hH : ∀ n, H n ≤ H (n + 1))
    (a : ℕ → G) (ha : ∀ n, a n ∈ H (n + 1)) (hne : ∀ n, a n ∉ H n) (n : ℕ) :
    (binaryProducts a n).card = 2 ^ n := by
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    have hd : Disjoint (binaryProducts a n) ((binaryProducts a n).image (a n * ·)) := by
      apply disjoint_left.mpr
      intro x hx hx'
      obtain ⟨y, hy, he⟩ := mem_image.mp hx'
      have hmem := (H n).mul_mem (binaryProducts_mem H hH a ha n x hx)
        ((H n).inv_mem (binaryProducts_mem H hH a ha n y hy))
      have hEq : x * y⁻¹ = a n := by rw [← he]; simp
      exact hne n (hEq ▸ hmem)
    rw [binaryProducts, card_union_of_disjoint hd,
      card_image_of_injective _ (by intro x y h; exact mul_left_cancel h), ih, pow_succ]
    ring

theorem binaryProducts_word_bound (S : Finset G) (L : ℕ) (a : ℕ → G)
    (ha : ∀ n, a n ∈ wordBall S (L * (n + 1))) (n : ℕ) :
    binaryProducts a n ⊆ wordBall S (L * n ^ 2) := by
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact wordBall_mono S (Nat.mul_le_mul_left L (by gcongr; omega)) (ih hx)
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      apply wordBall_mono S _ (mul_mem_wordBall (ha n) (ih hy))
      nlinarith

theorem polynomial_growth_forbids_short_strict_chain
    (S : Finset G) (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (H : ℕ → Subgroup G) (hH : ∀ n, H n ≤ H (n + 1)) (L : ℕ) :
    ¬(∀ n, ∃ a, a ∈ H (n + 1) ∧ a ∉ H n ∧ a ∈ wordBall S (L * (n + 1))) := by
  intro hex
  choose a ha hne hlen using hex
  obtain ⟨C, d, hvol⟩ := hvol
  have hcount (n : ℕ) : 2 ^ n ≤ C * (1 + L * n ^ 2) ^ d := by
    calc
      _ = (binaryProducts a n).card := (binaryProducts_card H hH a ha hne n).symm
      _ ≤ (wordBall S (L * n ^ 2)).card := card_le_card (binaryProducts_word_bound S L a hlen n)
      _ ≤ _ := hvol _
  have hb (n : ℕ) : 1 ≤ ((C : ℝ) * (1 + (L : ℝ)) ^ d) *
      ((1 + (n : ℝ)) ^ (2 * d) * (1 / 2 : ℝ) ^ n) := by
    have hc : (2 : ℝ) ^ n ≤ (C : ℝ) * (1 + (L : ℝ) * (n : ℝ) ^ 2) ^ d := by
      exact_mod_cast hcount n
    have hp : 1 + (L : ℝ) * (n : ℝ) ^ 2 ≤
        (1 + (L : ℝ)) * (1 + (n : ℝ)) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) L, Nat.cast_nonneg (α := ℝ) n,
        sq_nonneg (n : ℝ), mul_nonneg (Nat.cast_nonneg (α := ℝ) L) (Nat.cast_nonneg (α := ℝ) n)]
    calc
      1 = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by rw [← mul_pow]; norm_num
      _ ≤ ((C : ℝ) * (1 + (L : ℝ) * (n : ℝ) ^ 2) ^ d) * (1 / 2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ ((C : ℝ) * ((1 + (L : ℝ)) * (1 + (n : ℝ)) ^ 2) ^ d) * (1 / 2 : ℝ) ^ n := by
        gcongr
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have ht : Tendsto (fun n : ℕ => ((C : ℝ) * (1 + (L : ℝ)) ^ d) *
      ((1 + (n : ℝ)) ^ (2 * d) * (1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_add_one_pow_mul_geometric (2 * d) (q := 1 / 2)
        (by norm_num) (by norm_num)).const_mul ((C : ℝ) * (1 + (L : ℝ)) ^ d)
  have hh : (1 : ℝ) ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hb)
  norm_num at hh

end PolycyclicRecognition

end

end OAI
