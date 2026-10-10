import OAI.GroupTheory.PolycyclicRecognition.Algebra.CayleyDirichletEnergy
import Mathlib.Tactic.Positivity

namespace OAI

/-! # A discrete Poincare inequality with the local volume ratio

This is the vertex version of the path-counting argument in Kleiner,
JAMS 23 (2010), Theorem 2.2. It requires no doubling assumption.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

theorem word_translate_energy_le (S : Finset G) (f : G → ℝ)
    (R n : ℕ) {g : G} (hg : g ∈ wordBall S n) :
    (∑ x ∈ wordBall S R, (f (x * g) - f x) ^ 2) ≤
      (n : ℝ) ^ 2 * cayleyDirichletEnergy S (wordBall S (R + n)) f := by
  obtain ⟨l, hl, hs, rfl⟩ := (mem_wordBall_iff S n g).mp hg
  exact (word_path_energy_sum_le S f l hs R).trans
    (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg l.length) (Nat.cast_le.mpr hl) 2)
      (cayleyDirichletEnergy_mono S (wordBall_mono S (Nat.add_le_add_left hl R)) f)
      (cayleyDirichletEnergy_nonneg _ _ _) (sq_nonneg _))

theorem pairwise_wordBall_energy_le (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (f : G → ℝ) (R : ℕ) :
    (∑ x ∈ wordBall S R, ∑ y ∈ wordBall S R, (f x - f y) ^ 2) ≤
      ((wordBall S (2 * R)).card : ℝ) * (2 * (R : ℝ)) ^ 2 *
        cayleyDirichletEnergy S (wordBall S (3 * R)) f := by
  have hone (x : G) (hx : x ∈ wordBall S R) :
      (∑ y ∈ wordBall S R, (f x - f y) ^ 2) ≤
        ∑ z ∈ wordBall S (2 * R), (f (x * z) - f x) ^ 2 := by
    calc
      _ = ∑ z ∈ (wordBall S R).image (fun y => x⁻¹ * y), (f (x * z) - f x) ^ 2 := by
        rw [sum_image]
        · apply sum_congr rfl
          intro y _
          simp only [mul_inv_cancel_left]
          ring
        · intro a _ b _ hab
          exact mul_left_cancel hab
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by
        rintro z hz
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hz
        simpa only [two_mul] using mul_mem_wordBall (inv_mem_wordBall hS hx) hy)
        (fun _ _ _ => sq_nonneg _)
  calc
    _ ≤ ∑ x ∈ wordBall S R, ∑ z ∈ wordBall S (2 * R), (f (x * z) - f x) ^ 2 :=
      sum_le_sum hone
    _ = ∑ z ∈ wordBall S (2 * R), ∑ x ∈ wordBall S R, (f (x * z) - f x) ^ 2 := sum_comm
    _ ≤ ∑ _z ∈ wordBall S (2 * R), (2 * (R : ℝ)) ^ 2 *
        cayleyDirichletEnergy S (wordBall S (3 * R)) f := by
      apply sum_le_sum
      intro z hz
      convert word_translate_energy_le S f R (2 * R) hz using 1
      simp only [Nat.cast_mul, Nat.cast_ofNat, show R + 2 * R = 3 * R by omega]
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

theorem cayley_wordBall_poincare (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (f : G → ℝ) (R : ℕ) :
    (∑ x ∈ wordBall S R,
      (f x - (∑ y ∈ wordBall S R, f y) / (wordBall S R).card) ^ 2) ≤
      2 * (R : ℝ) ^ 2 *
        (((wordBall S (2 * R)).card : ℝ) / (wordBall S R).card) *
        cayleyDirichletEnergy S (wordBall S (3 * R)) f := by
  have hn : ((wordBall S R).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (card_ne_zero.mpr ⟨1, one_mem_wordBall S R⟩)
  rw [finite_variance_identity _ ⟨1, one_mem_wordBall S R⟩]
  apply (div_le_div_of_nonneg_right (pairwise_wordBall_energy_le S hS f R)
    (by positivity : (0 : ℝ) ≤ 2 * (wordBall S R).card)).trans_eq
  field_simp [hn]

end PolycyclicRecognition

end

end OAI
