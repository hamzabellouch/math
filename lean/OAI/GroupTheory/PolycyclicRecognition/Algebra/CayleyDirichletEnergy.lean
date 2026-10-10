import OAI.GroupTheory.PolycyclicRecognition.Analysis.CayleyWordBallAlgebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

/-! # Discrete path energy and variance on Cayley balls

These are the finite-sum ingredients of the Cayley-graph Poincare estimate
in Kleiner, JAMS 23 (2010), Section 2. No harmonic-function theorem is assumed.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

def cayleyDirichletEnergy (S F : Finset G) (f : G → ℝ) : ℝ :=
  ∑ x ∈ F, ∑ s ∈ S, (f (x * s) - f x) ^ 2

omit [DecidableEq G] in
theorem cayleyDirichletEnergy_nonneg (S F : Finset G) (f : G → ℝ) :
    0 ≤ cayleyDirichletEnergy S F f :=
  sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))

omit [DecidableEq G] in
theorem cayleyDirichletEnergy_mono (S : Finset G) {A B : Finset G}
    (hAB : A ⊆ B) (f : G → ℝ) :
    cayleyDirichletEnergy S A f ≤ cayleyDirichletEnergy S B f :=
  sum_le_sum_of_subset_of_nonneg hAB (fun _ _ _ => sum_nonneg (fun _ _ => sq_nonneg _))

theorem finite_path_energy_bound (p : ℕ → ℝ) (n : ℕ) :
    (p n - p 0) ^ 2 ≤ (n : ℝ) * ∑ i ∈ range n, (p (i + 1) - p i) ^ 2 := by
  have ht : ∑ i ∈ range n, (p (i + 1) - p i) = p n - p 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; ring
  have h := sum_mul_sq_le_sq_mul_sq (range n) (fun i => p (i + 1) - p i) (fun _ => (1 : ℝ))
  simpa only [mul_one, ht, one_pow, sum_const, card_range, nsmul_eq_mul, mul_comm] using h

omit [Group G] [DecidableEq G] in
theorem sum_pairwise_sq_sub (F : Finset G) (f : G → ℝ) :
    (∑ x ∈ F, ∑ y ∈ F, (f x - f y) ^ 2) =
      2 * (F.card : ℝ) * (∑ x ∈ F, f x ^ 2) - 2 * (∑ x ∈ F, f x) ^ 2 := by
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib,
    sum_const, nsmul_eq_mul, ← mul_sum, ← sum_mul]
  ring

omit [Group G] [DecidableEq G] in
theorem finite_variance_identity (F : Finset G) (hF : F.Nonempty) (f : G → ℝ) :
    (∑ x ∈ F, (f x - (∑ y ∈ F, f y) / F.card) ^ 2) =
      (∑ x ∈ F, ∑ y ∈ F, (f x - f y) ^ 2) / (2 * F.card) := by
  have hn : (F.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (card_ne_zero.mpr hF)
  rw [sum_pairwise_sq_sub]
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, div_eq_mul_inv,
    sum_const, nsmul_eq_mul, ← mul_sum, ← sum_mul]
  field_simp [hn]
  ring

theorem translated_edge_sum_le_energy
    (S A F : Finset G) (f : G → ℝ) (t s : G) (hs : s ∈ S)
    (hAF : ∀ x ∈ A, x * t ∈ F) :
    (∑ x ∈ A, (f (x * t * s) - f (x * t)) ^ 2) ≤ cayleyDirichletEnergy S F f := by
  calc
    _ = ∑ z ∈ A.image (fun x => x * t), (f (z * s) - f z) ^ 2 := by
      rw [sum_image]
      intro x _ y _ hxy
      exact mul_right_cancel hxy
    _ ≤ ∑ z ∈ F, (f (z * s) - f z) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (by
        rintro z hz
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
        exact hAF x hx) (fun _ _ _ => sq_nonneg _)
    _ ≤ cayleyDirichletEnergy S F f :=
      sum_le_sum (fun z _ => single_le_sum
        (f := fun s => (f (z * s) - f z) ^ 2) (fun _ _ => sq_nonneg _) hs)

theorem word_path_energy_sum_le (S : Finset G) (f : G → ℝ)
    (l : List G) (hl : ∀ s ∈ l, s ∈ S) (R : ℕ) :
    (∑ x ∈ wordBall S R, (f (x * l.prod) - f x) ^ 2) ≤
      (l.length : ℝ) ^ 2 * cayleyDirichletEnergy S (wordBall S (R + l.length)) f := by
  have hedge (i : ℕ) (hi : i ∈ range l.length) :
      (∑ x ∈ wordBall S R,
        (f (x * (l.take (i + 1)).prod) - f (x * (l.take i).prod)) ^ 2) ≤
        cayleyDirichletEnergy S (wordBall S (R + l.length)) f := by
    have hi' : i < l.length := mem_range.mp hi
    rw [List.prod_take_succ l i hi']
    simp_rw [← mul_assoc]
    apply translated_edge_sum_le_energy S _ _ f (l.take i).prod l[i]
      (hl _ (List.getElem_mem hi'))
    intro x hx
    exact wordBall_mono S (Nat.add_le_add_left (Nat.le_of_lt hi') R)
      (mul_mem_wordBall hx (word_prefix_mem_wordBall hl i))
  calc
    _ ≤ ∑ x ∈ wordBall S R,
        (l.length : ℝ) * ∑ i ∈ range l.length,
          (f (x * (l.take (i + 1)).prod) - f (x * (l.take i).prod)) ^ 2 := by
      apply sum_le_sum
      intro x _
      simpa only [List.take_length, List.take_zero, List.prod_nil, mul_one] using
        finite_path_energy_bound (fun i => f (x * (l.take i).prod)) l.length
    _ = (l.length : ℝ) * ∑ i ∈ range l.length, ∑ x ∈ wordBall S R,
          (f (x * (l.take (i + 1)).prod) - f (x * (l.take i).prod)) ^ 2 := by
      rw [← mul_sum, sum_comm]
    _ ≤ (l.length : ℝ) * ∑ _i ∈ range l.length,
        cayleyDirichletEnergy S (wordBall S (R + l.length)) f :=
      mul_le_mul_of_nonneg_left (sum_le_sum hedge) (Nat.cast_nonneg _)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

end PolycyclicRecognition

end

end OAI
