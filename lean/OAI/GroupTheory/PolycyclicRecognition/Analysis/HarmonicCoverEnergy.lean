import OAI.GroupTheory.PolycyclicRecognition.Analysis.CayleyBallCover
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBallQuadraticForms

namespace OAI

/-! # Energy control for the kernel of the ball-averaging map -/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

theorem sum_translatedWordBall (S : Finset G) (r : ℕ) (x : G) (f : G → ℝ) :
    (∑ y ∈ translatedWordBall S r x, f y) = ∑ y ∈ wordBall S r, f (x * y) := by
  exact sum_image (fun _ _ _ _ h => mul_left_cancel h)

theorem energy_translatedWordBall (S : Finset G) (r : ℕ) (x : G) (f : G → ℝ) :
    cayleyDirichletEnergy S (translatedWordBall S r x) f =
      cayleyDirichletEnergy S (wordBall S r) (fun y => f (x * y)) := by
  simp only [cayleyDirichletEnergy, sum_translatedWordBall, mul_assoc]

theorem translatedWordBall_zero_average_poincare (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (r : ℕ) (x : G) (f : G → ℝ)
    (hf : ∑ y ∈ translatedWordBall S r x, f y = 0) :
    (∑ y ∈ translatedWordBall S r x, (f y) ^ 2) ≤
      2 * (r : ℝ) ^ 2 * (((wordBall S (2 * r)).card : ℝ) / (wordBall S r).card) *
        cayleyDirichletEnergy S (translatedWordBall S (3 * r) x) f := by
  have h := cayley_wordBall_poincare S hS (fun y => f (x * y)) r
  rw [sum_translatedWordBall] at hf
  simpa only [hf, zero_div, sub_zero, sum_translatedWordBall,
    energy_translatedWordBall] using h

theorem wordBall_sum_le_cover (S : Finset G) (C : Finset G) (R t : ℕ)
    (hcover : ∀ x ∈ wordBall S R, ∃ y ∈ C, x ∈ translatedWordBall S t y)
    (w : G → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ wordBall S R, w x) ≤ ∑ y ∈ C, ∑ x ∈ translatedWordBall S t y, w x := by
  classical
  calc
    _ ≤ ∑ x ∈ wordBall S R, ∑ y ∈ C,
        if x ∈ translatedWordBall S t y then w x else 0 := by
      apply sum_le_sum
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hcover x hx
      have hn (z : G) (_hz : z ∈ C) :
          0 ≤ if x ∈ translatedWordBall S t z then w x else 0 := by
        split_ifs
        · exact hw x
        · exact le_rfl
      simpa only [ite_eq_left hxy] using single_le_sum hn hy
    _ = ∑ y ∈ C, ∑ x ∈ wordBall S R,
        if x ∈ translatedWordBall S t y then w x else 0 := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro y _
      rw [← sum_filter]
      exact sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_filter.mp hx).2)
        (fun x _ _ => hw x)

theorem wordBall_zero_averages_energy (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (C : Finset G) (r R t : ℕ)
    (hdis : (C : Set G).Pairwise (fun x y =>
      Disjoint (translatedWordBall S r x) (translatedWordBall S r y)))
    (hC : C ⊆ wordBall S R)
    (hcover : ∀ x ∈ wordBall S R, ∃ y ∈ C, x ∈ translatedWordBall S t y)
    (f : G → ℝ) (hf : ∀ y ∈ C, ∑ x ∈ translatedWordBall S t y, f x = 0) :
    wordBallQuadraticValue S R f ≤
      (2 * (t : ℝ) ^ 2 * (((wordBall S (2 * t)).card : ℝ) / (wordBall S t).card)) *
      (((wordBall S (3 * t + r)).card : ℝ) / (wordBall S r).card) *
      cayleyDirichletEnergy S (wordBall S (R + 3 * t)) f := by
  let P := 2 * (t : ℝ) ^ 2 * (((wordBall S (2 * t)).card : ℝ) / (wordBall S t).card)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  calc
    _ ≤ ∑ y ∈ C, ∑ x ∈ translatedWordBall S t y, (f x) ^ 2 :=
      wordBall_sum_le_cover S C R t hcover _ (fun x => sq_nonneg (f x))
    _ ≤ ∑ y ∈ C, P * cayleyDirichletEnergy S (translatedWordBall S (3 * t) y) f :=
      sum_le_sum (fun y hy => translatedWordBall_zero_average_poincare S hS t y f (hf y hy))
    _ = P * (∑ y ∈ C, cayleyDirichletEnergy S (translatedWordBall S (3 * t) y) f) :=
      (mul_sum ..).symm
    _ ≤ P * ((((wordBall S (3 * t + r)).card : ℝ) / (wordBall S r).card) *
        cayleyDirichletEnergy S (wordBall S (R + 3 * t)) f) := by
      apply mul_le_mul_of_nonneg_left _ hP
      exact sum_translatedWordBall_le_overlap S hS C r R (3 * t) hdis hC
        (fun x => ∑ s ∈ S, (f (x * s) - f x) ^ 2)
        (fun x => sum_nonneg (fun s _ => sq_nonneg (f (x * s) - f x)))
    _ = _ := by dsimp [P]; ring

def harmonicCoverFactor (S : Finset G) (r R t : ℕ) : ℝ :=
  (2 * (t : ℝ) ^ 2 * (((wordBall S (2 * t)).card : ℝ) / (wordBall S t).card)) *
    (((wordBall S (3 * t + r)).card : ℝ) / (wordBall S r).card) *
    (4 * (S.card : ℝ) * (1 / (R + 3 * t : ℕ)) ^ 2)

theorem harmonicCoverFactor_nonneg (S : Finset G) (r R t : ℕ) :
    0 ≤ harmonicCoverFactor S r R t := by
  unfold harmonicCoverFactor
  positivity

theorem harmonic_wordBall_zero_averages (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (C : Finset G) (r R t : ℕ) (hRt : 0 < R + 3 * t)
    (hdis : (C : Set G).Pairwise (fun x y =>
      Disjoint (translatedWordBall S r x) (translatedWordBall S r y)))
    (hC : C ⊆ wordBall S R)
    (hcover : ∀ x ∈ wordBall S R, ∃ y ∈ C, x ∈ translatedWordBall S t y)
    (f : G → ℝ) (hharm : CayleyHarmonic S f)
    (hf : ∀ y ∈ C, ∑ x ∈ translatedWordBall S t y, f x = 0) :
    wordBallQuadraticValue S R f ≤ harmonicCoverFactor S r R t *
      wordBallQuadraticValue S (2 * (R + 3 * t)) f := by
  have hcoef : 0 ≤ (2 * (t : ℝ) ^ 2 *
      (((wordBall S (2 * t)).card : ℝ) / (wordBall S t).card)) *
      (((wordBall S (3 * t + r)).card : ℝ) / (wordBall S r).card) := by positivity
  exact (wordBall_zero_averages_energy S hS C r R t hdis hC hcover f hf).trans
    ((mul_le_mul_of_nonneg_left
      (cayley_wordBall_reverse_poincare S hS hgen f hharm hRt) hcoef).trans_eq
        (by simp only [wordBallQuadraticValue, harmonicCoverFactor]; ring))

end PolycyclicRecognition

end

end OAI
