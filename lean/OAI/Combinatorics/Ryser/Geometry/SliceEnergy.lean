import OAI.Combinatorics.Ryser.Geometry.ProjectionPair
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample

open scoped BigOperators

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

def sliceCount (U : Finset (Point F)) (d : Direction F) (t : F) : ℕ :=
  (U.filter (fun p => projection d p = t)).card

noncomputable def sliceEnergy (U : Finset (Point F)) (d : Direction F) : ℝ :=
  (∑ t : F, ((sliceCount U d t : ℝ) -
    (U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2) / (Fintype.card F : ℝ)

theorem sliceCount_le_card_field (U : Finset (Point F)) (d : Direction F) (t : F) :
    sliceCount U d t ≤ Fintype.card F := by
  rw [← card_projection_fiber d t]
  apply Finset.card_le_card
  intro p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩

theorem sliceCount_eq_sum_indicator (U : Finset (Point F)) (d : Direction F) (t : F) :
    (sliceCount U d t : ℝ) =
      ∑ p ∈ U, if projection d p = t then (1 : ℝ) else 0 := let _ := instFintypeF; by
  exact Finset.natCast_card_filter _ _

theorem sum_sliceCount (U : Finset (Point F)) (d : Direction F) :
    (∑ t : F, (sliceCount U d t : ℝ)) = (U.card : ℝ) := by
  classical
  simp_rw [sliceCount_eq_sum_indicator]
  rw [Finset.sum_comm]
  simp

private theorem sum_projection_indicator_mul (d : Direction F) (p p' : Point F) :
    (∑ t : F, (if projection d p = t then (1 : ℝ) else 0) *
      (if projection d p' = t then (1 : ℝ) else 0)) =
      if projection d p = projection d p' then (1 : ℝ) else 0 := by
  classical
  calc
    _ = (if projection d p = projection d p then (1 : ℝ) else 0) *
        (if projection d p' = projection d p then (1 : ℝ) else 0) := by
      apply Finset.sum_eq_single (projection d p)
      · intro t _ ht
        simp [Ne.symm ht]
      · simp
    _ = _ := by simp [eq_comm]

theorem sum_sliceCount_sq (U : Finset (Point F)) (d : Direction F) :
    (∑ t : F, (sliceCount U d t : ℝ) ^ 2) =
      ∑ p ∈ U, ∑ p' ∈ U,
        if projection d p = projection d p' then (1 : ℝ) else 0 := by
  classical
  simp_rw [sliceCount_eq_sum_indicator, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p' hp'
  exact sum_projection_indicator_mul d p p'

theorem sum_all_sliceCount_sq (U : Finset (Point F)) :
    (∑ d : Direction F, ∑ t : F, (sliceCount U d t : ℝ) ^ 2) =
      (U.card : ℝ) ^ 2 + (Fintype.card F : ℝ) * (U.card : ℝ) := by
  classical
  simp_rw [sum_sliceCount_sq]
  rw [Finset.sum_comm]
  calc
    (∑ p ∈ U, ∑ d : Direction F, ∑ p' ∈ U,
        if projection d p = projection d p' then (1 : ℝ) else 0) =
        ∑ p ∈ U, ∑ p' ∈ U,
          if p = p' then (Fintype.card F : ℝ) + 1 else 1 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p' hp'
      exact sum_projection_eq_indicator p p'
    _ = ∑ p ∈ U, ((Fintype.card F : ℝ) + (U.card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = ∑ p' ∈ U, ((if p' = p then (Fintype.card F : ℝ) else 0) + 1) := by
          apply Finset.sum_congr rfl
          intro p' hp'
          by_cases h : p' = p
          · subst p'
            simp
          · simp [h, Ne.symm h]
        _ = _ := by simp [Finset.sum_add_distrib, hp]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem sliceEnergy_nonneg (U : Finset (Point F)) (d : Direction F) :
    0 ≤ sliceEnergy U d := by
  unfold sliceEnergy
  positivity

theorem sliceEnergy_eq (U : Finset (Point F)) (d : Direction F) :
    sliceEnergy U d =
      (∑ t : F, (sliceCount U d t : ℝ) ^ 2) / (Fintype.card F : ℝ) -
        (U.card : ℝ) ^ 2 / (Fintype.card F : ℝ) ^ 2 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  have hcenter :
      (∑ t : F, ((sliceCount U d t : ℝ) -
        (U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2) =
      (∑ t : F, (sliceCount U d t : ℝ) ^ 2) -
        (2 * ((U.card : ℝ) / (Fintype.card F : ℝ))) * (U.card : ℝ) +
        (Fintype.card F : ℝ) * ((U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2 := by
    calc
      _ = ∑ t : F, ((sliceCount U d t : ℝ) ^ 2 -
          (2 * ((U.card : ℝ) / (Fintype.card F : ℝ))) * (sliceCount U d t : ℝ) +
          ((U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, sum_sliceCount, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
  unfold sliceEnergy
  rw [hcenter]
  field_simp
  ring

theorem sum_sliceEnergy (U : Finset (Point F)) :
    (∑ d : Direction F, sliceEnergy U d) =
      (U.card : ℝ) - (U.card : ℝ) ^ 2 / (Fintype.card F : ℝ) ^ 2 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  simp_rw [sliceEnergy_eq]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_all_sliceCount_sq]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_direction, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem sum_sliceEnergy_le_card (U : Finset (Point F)) :
    (∑ d : Direction F, sliceEnergy U d) ≤ (U.card : ℝ) := by
  rw [sum_sliceEnergy]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem sum_sliceEnergy_le_sq_card (U : Finset (Point F)) :
    (∑ d : Direction F, sliceEnergy U d) ≤ (Fintype.card F : ℝ) ^ 2 := by
  apply (sum_sliceEnergy_le_card U).trans
  have h := U.card_le_univ
  rw [card_point] at h
  exact_mod_cast h

end RyserCoveringCounterexample

end OAI
