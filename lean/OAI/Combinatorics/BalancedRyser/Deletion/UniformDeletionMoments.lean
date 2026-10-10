import OAI.Combinatorics.BalancedRyser.Deletion.UniformDeletionSurvival
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.UniformDeletion

variable {F : Type*} [Field F] [DecidableEq F]

theorem eval_eq_iff_joining_direction (p r : Point F) (hne : p ≠ r)
    (d : Direction F) :
    lineEval d p = lineEval d r ↔ d = (joiningLine p r).1 := by
  constructor
  · intro h
    have hl : (d, lineEval d p) = joiningLine p r :=
      eq_of_two_common_points p r hne _ _ rfl h.symm
        (onLine_joiningLine_left p r) (onLine_joiningLine_right p r)
    exact congrArg Prod.fst hl
  · intro h
    rw [h]
    exact (onLine_joiningLine_left p r).trans (onLine_joiningLine_right p r).symm

theorem card_forbidden_pair (p r : Point F) (hne : p ≠ r) (d : Direction F) :
    (forbiddenOffsets {p, r} d).card =
      if d = (joiningLine p r).1 then 1 else 2 := by
  classical
  simp only [forbiddenOffsets, Finset.image_insert, Finset.image_singleton]
  by_cases hd : d = (joiningLine p r).1
  · rw [ite_eq_left hd, (eval_eq_iff_joining_direction p r hne d).mpr hd]
    simp
  · rw [ite_eq_right hd]
    exact Finset.card_pair (fun h => hd ((eval_eq_iff_joining_direction p r hne d).mp h))

variable [Fintype F]

theorem pair_survival (p r : Point F) (hne : p ≠ r)
    (k : ℕ) (hk : k ≤ Fintype.card F) :
    deletionEventProbability (law k hk)
      (fun D => p ∈ uncoveredBy D.val ∧ r ∈ uncoveredBy D.val) =
      (((Fintype.card F - 1).choose k : ℝ) / ((Fintype.card F).choose k : ℝ)) *
        ((((Fintype.card F - 2).choose k : ℝ) / ((Fintype.card F).choose k : ℝ)) ^
          Fintype.card F) := by
  classical
  have hprob := law_surviving_probability {p, r} k hk
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at hprob
  rw [hprob]
  let d₀ := (joiningLine p r).1
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Direction F))
    (fun d => ((Fintype.card F - (forbiddenOffsets {p, r} d).card).choose k : ℝ) /
      ((Fintype.card F).choose k : ℝ)) (Finset.mem_univ d₀)]
  rw [card_forbidden_pair p r hne d₀, ite_eq_left rfl]
  congr 1
  have hprod : (∏ d ∈ (Finset.univ : Finset (Direction F)).erase d₀,
      ((Fintype.card F - (forbiddenOffsets {p, r} d).card).choose k : ℝ) /
        ((Fintype.card F).choose k : ℝ)) =
      ∏ _d ∈ (Finset.univ : Finset (Direction F)).erase d₀,
        ((Fintype.card F - 2).choose k : ℝ) / ((Fintype.card F).choose k : ℝ) := by
    apply Finset.prod_congr rfl
    intro d hd
    rw [card_forbidden_pair p r hne d, ite_eq_right (Finset.mem_erase.mp hd).1]
  rw [hprod]
  simp [Direction, d₀, div_pow]

theorem expected_core_sq_sum {k : ℕ} (Q : PMF (DeletionSet F k)) :
    (∑ D, (Q D).toReal * (((uncoveredBy D.val).card : ℝ) ^ 2)) =
      ∑ p : Point F, ∑ r : Point F,
        deletionEventProbability Q
          (fun D => p ∈ uncoveredBy D.val ∧ r ∈ uncoveredBy D.val) := by
  classical
  have hsq (D : DeletionSet F k) :
      ((uncoveredBy D.val).card : ℝ) ^ 2 =
        ∑ p : Point F, ∑ r : Point F,
          if p ∈ uncoveredBy D.val ∧ r ∈ uncoveredBy D.val then (1 : ℝ) else 0 := by
    simp_rw [ite_and, Finset.sum_ite_irrel]
    simp [pow_two]
  simp_rw [hsq, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  unfold deletionEventProbability
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro D _
  split_ifs <;> rfl

theorem expected_core_sq (k : ℕ) (hk : k ≤ Fintype.card F) :
    (∑ D, (law k hk D).toReal * (((uncoveredBy D.val).card : ℝ) ^ 2)) =
      (Fintype.card F : ℝ) ^ 2 *
        (1 - (k : ℝ) / Fintype.card F) ^ (Fintype.card F + 1) +
      (Fintype.card F : ℝ) ^ 2 * ((Fintype.card F : ℝ) ^ 2 - 1) *
        ((1 - (k : ℝ) / Fintype.card F) *
          ((((Fintype.card F - 2).choose k : ℝ) / ((Fintype.card F).choose k : ℝ)) ^
            Fintype.card F)) := by
  classical
  let a : ℝ := (1 - (k : ℝ) / Fintype.card F) ^ (Fintype.card F + 1)
  let b : ℝ := (1 - (k : ℝ) / Fintype.card F) *
    ((((Fintype.card F - 2).choose k : ℝ) / ((Fintype.card F).choose k : ℝ)) ^
      Fintype.card F)
  have hinner (p : Point F) :
      (∑ r : Point F, deletionEventProbability (law k hk)
        (fun D => p ∈ uncoveredBy D.val ∧ r ∈ uncoveredBy D.val)) =
      a + ((Fintype.card (Point F) - 1 : ℕ) : ℝ) * b := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Point F))
      (fun r => deletionEventProbability (law k hk)
        (fun D => p ∈ uncoveredBy D.val ∧ r ∈ uncoveredBy D.val))
      (Finset.mem_univ p)]
    have hdiag : deletionEventProbability (law k hk)
        (fun D => p ∈ uncoveredBy D.val ∧ p ∈ uncoveredBy D.val) = a := by
      simpa [a] using point_survival_eq p k hk
    rw [hdiag]
    congr 1
    calc
      (∑ r ∈ (Finset.univ : Finset (Point F)).erase p,
        deletionEventProbability (law k hk)
          (fun D => p ∈ uncoveredBy D.val ∧ r ∈ uncoveredBy D.val)) =
          ∑ _r ∈ (Finset.univ : Finset (Point F)).erase p, b := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [pair_survival p r (Ne.symm (Finset.mem_erase.mp hr).1) k hk,
          one_offset_ratio k hk]
      _ = _ := by simp
  rw [expected_core_sq_sum]
  simp_rw [hinner]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Nat.cast_sub (Fintype.card_pos (α := Point F)), Nat.cast_one]
  simp only [Point, Fintype.card_prod, Nat.cast_mul, a, b]
  ring

end Balanced.UniformDeletion

end

end OAI
