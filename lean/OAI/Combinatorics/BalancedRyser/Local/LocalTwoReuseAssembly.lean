import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Local.LocalDirectionAssignments
import OAI.Combinatorics.BalancedRyser.Local.LocalNoninjectiveContribution

namespace OAI

namespace Balanced.Local.TwoReuseAssembly

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
private theorem offsetProbability_mono {E G : MergedPairs F → Prop}
    (h : ∀ M, E M → G M) : offsetProbability E ≤ offsetProbability G := by
  unfold offsetProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro M _
  by_cases he : E M
  · simp only [he, h M he, ite_true, le_refl]
  · simp only [he, ite_false]
    split_ifs <;> norm_num

private theorem offsetProbability_nonneg (E : MergedPairs F → Prop) :
    0 ≤ offsetProbability E := by
  unfold offsetProbability
  positivity

theorem cross_count_scale_le (q : ℝ) (hq : 0 < q) (b : ℕ) (hb : 1 ≤ b) :
    (b : ℝ) * (4 * b - 2 : ℕ) * (q + 1) ^ (5 * b - 3) ≤
      (q + 1) ^ (5 * b - 2) * (4 * (b : ℝ) ^ 3 / q) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hsub : ((4 * b - 2 : ℕ) : ℝ) ≤ 4 * b := by
    exact_mod_cast Nat.sub_le (4 * b) 2
  have hcoef : (b : ℝ) * (4 * b - 2 : ℕ) ≤ 4 * (b : ℝ) ^ 3 := by
    calc
      (b : ℝ) * (4 * b - 2 : ℕ) ≤ (b : ℝ) * (4 * b) :=
        mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)
      _ ≤ 4 * (b : ℝ) ^ 3 := by nlinarith [sq_nonneg ((b : ℝ) - 1)]
  have hexp : 5 * b - 2 = (5 * b - 3) + 1 := by omega
  have hpower : (q + 1) ^ (5 * b - 3) ≤ (q + 1) ^ (5 * b - 2) / q := by
    apply (le_div_iff₀ hq).mpr
    rw [hexp, pow_succ]
    exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith) _)
  calc
    (b : ℝ) * (4 * b - 2 : ℕ) * (q + 1) ^ (5 * b - 3)
        ≤ (4 * (b : ℝ) ^ 3) * (q + 1) ^ (5 * b - 3) :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (by linarith) _)
    _ ≤ (4 * (b : ℝ) ^ 3) * ((q + 1) ^ (5 * b - 2) / q) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by ring

theorem noninjective_joint_sum_le {b : ℕ} (P : EqualityPattern b 2)
    (bits : Bits b) (p : Point F) (hb : 1 ≤ b)
    (halign : ∀ a : DirectionAssignment F b 2, Eligible P a →
      offsetProbability (Aligned P a bits p) =
        1 / (Fintype.card F : ℝ) ^ (4 * b)) :
    (∑ a : DirectionAssignment F b 2,
      if Eligible P a ∧ ¬ AllTokensDistinct a then
        offsetProbability (fun M => Aligned P a bits p M ∧
          AdmissibleBadCover P a bits p M) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
        (Fintype.card F : ℝ) ^ (4 * b) *
          (4 * (b : ℝ) ^ 3 / Fintype.card F) := by
  let S := (Finset.univ : Finset (DirectionAssignment F b 2)).filter
    (fun a => Eligible P a ∧ ¬ AllTokensDistinct a)
  have hpoint (a : DirectionAssignment F b 2) (ha : a ∈ S) :
      offsetProbability (fun M => Aligned P a bits p M ∧
        AdmissibleBadCover P a bits p M) ≤
          1 / (Fintype.card F : ℝ) ^ (4 * b) := by
    rw [← halign a (Finset.mem_filter.mp ha).2.1]
    exact offsetProbability_mono (fun _ h => h.1)
  have hc : (S.card : ℝ) ≤
      (b : ℝ) * (4 * b - 2 : ℕ) * (Fintype.card F + 1 : ℕ) ^ (5 * b - 3) := by
    exact_mod_cast card_eligible_not_allDistinct_two_le (F := F) hb P
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hs := cross_count_scale_le (Fintype.card F : ℝ) hq b hb
  calc
    _ = ∑ a ∈ S, offsetProbability (fun M => Aligned P a bits p M ∧
          AdmissibleBadCover P a bits p M) := by
      rw [Finset.sum_filter]
    _ ≤ ∑ _a ∈ S, 1 / (Fintype.card F : ℝ) ^ (4 * b) :=
      Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * (1 / (Fintype.card F : ℝ) ^ (4 * b)) := by simp
    _ ≤ ((b : ℝ) * (4 * b - 2 : ℕ) *
          (Fintype.card F + 1 : ℕ) ^ (5 * b - 3)) *
        (1 / (Fintype.card F : ℝ) ^ (4 * b)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ (((Fintype.card F : ℝ) + 1) ^ (5 * b - 2) *
          (4 * (b : ℝ) ^ 3 / Fintype.card F)) *
        (1 / (Fintype.card F : ℝ) ^ (4 * b)) := by
      push_cast
      exact mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by push_cast; ring

theorem injective_joint_sum_le_of_conditional {b : ℕ} (P : EqualityPattern b 2)
    (bits : Bits b) (p : Point F) (C : ℝ)
    (halign : ∀ a : DirectionAssignment F b 2, Eligible P a →
      offsetProbability (Aligned P a bits p) =
        1 / (Fintype.card F : ℝ) ^ (4 * b))
    (hbound : (∑ a : DirectionAssignment F b 2,
      if AllTokensDistinct a then
        conditionedOffsetProbability (Aligned P a bits p)
          (AdmissibleBadCover P a bits p) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
        (C * (b : ℝ) ^ 3 / Fintype.card F)) :
    (∑ a : DirectionAssignment F b 2,
      if AllTokensDistinct a then
        offsetProbability (fun M => Aligned P a bits p M ∧
          AdmissibleBadCover P a bits p M) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
        (Fintype.card F : ℝ) ^ (4 * b) *
          (C * (b : ℝ) ^ 3 / Fintype.card F) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have heq (a : DirectionAssignment F b 2) (ha : AllTokensDistinct a) :
      offsetProbability (fun M => Aligned P a bits p M ∧
        AdmissibleBadCover P a bits p M) =
      (1 / (Fintype.card F : ℝ) ^ (4 * b)) *
        conditionedOffsetProbability (Aligned P a bits p)
          (AdmissibleBadCover P a bits p) := by
    unfold conditionedOffsetProbability
    rw [halign a (allTokensDistinct_eligible P a ha)]
    field_simp
  calc
    _ = (1 / (Fintype.card F : ℝ) ^ (4 * b)) *
        ∑ a : DirectionAssignment F b 2,
          if AllTokensDistinct a then conditionedOffsetProbability
            (Aligned P a bits p) (AdmissibleBadCover P a bits p) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : AllTokensDistinct a
      · simp only [ha, ite_true, heq a ha]
      · simp only [ha, ite_false, mul_zero]
    _ ≤ (1 / (Fintype.card F : ℝ) ^ (4 * b)) *
        (((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
          (C * (b : ℝ) ^ 3 / Fintype.card F)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

theorem direction_sum_le_of_injective {b : ℕ} (P : EqualityPattern b 2)
    (bits : Bits b) (p : Point F) (hb : 1 ≤ b) (C : ℝ)
    (halign : ∀ a : DirectionAssignment F b 2, Eligible P a →
      offsetProbability (Aligned P a bits p) =
        1 / (Fintype.card F : ℝ) ^ (4 * b))
    (hbound : (∑ a : DirectionAssignment F b 2,
      if AllTokensDistinct a then
        conditionedOffsetProbability (Aligned P a bits p)
          (AdmissibleBadCover P a bits p) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
        (C * (b : ℝ) ^ 3 / Fintype.card F)) :
    (∑ a : DirectionAssignment F b 2,
      if Eligible P a then offsetProbability (fun M =>
        Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
        (Fintype.card F : ℝ) ^ (4 * b) *
          ((C + 4) * (b : ℝ) ^ 3 / Fintype.card F) := by
  let W : DirectionAssignment F b 2 → ℝ := fun a =>
    offsetProbability (fun M => Aligned P a bits p M ∧
      AdmissibleBadCover P a bits p M)
  have hsplit : (∑ a, if Eligible P a then W a else 0) =
      (∑ a, if AllTokensDistinct a then W a else 0) +
        ∑ a, if Eligible P a ∧ ¬ AllTokensDistinct a then W a else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : AllTokensDistinct a
    · simp only [ha, allTokensDistinct_eligible P a ha, ite_true,
        not_true_eq_false, and_false, ite_false, add_zero]
    · by_cases he : Eligible P a <;> simp [ha, he]
  change (∑ a, if Eligible P a then W a else 0) ≤ _
  rw [hsplit]
  have hi := injective_joint_sum_le_of_conditional P bits p C halign hbound
  have hc := sum_noninjective_badCover_le hb P bits p
  calc
    _ ≤ (((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
        (Fintype.card F : ℝ) ^ (4 * b) * (C * (b : ℝ) ^ 3 / Fintype.card F)) +
        (((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
        (Fintype.card F : ℝ) ^ (4 * b) * (4 * (b : ℝ) ^ 3 / Fintype.card F)) :=
      add_le_add hi hc
    _ = _ := by ring

universe u

def InjectiveTwoReuseEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ b : ℕ, 3 ≤ b → b ≤ logBudget F →
      ∀ (P : EqualityPattern b 2) (bits : Bits b) (p : Point F),
        (∑ a : DirectionAssignment F b 2,
          if AllTokensDistinct a then conditionedOffsetProbability
            (Aligned P a bits p) (AdmissibleBadCover P a bits p) else 0) ≤
          ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
            (C * (b : ℝ) ^ 3 / Fintype.card F)

theorem pencilTwoReuses_of_alignment_and_injective
    (halign : AlignmentNormalizationResult.{u})
    (hinjective : InjectiveTwoReuseEstimate.{u}) : PencilTwoReusesResult.{u} := by
  obtain ⟨C, hC, q₀, hbound⟩ := hinjective
  refine ⟨C + 4, by linarith, q₀, ?_⟩
  intro F _ _ _ hq b hb hB P bits p
  apply direction_sum_le_of_injective P bits p (by omega) C
  · intro a ha
    exact halign F b 2 hb hB (by omega) P a ha bits p
  · exact hbound F hq b hb hB P bits p

end
end Balanced.Local.TwoReuseAssembly

end OAI
