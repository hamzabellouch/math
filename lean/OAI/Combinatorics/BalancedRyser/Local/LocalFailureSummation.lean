import OAI.Combinatorics.BalancedRyser.Incidence.LocalLargePencils
import OAI.Combinatorics.BalancedRyser.Local.LocalAlignedReuseCounting
import OAI.Combinatorics.BalancedRyser.Local.LocalPatternEvents

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem selectedProbability_exists_finset_le {ι : Type*} [DecidableEq ι]
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v) (s : Finset ι)
    (E : ι → Configuration F → Prop) :
    selectedProbability w (fun C => ∃ i ∈ s, E i C) ≤
      ∑ i ∈ s, selectedProbability w (E i) := by
  have h := sum_event_union_le
    (fun z : MergedPairs F × Output F => w z.1 z.2)
    (fun z => hw z.1 z.2) s (fun i z => E i (configuration z.1 z.2))
  have hd := div_le_div_of_nonneg_right h
    (show (0 : ℝ) ≤ Fintype.card (MergedPairs F) by positivity)
  calc
    selectedProbability w (fun C => ∃ i ∈ s, E i C) =
        (∑ z : MergedPairs F × Output F,
          if ∃ i ∈ s, E i (configuration z.1 z.2) then w z.1 z.2 else 0) /
            Fintype.card (MergedPairs F) := by
      unfold selectedProbability
      apply congrArg (fun x : ℝ => x / Fintype.card (MergedPairs F))
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> rfl
    _ ≤ (∑ i ∈ s, ∑ z : MergedPairs F × Output F,
        if E i (configuration z.1 z.2) then w z.1 z.2 else 0) /
          Fintype.card (MergedPairs F) := hd
    _ = _ := by simp only [Finset.sum_div, Fintype.sum_prod_type, selectedProbability]

def SmallBadLocalEvent (C : Configuration F) : Prop :=
  ∃ p : Point F, ∃ b ∈ Finset.Icc 3 (logBudget F), ∃ κ ∈ Finset.range 3,
    C.splitMultiplicity p = b ∧ reuseCount C p = κ ∧ BadLocalCoverAt b p C

theorem local_failure_cases (C : Configuration F) (hbad : ¬ C.LocalCondition) :
    LargePencilEvent C ∨ HighReuseEvent C ∨ SmallBadLocalEvent C := by
  unfold Configuration.LocalCondition at hbad
  push Not at hbad
  obtain ⟨p, hb, hbad⟩ := hbad
  by_cases hlarge : logBudget F < C.splitMultiplicity p
  · exact Or.inl ⟨p, hlarge⟩
  by_cases hhigh : 3 ≤ reuseCount C p
  · exact Or.inr (Or.inl ⟨p, by omega, hhigh⟩)
  refine Or.inr (Or.inr ⟨p, C.splitMultiplicity p,
    Finset.mem_Icc.mpr ⟨hb, by omega⟩, reuseCount C p,
    Finset.mem_range.mpr (by omega), rfl, rfl, hbad⟩)

theorem small_bad_local_probability_le_sum
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v) :
    selectedProbability w SmallBadLocalEvent ≤
      ∑ p : Point F, ∑ b ∈ Finset.Icc 3 (logBudget F), ∑ κ ∈ Finset.range 3,
        selectedProbability w (fun C => C.splitMultiplicity p = b ∧
          reuseCount C p = κ ∧ BadLocalCoverAt b p C) := by
  have hp := selectedProbability_exists_finset_le w hw (Finset.univ : Finset (Point F))
    (fun p C => ∃ b ∈ Finset.Icc 3 (logBudget F), ∃ κ ∈ Finset.range 3,
      C.splitMultiplicity p = b ∧ reuseCount C p = κ ∧ BadLocalCoverAt b p C)
  simp only [Finset.mem_univ, true_and] at hp
  refine hp.trans (Finset.sum_le_sum fun p _ => ?_)
  refine (selectedProbability_exists_finset_le w hw (Finset.Icc 3 (logBudget F))
    (fun b C => ∃ κ ∈ Finset.range 3,
      C.splitMultiplicity p = b ∧ reuseCount C p = κ ∧ BadLocalCoverAt b p C)).trans ?_
  apply Finset.sum_le_sum
  intro b _
  exact selectedProbability_exists_finset_le w hw (Finset.range 3)
    (fun κ C => C.splitMultiplicity p = b ∧ reuseCount C p = κ ∧ BadLocalCoverAt b p C)

theorem local_failure_probability_le_size_sum
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v) :
    selectedProbability w (fun C => ¬ C.LocalCondition) ≤
      selectedProbability w LargePencilEvent + selectedProbability w HighReuseEvent +
        ∑ p : Point F, ∑ b ∈ Finset.Icc 3 (logBudget F), ∑ κ ∈ Finset.range 3,
          selectedProbability w (fun C => C.splitMultiplicity p = b ∧
            reuseCount C p = κ ∧ BadLocalCoverAt b p C) := by
  have h := selectedProbability_le_three_of_positive_imp w hw
    (fun C => ¬ C.LocalCondition) LargePencilEvent HighReuseEvent SmallBadLocalEvent
    (fun _ _ _ hbad => local_failure_cases _ hbad)
  exact h.trans (add_le_add le_rfl (small_bad_local_probability_le_sum w hw))

theorem small_bad_local_probability_le_envelope
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (L : ℝ) (f : ℕ → ℝ)
    (hsmall : ∀ (p : Point F) b, b ∈ Finset.Icc 3 (logBudget F) →
      ∀ κ ∈ Finset.range 3,
        selectedProbability w (fun C => C.splitMultiplicity p = b ∧
          reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤ L * f b) :
    selectedProbability w SmallBadLocalEvent ≤
      3 * L * ((Fintype.card F : ℝ) ^ 2 * ∑ b ∈ Finset.Icc 3 (logBudget F), f b) := by
  refine (small_bad_local_probability_le_sum w hw).trans ?_
  calc
    _ ≤ ∑ _p : Point F, ∑ b ∈ Finset.Icc 3 (logBudget F),
        ∑ _κ ∈ Finset.range 3, L * f b := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.sum_le_sum (fun κ hk => hsmall p b hb κ hk)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.card_univ, Point, Fintype.card_prod, Nat.cast_mul]
      simp_rw [← mul_assoc, ← Finset.mul_sum]
      ring

theorem high_reuse_probability_le (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (C : ℝ)
    (hpoint : ∀ p : Point F,
      selectedProbability w (fun X => 2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p) ≤
        C / (Fintype.card F : ℝ) ^ 3) :
    selectedProbability w HighReuseEvent ≤ C / Fintype.card F := by
  have hu := selectedProbability_exists_finset_le w hw (Finset.univ : Finset (Point F))
    (fun p X => 2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p)
  simp only [Finset.mem_univ, true_and] at hu
  calc
    _ ≤ ∑ p : Point F,
        selectedProbability w (fun X => 2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p) := hu
    _ ≤ ∑ _p : Point F, C / (Fintype.card F : ℝ) ^ 3 :=
      Finset.sum_le_sum (fun p _ => hpoint p)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Point, Fintype.card_prod,
        Nat.cast_mul, nsmul_eq_mul]
      have hq : (Fintype.card F : ℝ) ≠ 0 := by positivity
      field_simp

end
end Balanced.Local

end OAI
