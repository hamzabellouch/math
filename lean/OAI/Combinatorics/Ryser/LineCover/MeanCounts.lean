import OAI.Combinatorics.Ryser.LineCover.Process
import OAI.Combinatorics.Ryser.LineCover.Deletion
import OAI.Combinatorics.Ryser.Geometry.Cardinality

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.DeletionProcess

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ} (process : DeletionProcess F D δ)

theorem expectation_base_count (test : Finset (Point F)) :
    process.law.expectation (retainedCount ∅ test) =
      process.survival * (test.card : ℝ) := by
  change (FiniteLaw.pi process.trials).expectation (retainedCount ∅ test) = _
  rw [expectation_retainedCount]
  simp_rw [process.uniformSurvival]
  simp [mul_comm]

theorem expectation_totalCount :
    process.law.expectation
        (retainedCount ∅ (Finset.univ : Finset (Point F))) =
      process.survival * (Fintype.card F : ℝ) ^ 2 := by
  rw [process.expectation_base_count]
  simp only [Finset.card_univ, card_point, Nat.cast_pow]

theorem expectation_survivorSet_card :
    process.law.expectation (fun ω => ((process.survivorSet ω).card : ℝ)) =
      process.survival * (Fintype.card F : ℝ) ^ 2 := by
  have hcount : (fun ω : process.Config => ((process.survivorSet ω).card : ℝ)) =
      (retainedCount ∅ Finset.univ : process.Config → ℝ) := by
    funext ω
    simp only [retainedCount, survivorSet, Finset.inter_univ]
  rw [hcount]
  exact process.expectation_totalCount

theorem expectation_base_lineCount (l : AffineLine F) :
    process.law.expectation (retainedCount ∅ (linePoints l)) =
      process.survival * (Fintype.card F : ℝ) := by
  simpa only [card_linePoints] using process.expectation_base_count (linePoints l)

theorem prob_selected_line_le (l : AffineLine F) :
    process.law.prob (fun ω => linePoints l ∈ selected ω) ≤
      (D : ℝ) / (Fintype.card F : ℝ) := by
  change (FiniteLaw.pi process.trials).prob
      (fun ω => linePoints l ∈ selected ω) ≤ _
  calc
    _ = (FiniteLaw.pi process.trials).prob
        (fun ω => ∃ i, ∃ S ∈ (ω i).val, S.val = linePoints l) := by
      congr 1
      funext ω
      exact propext mem_selected
    _ ≤ ∑ i, (FiniteLaw.pi process.trials).prob
        (fun ω => ∃ S ∈ (ω i).val, S.val = linePoints l) :=
      FiniteLaw.prob_exists_le (FiniteLaw.pi process.trials)
        (fun i ω => ∃ S ∈ (ω i).val, S.val = linePoints l)
    _ = ∑ i, (process.trials i).prob
        (fun a => ∃ S ∈ a.val, S.val = linePoints l) := by
      apply Finset.sum_congr rfl
      intro i _
      exact FiniteLaw.prob_pi_coordinate process.trials i
        (fun a => ∃ S ∈ a.val, S.val = linePoints l)
    _ ≤ (D : ℝ) / (Fintype.card F : ℝ) := process.lineCap l

theorem mem_ignored_line_survivors_imp (l : AffineLine F)
    (ω : process.Config) (x : Point F)
    (hx : x ∈ survivors {linePoints l} ω) :
    x ∈ survivors ∅ ω ∨ linePoints l ∈ selected ω := by
  by_cases hselected : linePoints l ∈ selected ω
  · exact Or.inr hselected
  · left
    have heq := survivors_insert_eq_of_not_selected
      (ignore := ∅) (ω := ω) hselected
    simp only [Finset.insert_empty] at heq
    exact heq ▸ hx

theorem prob_mem_ignored_line_le (l : AffineLine F) (x : Point F) :
    process.law.prob (fun ω => x ∈ survivors {linePoints l} ω) ≤
      process.survival + (D : ℝ) / (Fintype.card F : ℝ) := by
  calc
    _ ≤ process.law.prob
        (fun ω => x ∈ survivors ∅ ω ∨ linePoints l ∈ selected ω) :=
      process.law.prob_mono
        (fun ω hx => process.mem_ignored_line_survivors_imp l ω x hx)
    _ ≤ process.law.prob (fun ω => x ∈ survivors ∅ ω) +
        process.law.prob (fun ω => linePoints l ∈ selected ω) :=
      process.law.prob_union_le _ _
    _ ≤ process.survival + (D : ℝ) / (Fintype.card F : ℝ) :=
      add_le_add (process.uniformSurvival x).le (process.prob_selected_line_le l)

theorem expectation_ignored_lineCount_bounds (l : AffineLine F) :
    process.survival * (Fintype.card F : ℝ) ≤
        process.law.expectation (retainedCount {linePoints l} (linePoints l)) ∧
      process.law.expectation (retainedCount {linePoints l} (linePoints l)) ≤
        process.survival * (Fintype.card F : ℝ) + (D : ℝ) := by
  constructor
  · rw [← process.expectation_base_lineCount l]
    apply process.law.expectation_mono
    intro ω
    change ((survivors ∅ ω ∩ linePoints l).card : ℝ) ≤
      ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hs, hl⟩
    exact Finset.mem_inter.mpr
      ⟨survivors_mono_ignore (Finset.empty_subset {linePoints l}) ω hs, hl⟩
  · change (FiniteLaw.pi process.trials).expectation
        (retainedCount {linePoints l} (linePoints l)) ≤ _
    rw [expectation_retainedCount]
    calc
      _ ≤ ∑ _x ∈ linePoints l,
          (process.survival + (D : ℝ) / (Fintype.card F : ℝ)) :=
        Finset.sum_le_sum fun x _ => process.prob_mem_ignored_line_le l x
      _ = (Fintype.card F : ℝ) *
          (process.survival + (D : ℝ) / (Fintype.card F : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, card_linePoints]
      _ = process.survival * (Fintype.card F : ℝ) + (D : ℝ) := by
        have hq : (Fintype.card F : ℝ) ≠ 0 := by
          exact_mod_cast (Fintype.card_ne_zero (α := F))
        rw [mul_add, mul_div_cancel₀ (D : ℝ) hq,
          mul_comm (Fintype.card F : ℝ) process.survival]

end RyserCoveringCounterexample.LineCover.DeletionProcess

end

end OAI
