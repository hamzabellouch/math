import OAI.Combinatorics.Ryser.LineCover.CountEvents
import OAI.Combinatorics.Ryser.LineCover.CountTailNumerics

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ}

def GoodCounts (process : DeletionProcess F D δ) (ε : ℝ)
    (ω : process.Config) : Prop :=
  |((survivors ∅ ω).card : ℝ) - process.survival * (Fintype.card F : ℝ) ^ 2| ≤
      (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε) ∧
    ∀ l : AffineLine F,
      process.survival * (Fintype.card F : ℝ) -
          (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
        retainedCount {linePoints l} (linePoints l) ω ∧
      retainedCount {linePoints l} (linePoints l) ω ≤
        process.survival * (Fintype.card F : ℝ) + (D : ℝ) +
          (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε)

namespace GoodCounts

variable {process : DeletionProcess F D δ} {ε : ℝ} {ω : process.Config}

theorem total_lower (h : GoodCounts process ε ω) :
    process.survival * (Fintype.card F : ℝ) ^ 2 -
        (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
      ((survivors ∅ ω).card : ℝ) := by
  have hlo := (abs_le.mp h.1).1
  linarith

theorem total_upper (h : GoodCounts process ε ω) :
    ((survivors ∅ ω).card : ℝ) ≤
      process.survival * (Fintype.card F : ℝ) ^ 2 +
        (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε) := by
  have hhi := (abs_le.mp h.1).2
  linarith

theorem line_lower (h : GoodCounts process ε ω) (l : AffineLine F) :
    process.survival * (Fintype.card F : ℝ) -
        (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
      retainedCount {linePoints l} (linePoints l) ω := (h.2 l).1

theorem line_upper (h : GoodCounts process ε ω) (l : AffineLine F) :
    retainedCount {linePoints l} (linePoints l) ω ≤
      process.survival * (Fintype.card F : ℝ) + (D : ℝ) +
        (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) := (h.2 l).2

theorem line_ge_half (h : GoodCounts process ε ω)
    (herror : (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
      δ * (Fintype.card F : ℝ) / 2) (l : AffineLine F) :
    δ * (Fintype.card F : ℝ) / 2 ≤
      retainedCount {linePoints l} (linePoints l) ω := by
  have hbase := mul_le_mul_of_nonneg_right process.survivalLower
    (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ (Fintype.card F : ℝ))
  have hlo := h.line_lower l
  linarith

end GoodCounts

namespace DeletionProcess

variable (process : DeletionProcess F D δ)

theorem prob_not_goodCounts (ε : ℝ) (hD : 1 ≤ D)
    (_hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    process.law.prob (fun ω => ¬ GoodCounts process ε ω) ≤
      2 * (1 + (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) *
        Real.exp (-(Fintype.card F : ℝ) ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hqNat : 1 ≤ Fintype.card F :=
    Nat.succ_le_iff.mpr (Fintype.card_pos (α := F))
  have hq : 1 ≤ (Fintype.card F : ℝ) := by exact_mod_cast hqNat
  have hq0 : 0 < (Fintype.card F : ℝ) := lt_of_lt_of_le zero_lt_one hq
  have hD0 : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
  let T : process.Config → Prop := fun ω =>
    (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
      |((survivors ∅ ω).card : ℝ) - process.survival * (Fintype.card F : ℝ) ^ 2|
  let L : AffineLine F → process.Config → Prop := fun l ω =>
    (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
      |retainedCount {linePoints l} (linePoints l) ω -
        process.law.expectation (retainedCount {linePoints l} (linePoints l))|
  let B : ℝ := 2 * Real.exp
    (-(Fintype.card F : ℝ) ^ (2 * ε) / (16 * (D : ℝ) ^ 5))
  have htotal : process.law.prob T ≤ B := by
    have h := (process.total_count_concentration hD0
      ((Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε))
      (Real.rpow_pos_of_pos hq0 _)).trans
        (total_count_tail_le_stretched_exp hq hD hεhalf)
    simpa only [T, B, retainedCount, Finset.inter_univ] using h
  have hline (l : AffineLine F) : process.law.prob (L l) ≤ B := by
    exact (process.ignored_line_count_concentration hD0 l
      ((Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε))
      (Real.rpow_pos_of_pos hq0 _)).trans
        (line_count_tail_le_stretched_exp hq hD hεhalf)
  have hcover : ∀ ω, ¬ GoodCounts process ε ω → T ω ∨ ∃ l, L l ω := by
    intro ω hbad
    by_cases ht : T ω
    · exact Or.inl ht
    · right
      by_contra hlines
      apply hbad
      refine ⟨?_, ?_⟩
      · exact (lt_of_not_ge ht).le
      · intro l
        have hl : ¬ L l ω := fun h => hlines ⟨l, h⟩
        have habs :
            |retainedCount {linePoints l} (linePoints l) ω -
              process.law.expectation (retainedCount {linePoints l} (linePoints l))| ≤
            (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) := (lt_of_not_ge hl).le
        obtain ⟨hlo, hhi⟩ := abs_le.mp habs
        obtain ⟨hmlo, hmhi⟩ := process.expectation_ignored_lineCount_bounds l
        constructor <;> linarith
  calc
    _ ≤ process.law.prob (fun ω => T ω ∨ ∃ l, L l ω) :=
      process.law.prob_mono hcover
    _ ≤ process.law.prob T + process.law.prob (fun ω => ∃ l, L l ω) :=
      process.law.prob_union_le T (fun ω => ∃ l, L l ω)
    _ ≤ B + ∑ l, process.law.prob (L l) :=
      add_le_add htotal (FiniteLaw.prob_exists_le process.law L)
    _ ≤ B + ∑ _l : AffineLine F, B :=
      add_le_add le_rfl (Finset.sum_le_sum fun l _ => hline l)
    _ = (1 + (Fintype.card (AffineLine F) : ℝ)) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = _ := by
      simp only [card_affineLine, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      dsimp only [B]
      ring

end DeletionProcess
end RyserCoveringCounterexample.LineCover

end

end OAI
