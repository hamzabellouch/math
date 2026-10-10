import OAI.Computability.PerfectCompleteness.Reduction.SourceGame
import OAI.Computability.UniqueGames.Reduction.FinalParametersLemmas

namespace OAI

section

namespace PerfectCompleteness.SourceAmplification

open SourceClause UniqueGamesTheorem.Foundations Games
open UniqueGamesTheorem.Integration

theorem logTwo_le_four {x : ℝ} (hx : 0 < x) (hbound : x ≤ 16) :
    Repetition.logTwo x ≤ 4 := by
  calc
    Repetition.logTwo x ≤ Repetition.logTwo 16 := by
      unfold Repetition.logTwo
      exact div_le_div_of_nonneg_right (Real.log_le_log hx hbound)
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    _ = 4 := SourceParameters.logTwo_sixteen

theorem game_repetition_rate_le_sixteen {Q₁ Q₂ A₁ A₂ : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
    [Nonempty A₁] [Nonempty A₂] [DecidableEq Q₁] [DecidableEq Q₂]
    (G : Game Q₁ Q₂ A₁ A₂) {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hcards : Fintype.card A₁ * Fintype.card A₂ ≤ 16)
    (hvalue : G.value ≤ 1 - (gap : ℝ)) (k : Nat) :
    (G.repetition k).value ≤ (SourceParameters.rate gap : ℝ) ^ k := by
  have hg : (0 : ℝ) < gap := by exact_mod_cast hgap
  have ha : (0 : ℝ) < Fintype.card A₁ := by exact_mod_cast Fintype.card_pos (α := A₁)
  have hb : (0 : ℝ) < Fintype.card A₂ := by exact_mod_cast Fintype.card_pos (α := A₂)
  have hbound : (Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ) ≤ 16 := by
    exact_mod_cast hcards
  have halphabet := logTwo_le_four (mul_pos ha hb) hbound
  have h := Repetition.holenstein_repetition_value G k hvalue
    (by linarith) (by norm_num : (1 : ℝ) ≤ 4) halphabet
  simp only [sub_sub_cancel] at h
  exact h.trans (SourceParameters.four_bit_rate_comparison hgap hgap1 k)

def ClauseGap {n m : Nat} (clauses : Fin m → NormalizedClause n) (γ : ℚ) : Prop :=
  ∀ assignment : Fin n → Bool,
    γ * (m : ℚ) ≤ (SourceGame.violatedCount clauses assignment : ℚ)

theorem source_value_le {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) {γ : ℚ} (gap : ClauseGap clauses γ) :
    (SourceGame.game clauses).value ≤ 1 - ((γ / 3 : ℚ) : ℝ) := by
  apply ((SourceGame.game clauses).value_le_iff _).mpr
  intro strategy
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_neZero m
  have hcount : (γ : ℝ) * (m : ℝ) ≤
      (SourceGame.violatedCount clauses strategy.2 : ℝ) := by
    exact_mod_cast gap strategy.2
  have hfrac := (le_div_iff₀ hm).mpr hcount
  have h := SourceGame.success_le_one_sub_third_violations clauses strategy
  push_cast
  linarith

theorem source_repetition_rate {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) {γ : ℚ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (gap : ClauseGap clauses γ) (k : Nat) :
    ((SourceGame.game clauses).repetition k).value ≤
      (SourceParameters.rate (γ / 3) : ℝ) ^ k := by
  have hthird : (0 : ℚ) < γ / 3 := div_pos hγ (by norm_num)
  have hthird1 : γ / 3 ≤ (1 : ℚ) := by linarith
  have hv : (SourceGame.questionGame clauses).value ≤ 1 - ((γ / 3 : ℚ) : ℝ) := by
    simpa only [SourceGame.questionGame, OccurrenceGame.toGame_value] using
      source_value_le clauses gap
  have h := game_repetition_rate_le_sixteen (SourceGame.questionGame clauses)
    hthird hthird1 (by decide) hv k
  simpa only [SourceGame.questionGame, OccurrenceGame.toGame_repetition_value] using h

theorem exists_repetition_length {γ σ : ℚ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ) :
    ∃ k : Nat, 0 < k ∧ SourceParameters.rate (γ / 3) ^ k < σ := by
  have hthird : (0 : ℚ) < γ / 3 := div_pos hγ (by norm_num)
  have hthird1 : γ / 3 ≤ (1 : ℚ) := by linarith
  have hr := SourceParameters.rate_bounds hthird hthird1
  exact UniqueGamesTheorem.Soundness.RepetitionUpper.exists_power_lt
    (SourceParameters.rate (γ / 3)) σ hr.1.le hr.2 hσ

def repetitionLength (γ σ : ℚ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ) : Nat :=
  Nat.find (exists_repetition_length hγ hγ1 hσ)

theorem repetitionLength_spec (γ σ : ℚ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ) :
    0 < repetitionLength γ σ hγ hγ1 hσ ∧
      SourceParameters.rate (γ / 3) ^ repetitionLength γ σ hγ hγ1 hσ < σ :=
  Nat.find_spec (exists_repetition_length hγ hγ1 hσ)

theorem repeated_source_value_lt {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (γ σ : ℚ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ) (gap : ClauseGap clauses γ) :
    ((SourceGame.game clauses).repetition (repetitionLength γ σ hγ hγ1 hσ)).value < (σ : ℝ) := by
  have hsmall : (SourceParameters.rate (γ / 3) : ℝ) ^
      repetitionLength γ σ hγ hγ1 hσ < (σ : ℝ) := by
    exact_mod_cast (repetitionLength_spec γ σ hγ hγ1 hσ).2
  exact (source_repetition_rate clauses hγ hγ1 gap _).trans_lt hsmall

theorem repeated_completeness_success {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (assignment : Fin n → Bool)
    (satisfying : ∀ c, (clauses c).clause.eval assignment = true) (k : Nat) :
    ((SourceGame.game clauses).repetition k).success
      (Game.repeatStrategy (SourceGame.completenessStrategy clauses assignment satisfying) k) = 1 := by
  rw [← (SourceGame.game clauses).toGame_repetition_success (SourceGame.presentation clauses)]
  change ((SourceGame.questionGame clauses).repetition k).success
    (Game.repeatStrategy (SourceGame.completenessStrategy clauses assignment satisfying) k) = 1
  rw [Game.success_repeatStrategy, SourceGame.questionGame_success,
    SourceGame.completeness_success, one_pow]

theorem repeated_completeness_value {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (assignment : Fin n → Bool)
    (satisfying : ∀ c, (clauses c).clause.eval assignment = true) (k : Nat) :
    ((SourceGame.game clauses).repetition k).value = 1 := by
  apply le_antisymm ((SourceGame.game clauses).repetition k).value_le_one
  rw [← repeated_completeness_success clauses assignment satisfying k]
  exact ((SourceGame.game clauses).repetition k).success_le_value _

end PerfectCompleteness.SourceAmplification

end

end OAI
