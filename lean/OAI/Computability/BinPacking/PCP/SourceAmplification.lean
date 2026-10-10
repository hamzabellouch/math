import OAI.Computability.BinPacking.Games.Holenstein
import OAI.Computability.BinPacking.Games.RepetitionUpper
import OAI.Computability.BinPacking.PCP.NormalizationEmitMachine

namespace OAI

namespace BinPackingGames.Integration.SourceParameters

def rate (gap : ℚ) : ℚ := 1 - gap ^ 3 / 100000

theorem rate_bounds {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1) :
    0 < rate gap ∧ rate gap < 1 := by
  have hcube : gap ^ 3 ≤ 1 := pow_le_one₀ hgap.le hgap1
  have hcubePos : 0 < gap ^ 3 := pow_pos hgap _
  constructor <;> unfold rate <;> linarith

theorem fourth_power_comparison {gap : ℚ} (hgap : 0 ≤ gap) (hgap1 : gap ≤ 1) :
    1 - (gap : ℝ) ^ 3 / 6000 ≤ (rate gap : ℝ) ^ 4 := by
  have hg : (0 : ℝ) ≤ gap := by exact_mod_cast hgap
  have hg1 : (gap : ℝ) ≤ 1 := by exact_mod_cast hgap1
  have hc : (gap : ℝ) ^ 3 ≤ 1 := pow_le_one₀ hg hg1
  have hc0 : 0 ≤ (gap : ℝ) ^ 3 := pow_nonneg hg _
  have hb := one_add_mul_le_pow (a := -(gap : ℝ) ^ 3 / 100000)
    (by linarith : (-2 : ℝ) ≤ -(gap : ℝ) ^ 3 / 100000) 4
  have hr : (rate gap : ℝ) = 1 - (gap : ℝ) ^ 3 / 100000 := by
    simp only [rate, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat]
  rw [hr]
  calc
    _ ≤ 1 + 4 * (-(gap : ℝ) ^ 3 / 100000) := by linarith
    _ ≤ _ := by simpa only [Nat.cast_ofNat, sub_eq_add_neg, neg_div] using hb

theorem four_bit_rate_comparison {gap : ℚ}
    (hgap : 0 < gap) (hgap1 : gap ≤ 1) (n : Nat) :
    (1 - (gap : ℝ) ^ 3 / 6000) ^ ((n : ℝ) / 4) ≤ (rate gap : ℝ) ^ n := by
  have hg : (0 : ℝ) ≤ gap := by exact_mod_cast hgap.le
  have hg1 : (gap : ℝ) ≤ 1 := by exact_mod_cast hgap1
  have hc : (gap : ℝ) ^ 3 ≤ 1 := pow_le_one₀ hg hg1
  have hr : (0 : ℝ) ≤ rate gap := by exact_mod_cast (rate_bounds hgap hgap1).1.le
  calc
    _ ≤ ((rate gap : ℝ) ^ 4) ^ ((n : ℝ) / 4) :=
      Real.rpow_le_rpow (by linarith) (fourth_power_comparison hgap.le hgap1) (by positivity)
    _ = (rate gap : ℝ) ^ ((4 : ℝ) * ((n : ℝ) / 4)) :=
      (Real.rpow_natCast_mul hr 4 ((n : ℝ) / 4)).symm
    _ = (rate gap : ℝ) ^ (n : ℝ) := by congr 1; ring
    _ = _ := Real.rpow_natCast _ _

theorem logTwo_sixteen : BinPackingGames.Foundations.Repetition.logTwo 16 = 4 := by
  unfold BinPackingGames.Foundations.Repetition.logTwo
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  simp [hlog]

theorem game_repetition_rate {Q₁ Q₂ A₁ A₂ : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
    [Nonempty A₁] [Nonempty A₂] [DecidableEq Q₁] [DecidableEq Q₂]
    (G : BinPackingGames.Foundations.Games.Game Q₁ Q₂ A₁ A₂)
    {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hcards : Fintype.card A₁ * Fintype.card A₂ = 16)
    (hvalue : G.value ≤ 1 - (gap : ℝ)) (n : Nat) :
    (G.repetition n).value ≤ (rate gap : ℝ) ^ n := by
  have hg : (0 : ℝ) < gap := by exact_mod_cast hgap
  have halphabet : BinPackingGames.Foundations.Repetition.logTwo
      ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ 4 := by
    rw [← Nat.cast_mul, hcards]
    exact logTwo_sixteen.le
  have h := BinPackingGames.Foundations.Repetition.holenstein_repetition_value
    G n hvalue (by linarith) (by norm_num : (1 : ℝ) ≤ 4) halphabet
  simp only [sub_sub_cancel] at h
  exact h.trans (four_bit_rate_comparison hgap hgap1 n)

def sourceThreshold (D : Nat) (δ : ℚ) : ℚ := 4 * (D : ℚ)⁻¹ * δ ^ 2

theorem sourceThreshold_pos {D : Nat} (hD : 0 < D) {δ : ℚ} (hδ : 0 < δ) :
    0 < sourceThreshold D δ := by
  unfold sourceThreshold
  positivity

theorem exists_repetition_length {gap δ : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) {D : Nat} (hD : 0 < D) :
    ∃ u : Nat, 0 < u ∧ (rate gap) ^ u < sourceThreshold D δ :=
  BinPackingGames.Soundness.RepetitionUpper.exists_power_lt (rate gap) (sourceThreshold D δ)
    (rate_bounds hgap hgap1).1.le (rate_bounds hgap hgap1).2 (sourceThreshold_pos hD hδ)

def repetitionLength (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) : Nat :=
  Nat.find (exists_repetition_length hgap hgap1 hδ hD)

theorem repetitionLength_spec (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) :
    0 < repetitionLength gap δ hgap hgap1 hδ D hD ∧
      rate gap ^ repetitionLength gap δ hgap hgap1 hδ D hD < sourceThreshold D δ :=
  Nat.find_spec (exists_repetition_length hgap hgap1 hδ hD)

theorem repetitionLength_real_bound (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) :
    (rate gap : ℝ) ^ repetitionLength gap δ hgap hgap1 hδ D hD ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2 := by
  have h := (repetitionLength_spec gap δ hgap hgap1 hδ D hD).2.le
  unfold sourceThreshold at h
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  exact hr

end BinPackingGames.Integration.SourceParameters

namespace BinPackingCompleteness.SourceAmplification

open SourceClause BinPackingGames.Foundations Games
open BinPackingGames.Integration

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
  exact BinPackingGames.Soundness.RepetitionUpper.exists_power_lt
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

end BinPackingCompleteness.SourceAmplification

end OAI
