import OAI.NumberTheory.Ostmann.Construction.SmoothCellDeletion
import OAI.NumberTheory.Ostmann.Construction.SmoothLogCellProfile
import OAI.NumberTheory.Ostmann.Construction.OneSidedDecayBudget

namespace OAI

/-! # Uniform normalization after the two prescribed nongiant deletions -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- Removing either Page-exceptional prime costs less than half the cell
mass. The bound is uniform over the chosen centres and over the deleted set. -/
theorem PublishedProgressionInput.deletedSmoothCell_normalizer_rate
    (P : PublishedProgressionInput) (C b : ℝ) (hb : 0 < b)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (hφone : ∀ x, φ x ≤ 1)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hcentral : ∀ x, |x| ≤ 1 / 2 → b ≤ φ x) :
    ∀ᶠ L : ℝ in atTop, ∀ (G : ℝ) (E : Finset ℕ),
      2 ≤ G → Real.exp ((39 / 10000 : ℝ) * L) ≤ G - 1 / 2 →
      G ≤ Real.exp (C * L) → E.card ≤ 2 →
      Real.exp (-(C + 1 / 5) * L) ≤
        smoothGiantMass (smoothGiantPrimeRange G \ E) φ G ∧
      smoothGiantLogNormalizer (smoothGiantPrimeRange G \ E) φ G ≤ (C + 1 / 5) * L ∧
      (∑ p : smoothGiantPrimeRange G,
        deletedSmoothCellPrior (smoothGiantPrimeRange G) E φ G p) = 1 := by
  let K : ℝ := |C| + |Real.log 4| + 3
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  filter_upwards [P.smoothGiant_normalizer_rate C b hb φ hφ hcentral,
    eventual_polynomial_log_budget K 1 (39 / 10000) 1 1 hK (by norm_num)
      (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (10 * Real.log 2)]
    with L hbase hpoly hL hL2
  intro G E hG hlo hhi hE
  obtain ⟨hmass, _, _⟩ := hbase G hG hlo hhi
  have hpoly' : K * (1 + L) ≤ Real.exp ((39 / 10000 : ℝ) * L) := by
    simpa only [pow_one, one_mul] using hpoly L (by linarith) (by linarith)
  have hlin : (C + 1 / 10) * L + 1 + Real.log 4 ≤ K * (1 + L) := by
    have hC := le_abs_self C
    have hlog := le_abs_self (Real.log 4)
    have hC0 := abs_nonneg C
    have hlog0 := abs_nonneg (Real.log 4)
    dsimp only [K]
    nlinarith
  have hexponent : 1 - G ≤ -(C + 1 / 10) * L - Real.log 4 := by linarith
  have hsmall : 2 * Real.exp (1 - G) ≤ Real.exp (-(C + 1 / 10) * L) / 2 := by
    calc
      _ ≤ 2 * Real.exp (-(C + 1 / 10) * L - Real.log 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
      _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; ring
  have hdelete := smoothCell_deletion_loss (smoothGiantPrimeRange G) E φ G hφone hout
  have hE' : (E.card : ℝ) * Real.exp (1 - G) ≤ 2 * Real.exp (1 - G) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hE) (Real.exp_nonneg _)
  have hhalf : Real.exp (-(C + 1 / 10) * L) / 2 ≤
      smoothGiantMass (smoothGiantPrimeRange G \ E) φ G := by linarith
  have htenth : Real.exp (-L / 10) ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hmass' : Real.exp (-(C + 1 / 5) * L) ≤
      smoothGiantMass (smoothGiantPrimeRange G \ E) φ G := by
    apply le_trans _ hhalf
    calc
      _ = Real.exp (-(C + 1 / 10) * L) * Real.exp (-L / 10) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-(C + 1 / 10) * L) * (1 / 2) :=
        mul_le_mul_of_nonneg_left htenth (Real.exp_nonneg _)
      _ = _ := by ring
  have hpos := lt_of_lt_of_le (Real.exp_pos _) hmass'
  refine ⟨hmass', ?_, deletedSmoothCellPrior_mass _ E φ G hpos⟩
  have hlog := Real.log_le_log (Real.exp_pos _) hmass'
  rw [Real.log_exp] at hlog
  unfold smoothGiantLogNormalizer
  linarith

theorem PublishedProgressionInput.logCellProfile_deleted_rate
    (P : PublishedProgressionInput) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (G : ℝ) (E : Finset ℕ),
      2 ≤ G → Real.exp ((39 / 10000 : ℝ) * L) ≤ G - 1 / 2 →
      G ≤ Real.exp (C * L) → E.card ≤ 2 →
      Real.exp (-(C + 1 / 5) * L) ≤
        smoothGiantMass (smoothGiantPrimeRange G \ E) logCellProfile G ∧
      smoothGiantLogNormalizer (smoothGiantPrimeRange G \ E) logCellProfile G ≤ (C + 1 / 5) * L ∧
      (∑ p : smoothGiantPrimeRange G,
        deletedSmoothCellPrior (smoothGiantPrimeRange G) E logCellProfile G p) = 1 :=
  P.deletedSmoothCell_normalizer_rate C logCellCentralLower logCellCentralLower_pos
    logCellProfile logCellProfile_nonneg logCellProfile_le_one logCellProfile_zero_outside
    logCellProfile_central

/-- All role centres share one threshold. Both the repeated-sample loss
and the maximum atom are computed from the actual deleted smooth prior. -/
theorem PublishedProgressionInput.logCellProfile_deleted_atom_rate
    (P : PublishedProgressionInput) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (G : ℝ) (E : Finset ℕ),
      2 ≤ G → Real.exp ((39 / 10000 : ℝ) * L) ≤ G - 1 / 2 →
      G ≤ Real.exp (C * L) → E.card ≤ 2 →
      (∑ p : smoothGiantPrimeRange G,
        deletedSmoothCellPrior (smoothGiantPrimeRange G) E logCellProfile G p) = 1 ∧
      ∀ p : smoothGiantPrimeRange G,
        (p : ℝ) * deletedSmoothCellPrior (smoothGiantPrimeRange G) E logCellProfile G p ≤
          Real.exp ((C + 1 / 5) * L) ∧
        deletedSmoothCellPrior (smoothGiantPrimeRange G) E logCellProfile G p ≤
          Real.exp ((C + 1 / 5) * L - (G - 1)) := by
  filter_upwards [P.logCellProfile_deleted_rate C] with L hL
  intro G E hG hlo hhi hE
  obtain ⟨_, hn, hm⟩ := hL G E hG hlo hhi hE
  refine ⟨hm, fun p => ⟨?_, ?_⟩⟩
  · exact (prime_mul_deletedSmoothCellPrior_le _ E
      (fun p hp => (Finset.mem_filter.mp hp).2) logCellProfile G logCellProfile_le_one p).trans
      (Real.exp_le_exp.mpr hn)
  · exact deletedSmoothCellPrior_le_exp _ E (fun p hp => (Finset.mem_filter.mp hp).2)
      logCellProfile G ((C + 1 / 5) * L) logCellProfile_le_one logCellProfile_zero_outside hn p

end Ostmann

end OAI
