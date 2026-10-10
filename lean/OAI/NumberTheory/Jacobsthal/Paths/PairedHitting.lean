import Mathlib.Probability.Kernel.Composition.KernelLemmas
import OAI.NumberTheory.Jacobsthal.Probability.FirstHitKernels

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedHitting

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures KernelDensityBridge GoodPairTransitions

noncomputable def pairedOdd : Kernel OddState OddState := evenToOdd ∘ₖ oddToEven

instance pairedOdd_isMarkovKernel : IsMarkovKernel pairedOdd := by unfold pairedOdd; infer_instance

theorem pairedOdd_map_ratio (s : OddState) :
    (pairedOdd s).map (Subtype.val : OddState → ℝ) = (oddTwoStep s).map Prod.snd := by
  have hm : Measurable (fun x : EvenState × OddState => (x.1.1, x.2.1)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  rw [pairedOdd, Kernel.comp_eq_snd_compProd, Kernel.snd_apply, oddTwoStep,
    Kernel.map_apply _ hm, Measure.map_map measurable_snd hm,
    Measure.map_map measurable_subtype_coe measurable_snd]
  rfl

theorem pairedOdd_progress {M : ℝ} (hM : 4 ≤ M) (s : OddState) (hs : s.1 ≤ M) :
    ENNReal.ofReal (goodPairProbability M) ≤
      pairedOdd s {t : OddState | t.1 ≤ max (3 / 2) (s.1 - 3 / 2)} := by
  have heq := congrArg (fun μ : Measure ℝ => μ (Iic (max (3 / 2) (s.1 - 3 / 2)))) (pairedOdd_map_ratio s)
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Iic,
    Measure.map_apply measurable_snd measurableSet_Iic] at heq
  change pairedOdd s {t : OddState | t.1 ≤ max (3 / 2) (s.1 - 3 / 2)} =
    oddTwoStep s {x : ℝ × ℝ | x.2 ≤ max (3 / 2) (s.1 - 3 / 2)} at heq
  rw [heq]
  exact odd_terminal_progress hM s hs

def pairedRegeneration : Set OddState := {s | s.1 ≤ 3}

theorem pairedRegeneration_measurable : MeasurableSet pairedRegeneration :=
  measurableSet_le measurable_subtype_coe measurable_const

noncomputable def pairedKilled : Kernel OddState OddState :=
  pairedOdd.restrict pairedRegeneration_measurable.compl

instance pairedKilled_isFiniteKernel : IsFiniteKernel pairedKilled := by unfold pairedKilled; infer_instance

instance pairedKilled_pow_isFiniteKernel (n : ℕ) : IsFiniteKernel (pairedKilled ^ n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel OddState OddState); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsFiniteKernel (pairedKilled ∘ₖ (pairedKilled ^ n))
    infer_instance

noncomputable def hitBy : ℕ → OddState → ℝ≥0∞
  | 0, _ => 0
  | n + 1, s => ∫⁻ t, if t.1 ≤ 3 then 1 else hitBy n t ∂pairedOdd s

theorem hitBy_measurable (n : ℕ) : Measurable (hitBy n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (Measurable.ite pairedRegeneration_measurable measurable_const ih).lintegral_kernel

theorem paired_survival_balance (n : ℕ) (s : OddState) :
    (pairedKilled ^ n) s univ + hitBy n s = 1 := by
  induction n generalizing s with
  | zero =>
    change (Measure.dirac s) univ + 0 = 1
    simp
  | succ n ih =>
    have hp : pairedKilled ^ (n + 1) = (pairedKilled ^ n) ∘ₖ pairedKilled := pow_succ pairedKilled n
    rw [hp, Kernel.comp_apply' _ _ _ MeasurableSet.univ, pairedKilled, Kernel.restrict_apply]
    rw [← lintegral_indicator pairedRegeneration_measurable.compl]
    change (∫⁻ t, pairedRegenerationᶜ.indicator (fun t => (pairedKilled ^ n) t univ) t ∂pairedOdd s) +
      (∫⁻ t, if t.1 ≤ 3 then 1 else hitBy n t ∂pairedOdd s) = 1
    rw [← lintegral_add_left ((Kernel.measurable_coe (pairedKilled ^ n) MeasurableSet.univ).indicator
      pairedRegeneration_measurable.compl)]
    have heq : ∀ t : OddState, pairedRegenerationᶜ.indicator (fun t => (pairedKilled ^ n) t univ) t +
        (if t.1 ≤ 3 then 1 else hitBy n t) = 1 := by
      intro t
      by_cases ht : t.1 ≤ 3
      · rw [ite_eq_left ht, indicator_of_notMem (show t ∉ pairedRegenerationᶜ from not_not_intro ht), zero_add]
      · rw [ite_eq_right ht, indicator_of_mem (show t ∈ pairedRegenerationᶜ from ht)]
        exact ih t
    rw [lintegral_congr heq]
    simp

theorem hitBy_le_one (n : ℕ) (s : OddState) : hitBy n s ≤ 1 := by
  calc
    _ ≤ (pairedKilled ^ n) s univ + hitBy n s := le_add_of_nonneg_left zero_le
    _ = 1 := paired_survival_balance n s

theorem hitBy_lower {M : ℝ} (hM : 4 ≤ M) (n : ℕ) (hn : 0 < n)
    (s : OddState) (hsM : s.1 ≤ M) (hsn : s.1 ≤ 3 + (3 / 2) * (n : ℝ)) :
    (ENNReal.ofReal (goodPairProbability M)) ^ n ≤ hitBy n s := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    let q : ℝ≥0∞ := ENNReal.ofReal (goodPairProbability M)
    let B : Set OddState := {t | t.1 ≤ max (3 / 2) (s.1 - 3 / 2)}
    have hB : MeasurableSet B := measurableSet_le measurable_subtype_coe measurable_const
    have hq1 : q ≤ 1 := by
      change ENNReal.ofReal (goodPairProbability M) ≤ 1
      exact (ENNReal.ofReal_le_one).mpr (goodPairProbability_le_one M)
    have hpoint : ∀ t ∈ B, q ^ n ≤ (if t.1 ≤ 3 then 1 else hitBy n t) := by
      intro t ht
      have htbound : t.1 ≤ max (3 / 2) (s.1 - 3 / 2) := ht
      have htM : t.1 ≤ M := le_trans htbound (max_le (by linarith) (by linarith))
      have htn : t.1 ≤ 3 + (3 / 2) * (n : ℝ) := by
        apply le_trans htbound
        apply max_le
        · nlinarith [Nat.cast_nonneg (α := ℝ) n]
        · push_cast at hsn
          linarith
      by_cases htR : t.1 ≤ 3
      · rw [ite_eq_left htR]
        exact pow_le_one₀ zero_le hq1
      · rw [ite_eq_right htR]
        have hn0 : 0 < n := by
          by_contra h
          have hnz : n = 0 := Nat.eq_zero_of_not_pos h
          subst n
          norm_num at htn
          exact htR htn
        exact ih hn0 t htM htn
    change q ^ (n + 1) ≤ _
    calc
      q ^ (n + 1) = q ^ n * q := pow_succ q n
      _ ≤ q ^ n * pairedOdd s B := mul_le_mul le_rfl (pairedOdd_progress hM s hsM) zero_le zero_le
      _ = ∫⁻ t in B, q ^ n ∂pairedOdd s := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ t in B, (if t.1 ≤ 3 then 1 else hitBy n t) ∂pairedOdd s := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict hB] with t ht
        exact hpoint t ht
      _ ≤ ∫⁻ t, (if t.1 ≤ 3 then 1 else hitBy n t) ∂pairedOdd s := setLIntegral_le_lintegral _ _
      _ = hitBy (n + 1) s := rfl

theorem compact_paired_hit {M : ℝ} (hM : 4 ≤ M) : ∃ n : ℕ, 0 < n ∧ ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
    ∀ s : OddState, s.1 ≤ M → ENNReal.ofReal p ≤ hitBy n s := by
  obtain ⟨n, hn⟩ := exists_nat_ge M
  refine ⟨n + 1, by omega, goodPairProbability M ^ (n + 1),
    pow_pos (goodPairProbability_pos hM) _, pow_le_one₀ (goodPairProbability_pos hM).le (goodPairProbability_le_one M), ?_⟩
  intro s hs
  rw [ENNReal.ofReal_pow (goodPairProbability_pos hM).le]
  apply hitBy_lower hM (n + 1) (by omega) s hs
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem paired_survival_le_one (n : ℕ) (s : OddState) : (pairedKilled ^ n) s univ ≤ 1 := by
  calc
    _ ≤ (pairedKilled ^ n) s univ + hitBy n s := le_add_of_nonneg_right zero_le
    _ = 1 := paired_survival_balance n s

theorem paired_survival_antitone (s : OddState) : Antitone (fun n => (pairedKilled ^ n) s univ) := by
  apply antitone_nat_of_succ_le
  intro n
  have hp : pairedKilled ^ (n + 1) = pairedKilled ∘ₖ (pairedKilled ^ n) := pow_succ' pairedKilled n
  rw [hp, Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  calc
    _ ≤ ∫⁻ _t, (1 : ℝ≥0∞) ∂(pairedKilled ^ n) s := lintegral_mono (fun t => by
      simpa only [pow_one] using paired_survival_le_one 1 t)
    _ = _ := by simp

theorem compact_paired_survival {M : ℝ} (hM : 4 ≤ M) : ∃ n : ℕ, 0 < n ∧ ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
    ∀ m : ℕ, n ≤ m → ∀ s : OddState, s.1 ≤ M →
      (pairedKilled ^ m) s univ ≤ ENNReal.ofReal (1 - p) := by
  obtain ⟨n, hn, p, hp, hp1, hh⟩ := compact_paired_hit hM
  refine ⟨n, hn, p, hp, hp1, ?_⟩
  intro m hnm s hs
  have hsum : ENNReal.ofReal p + (pairedKilled ^ n) s univ ≤ 1 := by
    calc
      _ ≤ hitBy n s + (pairedKilled ^ n) s univ := add_le_add (hh s hs) le_rfl
      _ = 1 := by rw [add_comm]; exact paired_survival_balance n s
  have hQ := ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top hsum
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp.le] at hQ
  exact le_trans (paired_survival_antitone s hnm) hQ

end NumberTheoryLean.PairedHitting

end

end Erdos970

end OAI
