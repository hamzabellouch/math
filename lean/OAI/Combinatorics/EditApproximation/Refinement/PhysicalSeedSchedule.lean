import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSeedTables
import OAI.Combinatorics.EditApproximation.Geometry.SeedFactorSchedule
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The actual finite adaptive sequence of median seed passes. Every chosen
incoming table uses its own fresh product of full-table copy streams. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





theorem scheduledSeedMultiplier_spec (N pass : ℕ) (hf : 3 ≤ smallLogExponent N)
    (hpass : pass < computedSeedPassCount N) :
    (scheduledSeedMultiplier N pass : ℚ) = refinementFactor (scheduledSeedFactor N pass) (inputSmallLog N) := by
  unfold scheduledSeedMultiplier scheduledSeedFactor
  simpa only [inputSmallLog] using
    (dyadicSeedFactor_integer (smallLogExponent N) (computedSeedInitialExponent N) pass hf hpass).symm

theorem scheduledSeedFactor_succ (N pass : ℕ) (hf : 3 ≤ smallLogExponent N)
    (hpass : pass < computedSeedPassCount N) :
    scheduledSeedFactor N (pass + 1) = 4 * (scheduledSeedMultiplier N pass : ℚ) := by
  have hactive := dyadicSeedExponent_active (smallLogExponent N) (computedSeedInitialExponent N) pass hf hpass
  have heq : dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) (pass + 1) =
      (dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass - smallLogExponent N) + 2 := by
    rw [dyadicSeedExponent_succ]
    omega
  unfold scheduledSeedFactor scheduledSeedMultiplier
  rw [heq, pow_add]
  push_cast
  norm_num
  ring

theorem scheduledSeedFactor_zero (N : ℕ) :
    scheduledSeedFactor N 0 = ((integerParameters N).initialFactor : ℚ) := by
  simpa only [scheduledSeedFactor, dyadicSeedExponent, zero_mul, Nat.sub_zero] using computedSeed_initial_factor N

theorem scheduledSeedFactor_terminal (N : ℕ) (hf : 3 ≤ smallLogExponent N) :
    scheduledSeedFactor N (computedSeedPassCount N) ≤ inputSmallLog N := by
  exact dyadicSeedFactor_terminal (smallLogExponent N) (computedSeedInitialExponent N) hf

theorem scheduledSeedFactor_terminal_refinement (N : ℕ) (hf : 3 ≤ smallLogExponent N) :
    refinementFactor (scheduledSeedFactor N (computedSeedPassCount N)) (inputSmallLog N) = 1 := by
  exact dyadicSeedFactor_terminal_refinement (smallLogExponent N) (computedSeedInitialExponent N) hf

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

abbrev ScheduledSeedDraw (pass : ℕ) (seed : Seed) := Fin (H ^ 2) →
  PhysicalProgramDraw (R := R) source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
    T thetaExponent H (ell ^ 80) tau

noncomputable instance scheduledSeedDrawFintype (pass : ℕ) (seed : Seed) :
    Fintype (ScheduledSeedDraw (R := R) source target N P T H pass seed) := by
  classical
  exact Fintype.ofFinite _

noncomputable def scheduledSeedDrawLaw (pass : ℕ) (seed : Seed) :
    Measure (ScheduledSeedDraw (R := R) source target N P T H pass seed) :=
  Measure.pi fun _ : Fin (H ^ 2) => physicalProgramDrawLaw (R := R)
    source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) tau

instance scheduledSeedDrawLaw_probability (pass : ℕ) (seed : Seed) :
    IsProbabilityMeasure (scheduledSeedDrawLaw (R := R) source target N P T H pass seed) := by
  unfold scheduledSeedDrawLaw
  infer_instance

noncomputable def scheduledSeedNext (pass : ℕ) (seed : Seed)
    (draw : ScheduledSeedDraw (R := R) source target N P T H pass seed) : Seed :=
  physicalMedianUpdateTable source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass) T delta
    (scheduledSeedMultiplier N pass) S (H ^ 2)
    (physicalProgramDrawSelections source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
      T thetaExponent H (ell ^ 80) tau eta kappa) draw

noncomputable def scheduledSeedLaw (incoming : Measure Seed) (passes : ℕ) : Measure Seed := by
  classical
  exact adaptiveSeedSequence (scheduledSeedDrawLaw (R := R) source target N P T H) incoming
    (scheduledSeedNext (R := R) source target N P T S H) passes

instance scheduledSeedLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming] (passes : ℕ) :
    IsProbabilityMeasure (scheduledSeedLaw (R := R) source target N P T S H incoming passes) := by
  unfold scheduledSeedLaw
  infer_instance

variable (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
  (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
  (hsize : source.length + target.length ≤ N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
 theorem scheduledSeedNext_failure (pass : ℕ) (hpass : pass < computedSeedPassCount N)
    (seed : Seed) (hseed : physicalSeedGood source target (scheduledSeedFactor N pass) seed) :
    (scheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
      {draw | ¬ physicalSeedGood source target (scheduledSeedFactor N (pass + 1))
        (scheduledSeedNext (R := R) source target N P T S H pass seed draw)} ≤
      Real.exp (10 * H - (H : ℝ) ^ 2) := by
  classical
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hA : (1 : ℚ) ≤ scheduledSeedFactor N pass := by
    unfold scheduledSeedFactor
    exact one_le_pow₀ (by norm_num)
  have hAupper : scheduledSeedFactor N pass ≤ ((integerParameters N).initialFactor : ℚ) := by
    unfold scheduledSeedFactor
    rw [← computedSeed_initial_factor]
    exact dyadicSeedFactor_bound _ _ _
  have hcopies : 0 < H ^ 2 := by rw [hHeq]; exact pow_pos (Nat.two_pow_pos _) 2
  have h := physicalMedianUpdate_computed_failure (R := R) source target N hN hell hMeq hJeq
    (clampedSeedNat seed) P hPeq (scheduledSeedFactor N pass) hA hAupper hsize hseed T S hTeq hSeq hHeq
    bernstein (scheduledSeedMultiplier N pass) (H ^ 2) (scheduledSeedMultiplier_spec N pass hf hpass) hcopies rfl
  have hevents : {draw | ¬ physicalSeedGood source target (scheduledSeedFactor N (pass + 1))
        (scheduledSeedNext (R := R) source target N P T S H pass seed draw)} =
      {draw : ScheduledSeedDraw (R := R) source target N P T H pass seed | ¬ ∀ state : PhysicalEntry M J target.length,
        stateEditCost (physicalSource source state.1) target state.2 ≤
          physicalMedianUpdate source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
            T delta (scheduledSeedMultiplier N pass) S (H ^ 2)
            (physicalProgramDrawSelections source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
              T thetaExponent H (ell ^ 80) tau eta kappa) draw state ∧
        physicalMedianUpdate source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
            T delta (scheduledSeedMultiplier N pass) S (H ^ 2)
            (physicalProgramDrawSelections source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
              T thetaExponent H (ell ^ 80) tau eta kappa) draw state ≤
          4 * scheduledSeedMultiplier N pass * stateEditCost (physicalSource source state.1) target state.2} := by
    ext draw
    rw [scheduledSeedFactor_succ N pass hf hpass]
    exact not_congr (physicalMedianUpdateTable_good_iff _ _ _ _ _ _ _ _ _ _ _ _ _ draw)
  rw [hevents]
  exact h

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
 theorem scheduledSeedLaw_failure (incoming : Measure Seed) [IsProbabilityMeasure incoming] :
    (scheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)).real
      {seed | ¬ physicalSeedGood source target (scheduledSeedFactor N (computedSeedPassCount N)) seed} ≤
      incoming.real {seed | ¬ physicalSeedGood source target (scheduledSeedFactor N 0) seed} +
        computedSeedPassCount N * Real.exp (10 * H - (H : ℝ) ^ 2) := by
  classical
  have h := adaptiveSeedSequence_failure
    (scheduledSeedDrawLaw (R := R) source target N P T H) incoming
    (scheduledSeedNext (R := R) source target N P T S H)
    (fun pass => physicalSeedGood source target (scheduledSeedFactor N pass))
    (fun _ => Real.exp (10 * H - (H : ℝ) ^ 2)) (fun _ => (Real.exp_pos _).le) (computedSeedPassCount N)
    (fun pass hp seed hg => scheduledSeedNext_failure source target N P T S H hN hell hMeq hJeq
      hPeq hTeq hSeq hHeq hsize bernstein pass hp seed hg)
  simpa only [scheduledSeedLaw, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
 theorem scheduledSeedLaw_failure_lt (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (hinitial : incoming.real {seed | ¬ physicalSeedGood source target
      ((integerParameters N).initialFactor : ℚ) seed} ≤ 1 / 100) :
    (scheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)).real
      {seed | ¬ physicalSeedGood source target (scheduledSeedFactor N (computedSeedPassCount N)) seed} < 1 / 10 := by
  classical
  have hbound := scheduledSeedLaw_failure (R := R) source target N P T S H hN hell hMeq hJeq hPeq
    hTeq hSeq hHeq hsize bernstein incoming
  rw [scheduledSeedFactor_zero] at hbound
  have hsmall : 256 ≤ (2 : ℕ) ^ 1000 := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
    norm_num only [show (2 : ℕ) ^ 8 = 256 by norm_num] at h
    exact h
  have hcut : 200 ≤ ell := by omega
  apply (hbound.trans (add_le_add hinitial le_rfl)).trans_lt
  rw [hHeq]
  exact computed_seed_total_failure N (computedSeedPassCount N) hN hcut
    (computedSeedPassCount_le_height N hN hell)

end Program

end EditApproximation

end OAI
