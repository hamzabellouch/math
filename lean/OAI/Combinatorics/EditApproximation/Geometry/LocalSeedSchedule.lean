import OAI.Combinatorics.EditApproximation.Geometry.LocalMedianDrawLaw
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSeedSchedule

namespace OAI

/-! The seed schedule run with bounded local random keys. A whole incoming
seed chooses one fresh product of full-copy local streams. The failure
bound follows from the actual local median law, rather than a seed oracle. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

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

abbrev LocalScheduledSeedDraw (pass : ℕ) (seed : Seed) := Fin (H ^ 2) →
  PhysicalLocalProgramDraw (R := R) source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) tau

noncomputable instance localScheduledSeedDrawFintype (pass : ℕ) (seed : Seed) :
    Fintype (LocalScheduledSeedDraw (R := R) source target N P T H pass seed) := by
  classical
  exact Fintype.ofFinite _

noncomputable def localScheduledSeedDrawLaw (pass : ℕ) (seed : Seed) :
    Measure (LocalScheduledSeedDraw (R := R) source target N P T H pass seed) :=
  Measure.pi fun _ : Fin (H ^ 2) => physicalLocalProgramDrawLaw (R := R)
    source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
      T thetaExponent H (ell ^ 80) tau

instance localScheduledSeedDrawLaw_probability (pass : ℕ) (seed : Seed) :
    IsProbabilityMeasure (localScheduledSeedDrawLaw (R := R) source target N P T H pass seed) := by
  unfold localScheduledSeedDrawLaw physicalLocalProgramDrawLaw
  infer_instance

noncomputable def localScheduledSeedNext (pass : ℕ) (seed : Seed)
    (draw : LocalScheduledSeedDraw (R := R) source target N P T H pass seed) : Seed :=
  physicalLocalMedianUpdateTable source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) tau eta kappa delta
    (scheduledSeedMultiplier N pass) S (H ^ 2) draw

noncomputable def localScheduledSeedLaw (incoming : Measure Seed) (passes : ℕ) : Measure Seed := by
  classical
  exact adaptiveSeedSequence (localScheduledSeedDrawLaw (R := R) source target N P T H) incoming
    (localScheduledSeedNext (R := R) source target N P T S H) passes

instance localScheduledSeedLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (passes : ℕ) :
    IsProbabilityMeasure (localScheduledSeedLaw (R := R) source target N P T S H incoming passes) := by
  unfold localScheduledSeedLaw
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

include hN hPeq hsize in
theorem localScheduledSeedNext_event (pass : ℕ) (seed : Seed)
    (hseed : physicalSeedGood source target (scheduledSeedFactor N pass) seed)
    (event : Set Seed) :
    (localScheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
      {draw | localScheduledSeedNext (R := R) source target N P T S H pass seed draw ∈ event} =
    (scheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
      {draw | scheduledSeedNext (R := R) source target N P T S H pass seed draw ∈ event} := by
  have hP : 66 ≤ P := computed_program_grid_lower N P hN hPeq
  have hF : 1 ≤ ell := Nat.one_le_two_pow
  have hA : (1 : ℚ) ≤ scheduledSeedFactor N pass := by
    unfold scheduledSeedFactor
    exact one_le_pow₀ (by norm_num)
  exact physicalLocalMedianUpdateTable_event (R := R) source target (clampedSeedNat seed)
    N P ell (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) tau eta kappa delta
    (scheduledSeedMultiplier N pass) S (H ^ 2) hsize hP hF hA hseed event

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
theorem localScheduledSeedNext_failure (pass : ℕ) (hpass : pass < computedSeedPassCount N)
    (seed : Seed) (hseed : physicalSeedGood source target (scheduledSeedFactor N pass) seed) :
    (localScheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
      {draw | ¬ physicalSeedGood source target (scheduledSeedFactor N (pass + 1))
        (localScheduledSeedNext (R := R) source target N P T S H pass seed draw)} ≤
      Real.exp (10 * H - (H : ℝ) ^ 2) := by
  have hevent := localScheduledSeedNext_event (R := R) source target N P T S H hN hPeq hsize
    pass seed hseed {next | ¬ physicalSeedGood source target (scheduledSeedFactor N (pass + 1)) next}
  simp only [Set.mem_ofPred_eq] at hevent
  rw [hevent]
  exact scheduledSeedNext_failure source target N P T S H hN hell hMeq hJeq hPeq hTeq hSeq hHeq
    hsize bernstein pass hpass seed hseed

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
theorem localScheduledSeedLaw_failure (incoming : Measure Seed) [IsProbabilityMeasure incoming] :
    (localScheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)).real
      {seed | ¬ physicalSeedGood source target (scheduledSeedFactor N (computedSeedPassCount N)) seed} ≤
      incoming.real {seed | ¬ physicalSeedGood source target (scheduledSeedFactor N 0) seed} +
        computedSeedPassCount N * Real.exp (10 * H - (H : ℝ) ^ 2) := by
  classical
  have h := adaptiveSeedSequence_failure
    (localScheduledSeedDrawLaw (R := R) source target N P T H) incoming
    (localScheduledSeedNext (R := R) source target N P T S H)
    (fun pass => physicalSeedGood source target (scheduledSeedFactor N pass))
    (fun _ => Real.exp (10 * H - (H : ℝ) ^ 2)) (fun _ => (Real.exp_pos _).le) (computedSeedPassCount N)
    (fun pass hp seed hg => localScheduledSeedNext_failure source target N P T S H
      hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein pass hp seed hg)
  simpa only [localScheduledSeedLaw, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
theorem localScheduledSeedLaw_failure_lt (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (hinitial : incoming.real {seed | ¬ physicalSeedGood source target
      ((integerParameters N).initialFactor : ℚ) seed} ≤ 1 / 100) :
    (localScheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)).real
      {seed | ¬ physicalSeedGood source target (scheduledSeedFactor N (computedSeedPassCount N)) seed} < 1 / 10 := by
  have hbound := localScheduledSeedLaw_failure (R := R) source target N P T S H hN hell hMeq hJeq hPeq
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
