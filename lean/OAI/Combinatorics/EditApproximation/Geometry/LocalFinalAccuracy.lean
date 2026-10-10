import OAI.Combinatorics.EditApproximation.Geometry.LocalSeedSchedule
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalValueLaw
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalConditionalAccuracy

namespace OAI

/-! The final fresh bounded-key local query, following the actual local
median schedule, has the required approximation probability. The incoming
law is supplied by the concrete coarse sampler in the final theorem. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Final

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "terminalFactor" => scheduledSeedFactor N (computedSeedPassCount N)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

abbrev LocalFinalProgramDraw (seed : Seed) :=
  PhysicalLocalProgramDraw (R := R) source target (clampedSeedNat seed) N P ell terminalFactor
    T thetaExponent H (ell ^ 80) tau

noncomputable def localFinalProgramDrawLaw (seed : Seed) :
    Measure (LocalFinalProgramDraw (R := R) source target N P T H seed) :=
  physicalLocalProgramDrawLaw (R := R) source target (clampedSeedNat seed) N P ell terminalFactor
    T thetaExponent H (ell ^ 80) tau

instance localFinalProgramDrawLaw_probability (seed : Seed) :
    IsProbabilityMeasure (localFinalProgramDrawLaw (R := R) source target N P T H seed) := by
  unfold localFinalProgramDrawLaw
  infer_instance

noncomputable def localFinalProgramValue (rootQ : TargetInterval target.length) (seed : Seed)
    (draw : LocalFinalProgramDraw (R := R) source target N P T H seed) : ℝ :=
  physicalLocalJointValue source target (clampedSeedNat seed) N P ell terminalFactor
    T thetaExponent H (ell ^ 80) tau eta kappa delta draw
    (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J) S rootQ

abbrev LocalFinalProgramOutcome :=
  Seed × (∀ seed : Seed, LocalFinalProgramDraw (R := R) source target N P T H seed)

noncomputable def localFinalProgramLaw (incoming : Measure Seed) :
    Measure (LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) := by
  classical
  exact (localScheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)).prod
    (Measure.pi (localFinalProgramDrawLaw (R := R) source target N P T H))

instance localFinalProgramLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming] :
    IsProbabilityMeasure (localFinalProgramLaw (R := R) source target N P T S H incoming) := by
  unfold localFinalProgramLaw
  infer_instance

noncomputable def localFinalProgramAnswer (rootQ : TargetInterval target.length)
    (pair : LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) : ℕ :=
  if source = substring target rootQ.lo rootQ.hi then 0 else
    integerAnswer N (freshSeedValue
      (localFinalProgramValue (M := M) (J := J) (R := R) source target N P T S H rootQ) pair)

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localFinalProgramAnswer_equal (rootQ : TargetInterval target.length)
    (heq : source = substring target rootQ.lo rootQ.hi)
    (pair : LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) :
    localFinalProgramAnswer (R := R) source target N P T S H rootQ pair = 0 := by
  simp only [localFinalProgramAnswer, heq, ite_true]

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localFinalProgramValue_eq (rootQ : TargetInterval target.length) (seed : Seed)
    (draw : LocalFinalProgramDraw (R := R) source target N P T H seed)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P)
    (hseed : physicalSeedGood source target terminalFactor seed) :
    localFinalProgramValue source target N P T S H rootQ seed draw =
      finalProgramValue source target N P T S H rootQ seed
        (physicalLocalProgramToComplete source target (clampedSeedNat seed) N P ell terminalFactor
          T thetaExponent H (ell ^ 80) tau hsize hP Nat.one_le_two_pow
          (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)) hseed draw) := by
  unfold localFinalProgramValue finalProgramValue
  rw [physicalLocalJointValue_eq source target (clampedSeedNat seed) N P ell terminalFactor
    T thetaExponent H (ell ^ 80) tau eta kappa delta draw hsize hP Nat.one_le_two_pow
    (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)) hseed]

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
theorem localFinalProgram_accuracy (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (hinitial : incoming.real {seed | ¬ physicalSeedGood source target
      ((integerParameters N).initialFactor : ℚ) seed} ≤ 1 / 100)
    (rootQ : TargetInterval target.length) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (haccuracy : 10 ≤ (inputSmallLog N : ℝ) * epsilon) :
    (4 / 5 : ℝ) ≤ (localFinalProgramLaw (R := R) source target N P T S H incoming).real
      {pair | stateEditCost source target rootQ ≤
        localFinalProgramAnswer (R := R) source target N P T S H rootQ pair ∧
        (localFinalProgramAnswer (R := R) source target N P T S H rootQ pair : ℝ) ≤
          (1 + epsilon) * stateEditCost source target rootQ} := by
  classical
  by_cases heq : source = substring target rootQ.lo rootQ.hi
  · have hcost : stateEditCost source target rootQ = 0 :=
      (EditDistortion.cost_eq_zero_iff (s := true)).mpr heq
    have hans (pair : LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) :
        localFinalProgramAnswer (R := R) source target N P T S H rootQ pair = 0 :=
      localFinalProgramAnswer_equal source target N P T S H rootQ heq pair
    simp only [hans, hcost, Nat.cast_zero, mul_zero, le_refl, and_self, Set.ofPred_true, probReal_univ]
    norm_num
  have hD : 0 < stateEditCost source target rootQ :=
    Nat.pos_of_ne_zero (fun h => heq ((EditDistortion.cost_eq_zero_iff (s := true)).mp h))
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hA : (1 : ℚ) ≤ terminalFactor := by
    unfold scheduledSeedFactor
    exact one_le_pow₀ (by norm_num)
  have hAupper : terminalFactor ≤ ((integerParameters N).initialFactor : ℚ) := by
    unfold scheduledSeedFactor
    rw [← computedSeed_initial_factor]
    exact dyadicSeedFactor_bound _ _ _
  have ha := scheduledSeedFactor_terminal_refinement N hf
  have hbranch : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hP := computed_program_grid_lower N P hN hPeq
  have hF : 1 ≤ ell := Nat.one_le_two_pow
  have hT : 0 < T := by rw [hTeq]; exact (computed_stage_positive_counts N hN hell).1
  have hEll : (0 : ℝ) < ell := Nat.cast_pos.2 (Nat.two_pow_pos _)
  let terminalLaw := localScheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)
  let good : Seed → Prop := physicalSeedGood source target terminalFactor
  let value := localFinalProgramValue (M := M) (J := J) (R := R) source target N P T S H rootQ
  have hseed : terminalLaw.real {seed | ¬ good seed} ≤ 1 / 10 :=
    (localScheduledSeedLaw_failure_lt (R := R) source target N P T S H hN hell hMeq hJeq hPeq
      hTeq hSeq hHeq hsize bernstein incoming hinitial).le
  have hlower (seed : Seed) (hg : good seed)
      (draw : LocalFinalProgramDraw (R := R) source target N P T H seed) :
      (stateEditCost source target rootQ : ℝ) ≤ value seed draw := by
    rw [show value seed draw = finalProgramValue source target N P T S H rootQ seed
      (physicalLocalProgramToComplete source target (clampedSeedNat seed) N P ell terminalFactor
        T thetaExponent H (ell ^ 80) tau hsize hP hF hA hg draw) from
      localFinalProgramValue_eq source target N P T S H rootQ seed draw hsize hP hg]
    have h := (physicalRefinement_stage_bounds source target hbranch (clampedSeedNat seed) N P ell
      terminalFactor hsize hP hF hA hg T hT delta
      (physicalProgramDrawSelections source target (clampedSeedNat seed) N P ell terminalFactor
        T thetaExponent H (ell ^ 80) tau eta kappa
        (physicalLocalProgramToComplete source target (clampedSeedNat seed) N P ell terminalFactor
          T thetaExponent H (ell ^ 80) tau hsize hP hF hA hg draw))
      (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J) S rootQ).1
    have hleft := (le_max_left _ _).trans h
    simpa only [finalProgramValue, ha, Rat.cast_one, div_one, physicalSource, physicalSourceInterval,
      sourceIntervalAt, substring, List.take_length, List.drop_zero] using hleft
  have hmoment (seed : Seed) (hg : good seed) :
      (∫ draw, max (value seed draw - stateEditCost source target rootQ) 0
        ∂localFinalProgramDrawLaw (R := R) source target N P T H seed) ≤
        (stateEditCost source target rootQ : ℝ) / ell := by
    let project := physicalLocalProgramToComplete (R := R) source target (clampedSeedNat seed)
      N P ell terminalFactor T thetaExponent H (ell ^ 80) tau hsize hP hF hA hg
    let fullValue := finalProgramValue (M := M) (J := J) (R := R) source target N P T S H rootQ seed
    have hpoint (draw : LocalFinalProgramDraw (R := R) source target N P T H seed) :
        value seed draw = fullValue (project draw) :=
      localFinalProgramValue_eq source target N P T S H rootQ seed draw hsize hP hg
    have hmap : (localFinalProgramDrawLaw (R := R) source target N P T H seed).map project =
        finalProgramDrawLaw (R := R) source target N P T H seed :=
      physicalLocalProgramDrawLaw_map source target (clampedSeedNat seed) N P ell terminalFactor
        T thetaExponent H (ell ^ 80) tau hsize hP hF hA hg
    have hcomp := integral_map (μ := localFinalProgramDrawLaw (R := R) source target N P T H seed)
      (φ := project) (measurable_of_finite _).aemeasurable
      (f := fun draw => max (fullValue draw - stateEditCost source target rootQ) 0)
      (measurable_of_finite _).aestronglyMeasurable
    have hfull := physicalProgram_expected_root_excess (R := R) source target N hN hell hMeq hJeq
      (clampedSeedNat seed) P hPeq terminalFactor hA hAupper hsize hg T S hTeq hSeq hHeq bernstein rootQ
    calc
      (∫ draw, max (value seed draw - stateEditCost source target rootQ) 0
          ∂localFinalProgramDrawLaw (R := R) source target N P T H seed) =
          ∫ draw, max (fullValue (project draw) - stateEditCost source target rootQ) 0
            ∂localFinalProgramDrawLaw (R := R) source target N P T H seed := by
        apply integral_congr_ae
        filter_upwards [] with draw
        rw [hpoint]
      _ = ∫ draw, max (fullValue draw - stateEditCost source target rootQ) 0
          ∂finalProgramDrawLaw (R := R) source target N P T H seed := by rw [← hcomp, hmap]
      _ ≤ (stateEditCost source target rootQ : ℝ) / ell := by
        simpa only [fullValue, finalProgramValue, finalProgramDrawLaw, one_div_mul_eq_div] using hfull
  have hDN : stateEditCost source target rootQ ≤ N := by
    have h := physical_state_cost_le (M := M) (J := J) source target N hsize
      ((Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J), rootQ)
    simpa only [physicalSource, physicalSourceInterval, sourceIntervalAt, substring,
      List.take_length, List.drop_zero] using h
  have h := freshSeed_answer_accuracy (localFinalProgramDrawLaw (R := R) source target N P T H)
    terminalLaw good value hDN hD hEll hepsilon haccuracy hseed hlower hmoment
  simpa only [localFinalProgramLaw, localFinalProgramAnswer, heq, ite_false, terminalLaw, value] using h

noncomputable def localWholeFinalAnswer
    (pair : LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) : ℕ :=
  localFinalProgramAnswer (R := R) source target N P T S H (finalTargetState target.length) pair

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localWholeFinalAnswer_equal (heq : source = target)
    (pair : LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) :
    localWholeFinalAnswer (R := R) source target N P T S H pair = 0 := by
  apply localFinalProgramAnswer_equal
  simpa only [finalTargetState, substring, List.take_length, List.drop_zero] using heq

end Final

section Coarse

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H B : ℕ)
  [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

theorem local_physical_conditional_accuracy (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
    (hsize : source.length + target.length ≤ N)
    (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
    (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
    (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
    (hB : B = (integerParameters N).B)
    (hdepth : ∀ state, depth state = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source state.1) (substring target state.2.lo state.2.hi)))
    (coarseBernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure))
    (groupBernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
      FiniteBernsteinInput (Measure.pi fun _ : Fin
        (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
        (PMF.uniformOfFintype (Fin M)).toMeasure))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (haccuracy : 10 ≤ (inputSmallLog N : ℝ) * epsilon) :
    (2 / 3 : ℝ) ≤ (localFinalProgramLaw (R := R) source target N P T S H
      (physicalCoarseSeedLaw source target N B depth)).real
      {pair | EditDistortion.edit source target ≤ localWholeFinalAnswer (R := R) source target N P T S H pair ∧
        (localWholeFinalAnswer (R := R) source target N P T S H pair : ℝ) ≤
          (1 + epsilon) * EditDistortion.edit source target} := by
  classical
  have hsmall : 256 ≤ (2 : ℕ) ^ 1000 := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
    norm_num only [show (2 : ℕ) ^ 8 = 256 by norm_num] at h
    exact h
  have hcut : 200 ≤ inputSmallLog N := by omega
  have hinitial := physicalCoarseSeedLaw_failure source target N B depth hN hsize hcut
    hB hMeq hJeq hdepth coarseBernstein
  have h := localFinalProgram_accuracy (R := R) source target N P T S H hN hell hMeq hJeq hPeq
    hTeq hSeq hHeq hsize groupBernstein (physicalCoarseSeedLaw source target N B depth)
    hinitial.le (finalTargetState target.length) epsilon hepsilon haccuracy
  apply (by norm_num : (2 / 3 : ℝ) ≤ 4 / 5).trans
  simpa only [localWholeFinalAnswer, stateEditCost, finalTargetState, substring,
    List.take_length, List.drop_zero] using h

end Coarse

end EditApproximation

end OAI
