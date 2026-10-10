import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSeedSchedule
import OAI.Combinatorics.EditApproximation.Probability.FiniteSeedFinal

namespace OAI

/-! Accuracy of the final fresh refinement after adaptive median seed passes,
under finite Bernstein bounds and an explicit incoming seed failure bound. -/

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

abbrev FinalProgramDraw (seed : Seed) :=
  PhysicalProgramDraw (R := R) source target (clampedSeedNat seed) N P ell terminalFactor
    T thetaExponent H (ell ^ 80) tau

noncomputable def finalProgramDrawLaw (seed : Seed) :
    Measure (FinalProgramDraw (R := R) source target N P T H seed) :=
  physicalProgramDrawLaw (R := R) source target (clampedSeedNat seed) N P ell terminalFactor
    T thetaExponent H (ell ^ 80) tau

instance finalProgramDrawLaw_probability (seed : Seed) :
    IsProbabilityMeasure (finalProgramDrawLaw (R := R) source target N P T H seed) := by
  unfold finalProgramDrawLaw
  infer_instance

noncomputable def finalProgramValue (rootQ : TargetInterval target.length) (seed : Seed)
    (draw : FinalProgramDraw (R := R) source target N P T H seed) : ℝ :=
  physicalRefinement source target (clampedSeedNat seed) N P ell terminalFactor T delta
    (physicalProgramDrawSelections source target (clampedSeedNat seed) N P ell terminalFactor
      T thetaExponent H (ell ^ 80) tau eta kappa draw)
    (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J) S rootQ

abbrev FinalProgramOutcome := Seed × (∀ seed : Seed, FinalProgramDraw (R := R) source target N P T H seed)

noncomputable def finalProgramLaw (incoming : Measure Seed) :
    Measure (FinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) := by
  classical
  exact (scheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)).prod
    (Measure.pi (finalProgramDrawLaw (R := R) source target N P T H))

instance finalProgramLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming] :
    IsProbabilityMeasure (finalProgramLaw (R := R) source target N P T S H incoming) := by
  unfold finalProgramLaw
  infer_instance

/-- Equality is tested before the final query, so equal strings return zero
on every execution, including executions with a bad seed. -/
noncomputable def finalProgramAnswer (rootQ : TargetInterval target.length)
    (pair : FinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) : ℕ :=
  if source = substring target rootQ.lo rootQ.hi then 0 else
    integerAnswer N (freshSeedValue (finalProgramValue (M := M) (J := J) (R := R) source target N P T S H rootQ) pair)

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem finalProgramAnswer_equal (rootQ : TargetInterval target.length)
    (heq : source = substring target rootQ.lo rootQ.hi)
    (pair : FinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) :
    finalProgramAnswer (R := R) source target N P T S H rootQ pair = 0 := by
  simp only [finalProgramAnswer, heq, ite_true]

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
theorem finalProgram_accuracy (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (hinitial : incoming.real {seed | ¬ physicalSeedGood source target
      ((integerParameters N).initialFactor : ℚ) seed} ≤ 1 / 100)
    (rootQ : TargetInterval target.length) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (haccuracy : 10 ≤ (inputSmallLog N : ℝ) * epsilon) :
    (4 / 5 : ℝ) ≤ (finalProgramLaw (R := R) source target N P T S H incoming).real
      {pair | stateEditCost source target rootQ ≤
        finalProgramAnswer (R := R) source target N P T S H rootQ pair ∧
        (finalProgramAnswer (R := R) source target N P T S H rootQ pair : ℝ) ≤
          (1 + epsilon) * stateEditCost source target rootQ} := by
  classical
  by_cases heq : source = substring target rootQ.lo rootQ.hi
  · have hcost : stateEditCost source target rootQ = 0 :=
      (EditDistortion.cost_eq_zero_iff (s := true)).mpr heq
    have hans (pair : FinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) :
        finalProgramAnswer (R := R) source target N P T S H rootQ pair = 0 :=
      finalProgramAnswer_equal source target N P T S H rootQ heq pair
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
  let terminalLaw := scheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)
  let good : Seed → Prop := physicalSeedGood source target terminalFactor
  let value := finalProgramValue (M := M) (J := J) (R := R) source target N P T S H rootQ
  have hseed : terminalLaw.real {seed | ¬ good seed} ≤ 1 / 10 :=
    (scheduledSeedLaw_failure_lt (R := R) source target N P T S H hN hell hMeq hJeq hPeq
      hTeq hSeq hHeq hsize bernstein incoming hinitial).le
  have hlower (seed : Seed) (hg : good seed) (draw : FinalProgramDraw (R := R) source target N P T H seed) :
      (stateEditCost source target rootQ : ℝ) ≤ value seed draw := by
    have h := (physicalRefinement_stage_bounds source target hbranch (clampedSeedNat seed) N P ell
      terminalFactor hsize hP hF hA hg T hT delta
      (physicalProgramDrawSelections source target (clampedSeedNat seed) N P ell terminalFactor
        T thetaExponent H (ell ^ 80) tau eta kappa draw)
      (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J) S rootQ).1
    have hleft := (le_max_left _ _).trans h
    simpa only [value, finalProgramValue, ha, Rat.cast_one, div_one, physicalSource, physicalSourceInterval,
      sourceIntervalAt, substring, List.take_length, List.drop_zero] using hleft
  have hmoment (seed : Seed) (hg : good seed) :
      (∫ draw, max (value seed draw - stateEditCost source target rootQ) 0
        ∂finalProgramDrawLaw (R := R) source target N P T H seed) ≤
        (stateEditCost source target rootQ : ℝ) / ell := by
    have h := physicalProgram_expected_root_excess (R := R) source target N hN hell hMeq hJeq
      (clampedSeedNat seed) P hPeq terminalFactor hA hAupper hsize hg T S hTeq hSeq hHeq bernstein rootQ
    simpa only [value, finalProgramValue, finalProgramDrawLaw, one_div_mul_eq_div] using h
  have hDN : stateEditCost source target rootQ ≤ N := by
    have h := physical_state_cost_le (M := M) (J := J) source target N hsize
      ((Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J), rootQ)
    simpa only [physicalSource, physicalSourceInterval, sourceIntervalAt, substring,
      List.take_length, List.drop_zero] using h
  have h := freshSeed_answer_accuracy (finalProgramDrawLaw (R := R) source target N P T H)
    terminalLaw good value hDN hD hEll hepsilon haccuracy hseed hlower hmoment
  simpa only [finalProgramLaw, finalProgramAnswer, heq, ite_false, terminalLaw, value] using h

end Final

end EditApproximation

end OAI
