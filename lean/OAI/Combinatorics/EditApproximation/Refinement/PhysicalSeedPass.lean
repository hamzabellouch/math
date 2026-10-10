import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSeedMedian
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalProgramStateAccuracy
import OAI.Combinatorics.EditApproximation.Geometry.SeedPassNumerics

namespace OAI

/-! A full-table median seed pass from independent refinement copies under finite Bernstein bounds. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def physicalMedianUpdate {α Ω : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ) (a S copies : ℕ)
    (choices : Ω → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (draws : Fin copies → Ω)
    (state : PhysicalEntry M J target.length) : ℕ :=
  finiteMedianSeed N copies
    (fun draw => physicalScaledCopy source target U N P F A T delta a S (choices draw) state) draws

section Pass

variable {α : Type*} [DecidableEq α] {M J R H : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (U : PhysicalEntry M J target.length → ℕ) (P : ℕ) (hPeq : P = (integerParameters N).P)
  (A : ℚ) (hA : 1 ≤ A) (hAupper : A ≤ (integerParameters N).initialFactor)
  (hsize : source.length + target.length ≤ N)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T S : ℕ) (hTeq : T = (integerParameters N).T) (hSeq : S = (integerParameters N).S)
  (hHeq : H = inputHeight N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))
  (a copies : ℕ) (ha : (a : ℚ) = refinementFactor A (inputSmallLog N)) (hcopies : 0 < copies)

local notation "ell" => inputSmallLog N
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P ell A T thetaExponent H (ell ^ 80) tau
local notation "choices" => physicalProgramDrawSelections source target U N P ell A T thetaExponent H (ell ^ 80) tau eta kappa
local notation "law" => physicalProgramDrawLaw (R := R) source target U N P ell A T thetaExponent H (ell ^ 80) tau
local notation "copyLaw" => Measure.pi (fun _ : Fin copies => law)
local notation "update" => physicalMedianUpdate source target U N P ell A T delta a S copies choices

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
include hN hell hPeq hA hsize hseed hTeq ha hcopies in
 theorem physicalMedianUpdate_lower (draws : Fin copies → Draw) (state : PhysicalEntry M J target.length) :
    stateEditCost (physicalSource source state.1) target state.2 ≤ update draws state := by
  classical
  have hbranch : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hP := computed_program_grid_lower N P hN hPeq
  have hF : 1 ≤ ell := Nat.one_le_two_pow
  have hT : 0 < T := by rw [hTeq]; exact (computed_stage_positive_counts N hN hell).1
  exact finiteMedianSeed_lower N copies _ hcopies (physical_state_cost_le source target N hsize state) _
    (fun draw => physicalScaledCopy_lower source target hbranch U N P ell A hsize hP hF hA hseed
      T hT delta a S ha (choices draw) state) draws

include hN hell hMeq hJeq hPeq hA hAupper hsize hseed hTeq hSeq hHeq bernstein ha hcopies in
 theorem physicalMedianUpdate_state_failure (state : PhysicalEntry M J target.length) :
    (copyLaw).real {draws | 2 * a * stateEditCost (physicalSource source state.1) target state.2 < update draws state} ≤
      (2 : ℝ) ^ copies * (1 / (ell : ℝ)) ^ (copies - copies / 2) := by
  classical
  let c := stateEditCost (physicalSource source state.1) target state.2
  let value : Draw → ℚ := fun draw => physicalRefinement source target U N P ell A T delta (choices draw) state.1 S state.2
  let output : Draw → ℕ := fun draw => physicalScaledCopy source target U N P ell A T delta a S (choices draw) state
  have hbranch : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hP := computed_program_grid_lower N P hN hPeq
  have hF : 1 ≤ ell := Nat.one_le_two_pow
  have hT : 0 < T := by rw [hTeq]; exact (computed_stage_positive_counts N hN hell).1
  have haQ : (0 : ℚ) < a := by
    rw [ha]
    exact lt_of_lt_of_le zero_lt_one (refinementFactor_spec A ell (by omega)).1
  have hsingle : (law).real {draw | 2 * a * c < output draw} ≤ 1 / (ell : ℝ) := by
    by_cases hzero : c = 0
    · have hout (draw : Draw) : output draw = 0 := by
        have hz := physicalRefinement_zero_cost source target hbranch U N P ell A hsize hP hF hA hseed
          T hT delta (choices draw) state.1 S state.2 hzero
        simp only [output, physicalScaledCopy, hz, mul_zero, Nat.ceil_zero]
      simp only [hzero, mul_zero, hout, lt_self_iff_false, Set.ofPred_false, measureReal_empty]
      exact div_nonneg zero_le_one (Nat.cast_nonneg _)
    · have hexcess := physicalProgram_expected_state_excess (R := R) source target N hN hell hMeq hJeq
        U P hPeq A hA hAupper hsize hseed T S hTeq hSeq hHeq bernstein state.1 state.2
      have hraw := finite_positive_excess_tail law value c (Nat.pos_of_ne_zero hzero)
        (ell : ℝ) (Nat.cast_pos.2 (Nat.two_pow_pos _)) hexcess
      apply (measureReal_mono (μ := law) ?_ (measure_ne_top _ _)).trans hraw
      intro draw hbad
      by_contra hnot
      have hvalue : value draw ≤ 2 * c := le_of_not_gt hnot
      have hround : output draw ≤ 2 * a * c := by
        apply Nat.ceil_le.mpr
        have hm := mul_le_mul_of_nonneg_left hvalue haQ.le
        push_cast
        nlinarith only [hm]
      exact (not_lt_of_ge hround) hbad
  exact finiteMedianSeed_failure_bound law N copies (2 * a * c) hcopies output
    (1 / (ell : ℝ)) (div_nonneg zero_le_one (Nat.cast_nonneg _)) hsingle

include hN hell hMeq hJeq hPeq hA hAupper hsize hseed hTeq hSeq hHeq bernstein ha hcopies in
 theorem physicalMedianUpdate_all_failure :
    (copyLaw).real {draws | ¬ ∀ state : PhysicalEntry M J target.length,
      stateEditCost (physicalSource source state.1) target state.2 ≤ update draws state ∧
      update draws state ≤ 4 * a * stateEditCost (physicalSource source state.1) target state.2} ≤
      Fintype.card (PhysicalEntry M J target.length) *
        ((2 : ℝ) ^ copies * (1 / (ell : ℝ)) ^ (copies - copies / 2)) := by
  classical
  let bad := fun state : PhysicalEntry M J target.length =>
    {draws : Fin copies → Draw | 2 * a * stateEditCost (physicalSource source state.1) target state.2 < update draws state}
  have hcover : {draws | ¬ ∀ state : PhysicalEntry M J target.length,
      stateEditCost (physicalSource source state.1) target state.2 ≤ update draws state ∧
      update draws state ≤ 4 * a * stateEditCost (physicalSource source state.1) target state.2} ⊆ ⋃ state, bad state := by
    intro draws hfail
    obtain ⟨state, hstate⟩ := not_forall.mp hfail
    apply Set.mem_iUnion.mpr
    refine ⟨state, ?_⟩
    have hlower := physicalMedianUpdate_lower (R := R) source target N hN hell U P hPeq A hA
      hsize hseed T S hTeq a copies ha hcopies draws state
    have hu : 4 * a * stateEditCost (physicalSource source state.1) target state.2 < update draws state := by
      exact lt_of_not_ge (fun h => hstate ⟨hlower, h⟩)
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right a (by decide : 2 ≤ 4))) hu
  apply (measureReal_mono (μ := copyLaw) hcover (measure_ne_top _ _)).trans
  apply (measureReal_iUnion_fintype_le bad).trans
  have hsum := sum_le_sum (fun state (_ : state ∈ (univ : Finset (PhysicalEntry M J target.length))) =>
    physicalMedianUpdate_state_failure (R := R) source target N hN hell hMeq hJeq U P hPeq A hA hAupper
      hsize hseed T S hTeq hSeq hHeq bernstein a copies ha hcopies state)
  simpa only [sum_const, card_univ, nsmul_eq_mul] using hsum

include hN hell hMeq hJeq hPeq hA hAupper hsize hseed hTeq hSeq hHeq bernstein ha hcopies in
 theorem physicalMedianUpdate_computed_failure (hcopiesEq : copies = H ^ 2) :
    (copyLaw).real {draws | ¬ ∀ state : PhysicalEntry M J target.length,
      stateEditCost (physicalSource source state.1) target state.2 ≤ update draws state ∧
      update draws state ≤ 4 * a * stateEditCost (physicalSource source state.1) target state.2} ≤
      Real.exp (10 * H - (H : ℝ) ^ 2) := by
  classical
  have hsmall : 256 ≤ (2 : ℕ) ^ 1000 := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
    norm_num only [show (2 : ℕ) ^ 8 = 256 by norm_num] at h
    exact h
  have hcut : 200 ≤ ell := by omega
  have hcard : Fintype.card (PhysicalEntry M J target.length) ≤ labeledStateCount M source.length target.length := by
    rw [hJeq]
    exact labeledEntry_card_le M source.length target.length
  have hcardR : (Fintype.card (PhysicalEntry M J target.length) : ℝ) ≤ Real.exp (10 * H) := by
    apply (Nat.cast_le.mpr hcard).trans
    rw [hMeq, hHeq]
    exact computed_labeledStateCount_exp N source.length target.length hN (by omega) (by omega) hcut
  have htail := seed_copy_binary_tail copies ell (by omega : 64 ≤ ell)
  have hbound := physicalMedianUpdate_all_failure (R := R) source target N hN hell hMeq hJeq U P hPeq
    A hA hAupper hsize hseed T S hTeq hSeq hHeq bernstein a copies ha hcopies
  apply hbound.trans
  apply (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)).trans
  rw [hcopiesEq, Nat.cast_pow]
  exact seed_state_union_numeric (H : ℝ) (Fintype.card (PhysicalEntry M J target.length) : ℝ) hcardR

end Pass

end EditApproximation

end OAI
