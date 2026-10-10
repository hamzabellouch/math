import OAI.Combinatorics.EditApproximation.Refinement.PhysicalProgramAccuracy
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalProgramSubtreeRegret
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSubtreeBudget

namespace OAI

/-! Expected excess at every original physical table entry, under the same
query-filtered global stream law. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem rooted_refinement_budget_mono {M F P T S ratio velocityTolerance coefficient K J : ℝ}
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hP : 0 ≤ P) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hratio : 0 ≤ ratio) (htau : 0 ≤ velocityTolerance) (hcoef : 0 ≤ coefficient)
    (hKJ : K ≤ J) :
    (8 * M + 512 * F) * K / P +
      (40000 * ratio * F ^ 2 * (1 + K / P + K / T) +
        2 * K * (1 / ratio + 4 * velocityTolerance * F + coefficient)) / S ≤
    (8 * M + 512 * F) * J / P +
      (40000 * ratio * F ^ 2 * (1 + J / P + J / T) +
        2 * J * (1 / ratio + 4 * velocityTolerance * F + coefficient)) / S := by
  gcongr

section Accuracy

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
  (root : PhysicalNode M J) (rootQ : TargetInterval target.length)

local notation "ell" => inputSmallLog N
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P ell A T thetaExponent H (ell ^ 80) tau
local notation "choices" => physicalProgramDrawSelections source target U N P ell A T thetaExponent H (ell ^ 80) tau eta kappa
local notation "globalLaw" => physicalProgramDrawLaw (R := R) source target U N P ell A T thetaExponent H (ell ^ 80) tau

include hN hell hMeq hJeq hPeq hA hAupper hsize hseed hTeq hSeq hHeq bernstein

/-- A pass of the actual rational recurrence has expected positive root
error at most the actual edit cost divided by the computed small logarithm. -/
theorem physicalProgram_expected_state_excess :
    (∫ draw : Draw, max ((physicalRefinement source target U N P ell A T delta (choices draw)
      root S rootQ : ℝ) -
        stateEditCost (physicalSource source root) target rootQ) 0 ∂globalLaw) ≤
      (1 / (ell : ℝ)) * stateEditCost (physicalSource source root) target rootQ := by
  classical
  have hell1764 : 1764 ≤ ell := by
    have hlarge : 4096 ≤ (2 : ℕ) ^ 1000 := by
      have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 12 ≤ 1000)
      norm_num only [show (2 : ℕ) ^ 12 = 4096 by norm_num] at h
      exact h
    omega
  have hell200 : 200 ≤ ell := by omega
  have hF : 1 ≤ ell := Nat.one_le_two_pow
  have hEllQ : (8 : ℚ) ≤ ell := by exact_mod_cast (show 8 ≤ ell by omega)
  have hEllPos : (0 : ℚ) < ell := Nat.cast_pos.2 (Nat.two_pow_pos _)
  have hbranch : 2 ≤ M := by
    rw [hMeq]
    exact (computed_branching_bounds N hN hell200).1
  have hM : 0 < M := by omega
  have hP := computed_program_grid_lower N P hN hPeq
  have hcounts := computed_stage_positive_counts N hN hell
  have hT : 0 < T := by rw [hTeq]; exact hcounts.1
  have hS : 0 < S := by rw [hSeq]; exact hcounts.2
  have hpoly : ell ^ 20000 ≤ inputHeight N := by exact_mod_cast inputHeight_polynomial_slack N hN hell
  have hEllHeight : ell ≤ inputHeight N := by
    have hpow : ell ≤ ell ^ 20000 := by
      simpa only [pow_one] using pow_le_pow_right₀ hF (by decide : 1 ≤ 20000)
    exact hpow.trans hpoly
  have hH : 4 ≤ H := by rw [hHeq]; omega
  have hrange := computed_online_range ell (by omega : 8 ≤ ell)
  have hdelta : 0 < delta := div_pos zero_lt_one (pow_pos hEllPos 10)
  have htau : 0 ≤ tau := (div_pos zero_lt_one (pow_pos hEllPos 4)).le
  have hηrange : (eta : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * ell : ℚ) : ℝ) *
      (((2 : ℚ) ^ (-(thetaExponent : ℤ))) : ℝ)) ≤ (kappa : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, computed_theta_dyadic,
      Rat.cast_zpow] using hrange.2.2.2
  have herror : 2 * (rationalParameters ell).gamma + 512 * (128 * ell : ℚ) * ell *
      (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ kappa * delta := by
    simpa only [← computed_theta_dyadic, rationalParameters] using group_rounded_error_small hEllQ
  have hscale : 2 * (refinementFactor A ell : ℝ) ≤ P := by
    rw [hPeq]
    exact computed_refinementFactor_spacing N hN A hA hAupper
  have hMP : 4 * (M : ℝ) / P ≤ 1 := by
    rw [hMeq, hPeq]
    exact (computed_stage_grid_bounds N hN).2.2
  have hcapacity : source.length ≤ M ^ J := by
    rw [hJeq]
    exact intervalTreeDepth_capacity M source.length hbranch
  have hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2 := by
    rw [hJeq, hMeq, hPeq]
    exact computed_stage_tree_small N source.length hN (by omega) hell200
  have hratio : 0 < heightQuarterRoot N := by
    unfold heightQuarterRoot
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.two_pow_pos _)))
  have hηR : (0 : ℝ) < eta := (Rat.cast_pos (K := ℝ)).mpr hrange.1
  have hκR : (0 : ℝ) ≤ kappa := (Rat.cast_nonneg (K := ℝ)).mpr hrange.2.1
  have hdeltaR : (0 : ℝ) < delta := (Rat.cast_pos (K := ℝ)).mpr hdelta
  have hcoef := physicalProgramNodeCoefficient_nonneg N ell S H eta kappa delta hηR.le hκR hdeltaR.le
  let K := J - root.1.val
  have hK : K ≤ J := Nat.sub_le _ _
  have hheight : root.1.val + K = J := by dsimp only [K]; omega
  have hsmallK : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK)
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))).trans hsmall
  have hgood := fun (d : Fin K) (path : TreeLayer M d.val) =>
    physicalProgram_subtree_node_regret (R := R) source target N hN hell hM hMeq U P hPeq A hA hAupper
      hsize hseed T hT hHeq hH delta eta kappa hdelta hrange.1 hrange.2.1 hrange.2.2.1
      hηrange herror bernstein root K hheight rootQ S d path
  have hbound := subtree_expected_excess_of_good_nodes source target hM U N P ell A
    hsize hP hF hA hseed T hT delta choices root K hheight rootQ globalLaw (heightQuarterRoot N) hratio tau htau
    hscale hMP hcapacity hsmallK S hS (physicalProgramNodeCoefficient N ell eta kappa delta S H) hcoef hgood
  have hbudget : ((8 * (M : ℝ) + 512 * ell) * J / P +
      (40000 * heightQuarterRoot N * (ell : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) +
        2 * J * (1 / heightQuarterRoot N + 4 * (tau : ℝ) * ell +
          physicalProgramNodeCoefficient N ell eta kappa delta S H)) / S) =
        computedRefinementError N source.length := by
    dsimp only [physicalProgramNodeCoefficient, computedRefinementError]
    rw [hJeq, hMeq, hPeq, hTeq, hSeq, hHeq]
    simp only [rationalParameters, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_ofNat]
  have hbudget_le := rooted_refinement_budget_mono (M := (M : ℝ)) (F := (ell : ℝ))
    (P := (P : ℝ)) (T := (T : ℝ)) (S := (S : ℝ)) (ratio := heightQuarterRoot N)
    (velocityTolerance := (tau : ℝ)) (coefficient := physicalProgramNodeCoefficient N ell eta kappa delta S H)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hratio.le ((Rat.cast_nonneg (K := ℝ)).mpr htau) hcoef
    (Nat.cast_le.mpr hK)
  rw [hbudget] at hbudget_le
  exact (hbound.trans (mul_le_mul_of_nonneg_right hbudget_le (Nat.cast_nonneg _))).trans (mul_le_mul_of_nonneg_right
    (computedRefinementError_lt N source.length hN (by omega) hell).le (Nat.cast_nonneg _))

end Accuracy

end EditApproximation

end OAI
