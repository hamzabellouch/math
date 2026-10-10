import OAI.Combinatorics.EditApproximation.Refinement.PhysicalProgramNodeRegret
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalComparisonBand
import OAI.Combinatorics.EditApproximation.Refinement.StageComparisonPrediction
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalTreeGeneric
import OAI.Combinatorics.EditApproximation.Refinement.ComputedStageParameters

namespace OAI

/-! The actual selection program supplies the good-node premise of the
comparison-tree expected-regret telescope. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem computed_program_grid_lower (N P : ℕ) (hN : 0 < N)
    (hPeq : P = (integerParameters N).P) : 66 ≤ P := by
  rw [hPeq]
  exact (computed_stage_grid_bounds N hN).1

section Comparison

variable {α : Type*} [DecidableEq α] {M J R H : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hM : 0 < M) (hMeq : M = (integerParameters N).M)
  (U : PhysicalEntry M J target.length → ℕ) (P : ℕ) (hPeq : P = (integerParameters N).P)
  (A : ℚ) (hA : 1 ≤ A) (hAupper : A ≤ (integerParameters N).initialFactor)
  (hsize : source.length + target.length ≤ N)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (hHeq : H = inputHeight N) (hH : 4 ≤ H)
  (delta η κ : ℚ) (hdelta : 0 < delta) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
  (hηrange : (η : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * inputSmallLog N : ℚ) : ℝ) *
    (((2 : ℚ) ^ (-((40 * smallLogExponent N : ℕ) : ℤ))) : ℝ)) ≤ (κ : ℝ))
  (herror : 2 * (rationalParameters (inputSmallLog N)).gamma +
    512 * (128 * inputSmallLog N : ℚ) * inputSmallLog N *
      (2 : ℚ) ^ (-((40 * smallLogExponent N : ℕ) : ℤ)) ≤ κ * delta)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))
  (rootQ : TargetInterval target.length)

local notation "F" => inputSmallLog N
local notation "thetaExponent" => 40 * smallLogExponent N
local notation "tau" => RationalParameters.tau (rationalParameters F)
local notation "hP" => computed_program_grid_lower N P hN hPeq
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))
local notation "charges" => stageComparisonCharges source target hM U N P F A hP T rootQ
local notation "prediction" => stageComparisonPrediction source target hM U N P F A hP T rootQ
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H (F ^ 80) tau
local notation "choices" => physicalProgramDrawSelections source target U N P F A T thetaExponent H (F ^ 80) tau η κ
local notation "globalLaw" => physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H (F ^ 80) tau

include hell hM hMeq hA hAupper hsize hseed hT hHeq hH hdelta hη hκ hκhalf hηrange herror bernstein

/-- Non-bad, low-prediction comparison slots use their literal accepted
representative and whole-cell random coordinates in the global program. -/
theorem physicalProgram_comparison_node_regret (S : ℕ) (d : Fin J) (path : TreeLayer M d.val)
    (hnotbad : ¬ (comparisonActiveScale source target (frontier d.val path) <
      heightQuarterRoot N * (charges d path).1 ∨
      comparisonActiveScale source target (frontier d.val path) < heightQuarterRoot N * (charges d path).2))
    (hvelocity : |prediction d path| ≤ 1 - tau) :
    (∫ draw : Draw, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
      (choices draw) rootQ t d path) ∂globalLaw) ≤
      physicalProgramNodeCoefficient N F η κ delta S H * comparisonActiveCost source target (frontier d.val path) := by
  classical
  have hF : 1 ≤ F := Nat.one_le_two_pow
  have hell1764 : 1764 ≤ F := by
    have hlarge : 4096 ≤ (2 : ℕ) ^ 1000 := by
      have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 12 ≤ 1000)
      norm_num only [show (2 : ℕ) ^ 12 = 4096 by norm_num] at h
      exact h
    omega
  have hscale : 2 * (refinementFactor A F : ℝ) ≤ P := by
    rw [hPeq]
    exact computed_refinementFactor_spacing N hN A hA hAupper
  have hMP : 4 * (M : ℝ) / P ≤ 1 := by
    rw [hMeq, hPeq]
    exact (computed_stage_grid_bounds N hN).2.2
  generalize heq : frontier d.val path = state at hnotbad ⊢
  cases state with
  | none =>
    have hpoint (draw : Draw) (t : ℕ) := physicalComparisonTreeRegret_none source target hM U N P F A hP T delta
      (choices draw) rootQ t d path heq
    simp_rw [hpoint]
    simp only [sum_const_zero, integral_zero, comparisonActiveCost, mul_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · have hpoint (draw : Draw) (t : ℕ) := physicalComparisonTreeRegret_stopped source target hM U N P F A hP T delta
        (choices draw) rootQ t d path parent q heq hstop
      simp_rw [hpoint]
      simp only [sum_const_zero, integral_zero, comparisonActiveCost, ite_eq_left hstop, mul_zero, le_refl]
    · have hp := comparisonFrontier_active_source source target hM P hP rootQ d.val path parent q heq hstop
      let node : PhysicalNode M J := ⟨⟨d.val, by omega⟩, path⟩
      have hp' : parent = physicalSourceInterval source.length node := hp
      subst parent
      change ¬ comparisonStopped source target (physicalSourceInterval source.length node) q at hstop
      have hc : 0 < stateEditCost (physicalSource source node) target q := by
        change ¬ ((physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 ∨
            stateEditCost (physicalSource source node) target q = 0) at hstop
        omega
      have hleaf : ¬ (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 := fun h => hstop (Or.inl h)
      let b : ℕ := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc
      have hspec := comparisonChildren_spec source target hM P hP (physicalSourceInterval source.length node) q hc
      have hn : wideActionList M (physicalSourceInterval source.length node) r b P ≠ [] := by
        intro hnil
        have hmem := hspec.1
        change action ∈ wideActionList M (physicalSourceInterval source.length node) r b P at hmem
        rw [hnil] at hmem
        exact List.not_mem_nil hmem
      have hcharges := stageComparisonCharges_active source target hM U N P F A hP T rootQ d path q heq hstop hc hn
      have hprediction := stageComparisonPrediction_active source target hM U N P F A hP T rootQ d path q heq hstop hn
      have hratio : 0 < heightQuarterRoot N := by
        unfold heightQuarterRoot
        exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.two_pow_pos _)))
      have hKG := nonbad_charge_bounds _ _ _ _ hratio hnotbad
      change (charges d path).1 ≤ comparisonActiveScale source target
        (some (physicalSourceInterval source.length node, q)) / heightQuarterRoot N ∧
        (charges d path).2 ≤ comparisonActiveScale source target
        (some (physicalSourceInterval source.length node, q)) / heightQuarterRoot N at hKG
      have hscaleEq : comparisonActiveScale source target
          (some (physicalSourceInterval source.length node, q)) = (b : ℝ) := by
        simp only [comparisonActiveScale, ite_eq_right hstop]
        rfl
      rw [hscaleEq, hcharges] at hKG
      rw [hprediction] at hvelocity
      obtain ⟨member, hmember, hcenter, haction⟩ := physicalComparison_unskipped source target hM U N P A hN hell
        hMeq hPeq hsize hP hA hseed T hT node d.isLt q hc hscale hMP hn hvelocity hKG.1 hKG.2
      have hrep := stageRounded_representative_mem source target U N P F A hsize hP hF hA hseed node q hc
      obtain ⟨representative, hget⟩ := List.mem_iff_get.mp hrep
      have hget' : (stageRepresentatives source target U N P F A node).get representative = (b, member.center) := by
        simpa only [hcenter] using hget
      have hdyadic := cost_dyadicScale _ N hc (physical_state_cost_le source target N hsize (node, q))
      obtain ⟨scale, hgetScale⟩ := List.mem_iff_get.mp hdyadic.1
      have hcellmem := physicalProgramCells_complete source target U N P F A thetaExponent node b r hrep
      have hmember' : member ∈ physicalNodeCellBands source target U N P F A T node d.isLt b thetaExponent tau
          (targetCell ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * b) r) := by
        simpa only [computed_theta_dyadic, Nat.cast_mul, Nat.cast_ofNat, b, r] using hmember
      have hnonempty : physicalNodeCellBands source target U N P F A T node d.isLt b thetaExponent tau
          (targetCell ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * b) r) ≠ [] := by
        intro he
        rw [he] at hmember'
        exact List.not_mem_nil hmember'
      have hcellmem' : targetCell ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * ((dyadicScales N).get scale)) r ∈
          physicalProgramCells source target U N P F A thetaExponent node ((dyadicScales N).get scale) := by
        simpa only [hgetScale, Nat.cast_mul, Nat.cast_ofNat, b] using hcellmem
      obtain ⟨actualCellIndex, hgetActualCell⟩ := List.mem_iff_get.mp hcellmem'
      have htau : 0 < tau := by
        dsimp only [rationalParameters]
        exact div_pos zero_lt_one (pow_pos (Nat.cast_pos.2 (Nat.two_pow_pos _)) 4)
      have hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q := by
        exact_mod_cast hdyadic.2.1
      have hquery : physicalProgramOnlineGuard source target U N P F A node q (b, member.center) := by
        simpa only [hcenter] using physicalProgramOnlineGuard_comparison source target U N P F A
          hsize hP hF hA hseed node q hc
      have hbound := physicalProgram_global_node_regret (R := R) source target N hN hell1764 hM hMeq hPeq rfl
        (Nat.log 2 (stateEditCost (physicalSource source node) target q)) rfl rfl rfl hHeq hH
        U A hsize hP hF hA hseed T hT delta η κ hdelta hη hκ hκhalf
        (⟨node, d.isLt⟩ : PhysicalInternalNode M J) hleaf representative scale hgetScale
        (targetCell ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * b) r) actualCellIndex
        (by simpa only [hgetScale] using hgetActualCell) hnonempty member
        hmember' hget' q hb hquery action haction
        htau hηrange herror (bernstein b) S
      have hpoint (draw : Draw) (t : ℕ) :
          physicalComparisonTreeRegret source target hM U N P F A hP T delta (choices draw) rootQ t d path = _ :=
        physicalComparisonTreeRegret_active source target hM U N P F A hsize hP hF hA hseed
          T hT delta (choices draw) rootQ t node d.isLt q heq hstop
      simp_rw [hpoint]
      have hstop' : ¬ comparisonStopped source target (sourceIntervalAt M source.length d.val path) q := hstop
      simpa only [hcenter, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, comparisonActiveCost,
        ite_eq_right hstop', action, physicalSource, physicalSourceInterval, node] using hbound

end Comparison

end EditApproximation

end OAI
