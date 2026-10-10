import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.NumberTheory.Jacobsthal.Analysis.DensityComparison
import OAI.NumberTheory.Jacobsthal.Partitions.BandShiftTransport

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.StateMarginalBridge
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.RegenerationTails
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.MarginalDensityMeasures

theorem evenReal_map_lift : evenRealKernel.map oddLift = evenToOdd.comap evenLift evenLift_measurable := by
  ext s B hB
  rw [Kernel.map_apply _ oddLift_measurable]
  change (evenKernel (evenLift s)).map oddLift B = evenToOdd (evenLift s) B
  rw [evenKernel_map_lift]

theorem oddReal_map_lift : oddRealKernel.map evenLift = oddToEven.comap oddLift oddLift_measurable := by
  ext s B hB
  rw [Kernel.map_apply _ evenLift_measurable]
  change (oddKernel (oddLift s)).map evenLift B = oddToEven (oddLift s) B
  rw [oddKernel_map_lift]

theorem propagate_even (mu : Measure ℝ) :
    stateKernel ∘ₘ (mu.map evenLift).map Sum.inl = ((evenRealKernel ∘ₘ mu).map oddLift).map Sum.inr := by
  rw [comp_map_input _ _ _ measurable_inl]
  change evenBranch ∘ₘ mu.map evenLift = _
  rw [evenBranch, ← Measure.map_comp _ _ measurable_inr,
    comp_map_input _ _ _ evenLift_measurable, ← evenReal_map_lift,
    ← Measure.map_comp _ _ oddLift_measurable]

theorem propagate_odd (mu : Measure ℝ) :
    stateKernel ∘ₘ (mu.map oddLift).map Sum.inr = ((oddRealKernel ∘ₘ mu).map evenLift).map Sum.inl := by
  rw [comp_map_input _ _ _ measurable_inr]
  change oddBranch ∘ₘ mu.map oddLift = _
  rw [oddBranch, ← Measure.map_comp _ _ measurable_inl,
    comp_map_input _ _ _ oddLift_measurable, ← oddReal_map_lift,
    ← Measure.map_comp _ _ evenLift_measurable]

theorem state_even_first (s : EvenState) :
    stateKernel (Sum.inl s) = ((evenKernel s).map oddLift).map Sum.inr := by
  change evenBranch s = _
  rw [evenBranch, Kernel.map_apply _ measurable_inr, evenKernel_map_lift]

theorem state_odd_first (s : OddState) :
    stateKernel (Sum.inr s) = ((oddKernel s).map evenLift).map Sum.inl := by
  change oddBranch s = _
  rw [oddBranch, Kernel.map_apply _ measurable_inl, oddKernel_map_lift]

theorem state_even_two (s : EvenState) :
    (stateKernel ^ 2) (Sum.inl s) = ((initialTwoMeasure s).map evenLift).map Sum.inl := by
  rw [pow_two]
  change (stateKernel ∘ₖ stateKernel) (Sum.inl s) = _
  rw [Kernel.comp_apply, state_even_first]
  exact propagate_odd (evenKernel s)

theorem state_odd_two (s : OddState) :
    (stateKernel ^ 2) (Sum.inr s) = ((evenRealKernel ∘ₘ oddKernel s).map oddLift).map Sum.inr := by
  rw [pow_two]
  change (stateKernel ∘ₖ stateKernel) (Sum.inr s) = _
  rw [Kernel.comp_apply, state_odd_first]
  exact propagate_even (oddKernel s)

theorem state_reg_three :
    (stateKernel ^ 3) (Sum.inr regenerationState) = (regThreeMeasure.map evenLift).map Sum.inl := by
  have hp : stateKernel ^ 3 = stateKernel ∘ₖ (stateKernel ^ 2) := pow_succ' stateKernel 2
  rw [hp, Kernel.comp_apply, state_odd_two]
  exact propagate_odd (evenRealKernel ∘ₘ oddKernel regenerationState)

end Erdos970Dependency.StateMarginalBridge

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.InitialStateDomination
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures NumberTheoryLean.RegenerationTails
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.DensityComparison
open Erdos970Dependency.MarginalDensityMeasures Erdos970Dependency.StateMarginalBridge

theorem initial_state_measure_le (s : EvenState) (hs : 199 / 100 ≤ s.1) (hsup : s.1 ≤ 23 / 10) :
    (stateKernel ^ 2) (Sum.inl s) ≤ ENNReal.ofReal dominationConstant •
      (stateKernel ^ 3) (Sum.inr regenerationState) := by
  rw [state_even_two, state_reg_three]
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply measurable_inl hB,
    Measure.map_apply evenLift_measurable (measurable_inl hB),
    Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_inl hB,
    Measure.map_apply evenLift_measurable (measurable_inl hB)]
  have h := Measure.le_iff.mp (initial_real_measure_le s hs hsup)
    (evenLift ⁻¹' (Sum.inl ⁻¹' B)) (evenLift_measurable (measurable_inl hB))
  rw [Measure.smul_apply, smul_eq_mul] at h
  exact h

theorem initial_two_step_domination : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ s : EvenState, 199 / 100 ≤ s.1 → s.1 ≤ 23 / 10 →
      (stateKernel ^ 2) (Sum.inl s) ≤ C • (stateKernel ^ 3) (Sum.inr regenerationState) := by
  exact ⟨ENNReal.ofReal dominationConstant, ENNReal.ofReal_lt_top, initial_state_measure_le⟩

end Erdos970Dependency.InitialStateDomination

end

section

namespace NumberTheoryLean.InvariantInverseWeights

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open DerivativeWeights TransitionKernels FinitePathMeasures
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance

noncomputable def stateWeight : State → ℝ :=
  Sum.elim (fun s : EvenState => phiEven s.1) (fun s : OddState => phiOdd s.1)

theorem stateWeight_pos (s : State) : 0 < stateWeight s := by
  cases s with
  | inl s => exact phiEven_pos (by linarith [s.2])
  | inr s => exact phiOdd_pos s.1

theorem stateWeight_measurable : Measurable stateWeight :=
  (phiEven_measurable.comp measurable_subtype_coe).sumElim
    (phiOdd_continuous.measurable.comp measurable_subtype_coe)

noncomputable def inverseWeightCutoff (L : ℝ) : State → ℝ≥0∞ :=
  {s | stateRatio s < L}.indicator (fun s => (ENNReal.ofReal (stateWeight s))⁻¹)

theorem inverseWeightCutoff_measurable (L : ℝ) : Measurable (inverseWeightCutoff L) :=
  (ENNReal.measurable_ofReal.comp stateWeight_measurable).inv.indicator
    (measurableSet_lt stateRatio_measurable measurable_const)

theorem even_inverse_density_le (L t : ℝ) :
    ENNReal.ofReal (Erdos970Dependency.InvariantDensities.evenDensity t) * inverseWeightCutoff L (.inl (evenLift t)) ≤
      (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  by_cases ht : 2 ≤ t
  · have hl : (evenLift t).1 = t := max_eq_right (by linarith)
    have hw : stateWeight (.inl (evenLift t)) = phiEven t := by change phiEven (evenLift t).1 = _; rw [hl]
    have hr : stateRatio (.inl (evenLift t)) = t := hl
    rw [Erdos970Dependency.InvariantDensities.evenDensity, indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht)]
    unfold inverseWeightCutoff
    by_cases hL : t < L
    · rw [indicator_of_mem (show (.inl (evenLift t) : State) ∈ {s | stateRatio s < L} by simpa only [mem_ofPred_eq, hr] using hL), hw,
        ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (phiEven_pos (by linarith))).ne' ENNReal.ofReal_ne_top,
        indicator_of_mem (show t ∈ Icc (0 : ℝ) L from ⟨by linarith, hL.le⟩)]
    · rw [indicator_of_notMem (show (.inl (evenLift t) : State) ∉ {s | stateRatio s < L} by simpa only [mem_ofPred_eq, hr] using hL), mul_zero]
      exact zero_le
  · rw [Erdos970Dependency.InvariantDensities.evenDensity, indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht), ENNReal.ofReal_zero, zero_mul]
    exact zero_le

theorem odd_inverse_density_le (L t : ℝ) :
    ENNReal.ofReal (Erdos970Dependency.InvariantDensities.oddDensity t) * inverseWeightCutoff L (.inr (oddLift t)) ≤
      (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  by_cases ht : 1 ≤ t
  · have hl : (oddLift t).1 = t := max_eq_right (by linarith)
    have hw : stateWeight (.inr (oddLift t)) = phiOdd t := by change phiOdd (oddLift t).1 = _; rw [hl]
    have hr : stateRatio (.inr (oddLift t)) = t := hl
    have hf := oddFactor_bounds ht
    rw [Erdos970Dependency.InvariantDensities.oddDensity, indicator_of_mem (show t ∈ Ici (1 : ℝ) from ht), ENNReal.ofReal_mul hf.1]
    unfold inverseWeightCutoff
    by_cases hL : t < L
    · rw [indicator_of_mem (show (.inr (oddLift t) : State) ∈ {s | stateRatio s < L} by simpa only [mem_ofPred_eq, hr] using hL), hw,
        mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (phiOdd_pos t)).ne' ENNReal.ofReal_ne_top, mul_one,
        indicator_of_mem (show t ∈ Icc (0 : ℝ) L from ⟨by linarith, hL.le⟩)]
      exact (ENNReal.ofReal_le_ofReal hf.2).trans_eq ENNReal.ofReal_one
    · rw [indicator_of_notMem (show (.inr (oddLift t) : State) ∉ {s | stateRatio s < L} by simpa only [mem_ofPred_eq, hr] using hL), mul_zero]
      exact zero_le
  · rw [Erdos970Dependency.InvariantDensities.oddDensity, indicator_of_notMem (show t ∉ Ici (1 : ℝ) from ht), ENNReal.ofReal_zero, zero_mul]
    exact zero_le

theorem inverseWeightCutoff_mass_le {L : ℝ} (hL : 0 ≤ L) :
    (∫⁻ s : State, inverseWeightCutoff L s ∂stateMeasure) ≤ ENNReal.ofReal (2 * L) := by
  have hQ := inverseWeightCutoff_measurable L
  rw [stateMeasure, lintegral_add_measure,
    lintegral_map hQ measurable_inl, lintegral_map hQ measurable_inr,
    evenStateMeasure, oddStateMeasure,
    lintegral_map (f := fun s : EvenState => inverseWeightCutoff L (.inl s)) (hQ.comp measurable_inl) evenLift_measurable,
    lintegral_map (f := fun s : OddState => inverseWeightCutoff L (.inr s)) (hQ.comp measurable_inr) oddLift_measurable,
    evenMeasure, oddMeasure,
    lintegral_withDensity_eq_lintegral_mul volume
      (f := fun t : ℝ => ENNReal.ofReal (Erdos970Dependency.InvariantDensities.evenDensity t))
      (g := fun t : ℝ => inverseWeightCutoff L (.inl (evenLift t)))
      (ENNReal.measurable_ofReal.comp Erdos970Dependency.InvariantDensities.evenDensity_measurable)
      (hQ.comp (measurable_inl.comp evenLift_measurable)),
    lintegral_withDensity_eq_lintegral_mul volume
      (f := fun t : ℝ => ENNReal.ofReal (Erdos970Dependency.InvariantDensities.oddDensity t))
      (g := fun t : ℝ => inverseWeightCutoff L (.inr (oddLift t)))
      (ENNReal.measurable_ofReal.comp Erdos970Dependency.InvariantDensities.oddDensity_measurable)
      (hQ.comp (measurable_inr.comp oddLift_measurable))]
  calc
    _ ≤ (∫⁻ t : ℝ, (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t) +
        (∫⁻ t : ℝ, (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t) :=
      add_le_add (lintegral_mono (even_inverse_density_le L)) (lintegral_mono (odd_inverse_density_le L))
    _ = ENNReal.ofReal L + ENNReal.ofReal L := by
      have hI : (∫⁻ t : ℝ, (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t) = ENNReal.ofReal L := by
        change (∫⁻ t : ℝ, (Icc (0 : ℝ) L).indicator 1 t) = _
        rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc, sub_zero]
      rw [hI]
    _ = _ := by rw [← ENNReal.ofReal_add hL hL]; congr 1; ring

end NumberTheoryLean.InvariantInverseWeights

end

section

namespace NumberTheoryLean.FirstStepInverseWeight

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open DerivativeWeights WeightFutureIntegrals TransitionKernels FinitePathMeasures
open KernelDensityBridge InvariantInverseWeights

noncomputable def firstDensityConstant : ℝ := 3 / phiEven (23 / 10)

theorem firstDensityConstant_pos : 0 < firstDensityConstant := div_pos (by norm_num) (phiEven_pos (by norm_num))

theorem W_le_three {t : ℝ} (ht : (49 / 50 : ℝ) ≤ t) : W t ≤ 3 := by
  have ht0 : 0 < t := by linarith
  rw [W]
  apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
  nlinarith [sq_nonneg (t - 49 / 50)]

theorem first_odd_density_bound (s : EvenState) (hs : s.1 ≤ 23 / 10) (t : ℝ) :
    evenDensity s t ≤ firstDensityConstant * (Ici (49 / 50 : ℝ)).indicator phiOdd t := by
  have hφ := phiEven_pos (s := s.1) (by linarith [s.2])
  have hm := phiEven_pos (s := (23 / 10 : ℝ)) (by norm_num)
  have hmin : phiEven (23 / 10) ≤ phiEven s.1 :=
    phiEven_strictAntiOn.antitoneOn (by change 1 < s.1; linarith [s.2]) (by norm_num) hs
  unfold evenDensity tailDensity
  by_cases ht : s.1 - 1 ≤ t
  · have ht98 : (49 / 50 : ℝ) ≤ t := by linarith [s.2]
    rw [indicator_of_mem (show t ∈ Ici (s.1 - 1) from ht),
      indicator_of_mem (show t ∈ Ici (49 / 50 : ℝ) from ht98)]
    apply (div_le_iff₀ hφ).mpr
    calc
      W t * phiOdd t ≤ 3 * phiOdd t := mul_le_mul_of_nonneg_right (W_le_three ht98) (phiOdd_pos t).le
      _ = (firstDensityConstant * phiOdd t) * phiEven (23 / 10) := by
        dsimp [firstDensityConstant]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmin (mul_nonneg firstDensityConstant_pos.le (phiOdd_pos t).le)
  · rw [indicator_of_notMem (show t ∉ Ici (s.1 - 1) from ht)]
    by_cases h98 : (49 / 50 : ℝ) ≤ t
    · rw [indicator_of_mem (show t ∈ Ici (49 / 50 : ℝ) from h98)]
      exact mul_nonneg firstDensityConstant_pos.le (phiOdd_pos t).le
    · rw [indicator_of_notMem (show t ∉ Ici (49 / 50 : ℝ) from h98), mul_zero]

theorem first_odd_inverse_mass (s : EvenState) (hs : s.1 ≤ 23 / 10) {L : ℝ} (_hL : 0 ≤ L) :
    (∫⁻ t : State, inverseWeightCutoff L t ∂stateKernel (.inl s)) ≤
      ENNReal.ofReal (firstDensityConstant * L) := by
  classical
  let G : ℝ → ℝ≥0∞ := (Iio L).indicator (fun t => (ENNReal.ofReal (phiOdd t))⁻¹)
  have hG : Measurable G := (ENNReal.measurable_ofReal.comp phiOdd_continuous.measurable).inv.indicator measurableSet_Iio
  have hQ := inverseWeightCutoff_measurable L
  change (∫⁻ t : State, inverseWeightCutoff L t ∂evenBranch s) ≤ _
  rw [evenBranch, Kernel.map_apply _ measurable_inr, lintegral_map hQ measurable_inr]
  change (∫⁻ t : OddState, G t.1 ∂evenToOdd s) ≤ _
  rw [evenToOdd_lintegral_ratio s hG, evenKernel_lintegral_density s hG]
  change (∫⁻ t : ℝ, ENNReal.ofReal (evenDensity s t) * G t) ≤ _
  have hb : ∀ t : ℝ, ENNReal.ofReal (evenDensity s t) * G t ≤
      ENNReal.ofReal firstDensityConstant * (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t := by
    intro t
    have hd := first_odd_density_bound s hs t
    by_cases h98 : (49 / 50 : ℝ) ≤ t
    · rw [indicator_of_mem (show t ∈ Ici (49 / 50 : ℝ) from h98)] at hd
      by_cases htL : t < L
      · rw [show G t = (ENNReal.ofReal (phiOdd t))⁻¹ by
          exact indicator_of_mem (show t ∈ Iio L from htL) _,
          indicator_of_mem (show t ∈ Icc (0 : ℝ) L from ⟨by linarith, htL.le⟩), mul_one]
        calc
          _ ≤ ENNReal.ofReal (firstDensityConstant * phiOdd t) * (ENNReal.ofReal (phiOdd t))⁻¹ :=
            mul_le_mul (ENNReal.ofReal_le_ofReal hd) le_rfl zero_le zero_le
          _ = _ := by
            rw [ENNReal.ofReal_mul firstDensityConstant_pos.le, mul_assoc,
              ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (phiOdd_pos t)).ne' ENNReal.ofReal_ne_top, mul_one]
      · rw [show G t = 0 from indicator_of_notMem (show t ∉ Iio L from htL) _, mul_zero]
        exact zero_le
    · rw [indicator_of_notMem (show t ∉ Ici (49 / 50 : ℝ) from h98), mul_zero] at hd
      rw [ENNReal.ofReal_eq_zero.mpr hd, zero_mul]
      exact zero_le
  calc
    _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal firstDensityConstant * (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t := lintegral_mono hb
    _ = ENNReal.ofReal firstDensityConstant * ENNReal.ofReal L := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      change (∫⁻ t : ℝ, (Icc (0 : ℝ) L).indicator 1 t) = _
      rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc, sub_zero]
    _ = _ := (ENNReal.ofReal_mul firstDensityConstant_pos.le).symm

end NumberTheoryLean.FirstStepInverseWeight

end

section

namespace NumberTheoryLean.RegeneratingInverseBands

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures PairedCostGrouping RegenerationTails OccupationDecomposition
open RegenerationBandBounds InvariantInverseWeights FirstStepInverseWeight

noncomputable def gapValue (v : ℝ) (z : CostState) : ℝ := Real.exp (v - z.2)

noncomputable def inverseArrivalBand (v R ell : ℝ) : CostState → ℝ≥0∞ :=
  {z | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧
    stateRatio z.1 < gapValue v z / ell}.indicator
    (fun z => (ENNReal.ofReal (stateWeight z.1))⁻¹)

theorem inverseArrivalBand_measurable (v R ell : ℝ) : Measurable (inverseArrivalBand v R ell) := by
  have hg : Measurable (gapValue v) := Real.measurable_exp.comp (measurable_const.sub measurable_snd)
  exact ((ENNReal.measurable_ofReal.comp (stateWeight_measurable.comp measurable_fst)).inv).indicator
    ((measurableSet_le measurable_const hg).inter
      ((measurableSet_le hg measurable_const).inter
        (measurableSet_lt (stateRatio_measurable.comp measurable_fst) (hg.div_const ell))))

theorem stateBandReward_le (Q : State → ℝ≥0∞) (v h : ℝ) (z : CostState) :
    stateBandReward Q v h z ≤ Q z.1 := by
  classical
  unfold stateBandReward
  by_cases hz : z.2 ∈ Icc v (v + h)
  · rw [indicator_of_mem (show z ∈ Prod.snd ⁻¹' Icc v (v + h) from hz)]
  · rw [indicator_of_notMem (show z ∉ Prod.snd ⁻¹' Icc v (v + h) from hz)]
    exact zero_le

theorem inverseArrivalBand_le_costBand (v : ℝ) {R ell : ℝ} (hR : 0 < R) (hell : 1 ≤ ell)
    (z : CostState) :
    inverseArrivalBand v R ell z ≤
      stateBandReward (inverseWeightCutoff (Real.exp 1 * R)) (v - Real.log R - 1) 1 z := by
  classical
  by_cases hz : R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell
  · have hg : 0 < gapValue v z := Real.exp_pos _
    have hl : Real.log R ≤ v - z.2 := by
      have h := Real.log_le_log hR hz.1
      rwa [gapValue, Real.log_exp] at h
    have hu : v - z.2 ≤ 1 + Real.log R := by
      have h := Real.log_le_log hg hz.2.1
      rwa [gapValue, Real.log_exp, Real.log_mul (Real.exp_pos 1).ne' hR.ne', Real.log_exp] at h
    have ht : stateRatio z.1 < Real.exp 1 * R :=
      lt_of_lt_of_le hz.2.2 (le_trans (div_le_self hg.le hell) hz.2.1)
    have hband : z.2 ∈ Icc (v - Real.log R - 1) (v - Real.log R - 1 + 1) := by
      constructor <;> linarith
    unfold inverseArrivalBand stateBandReward inverseWeightCutoff
    rw [indicator_of_mem (show z ∈ {z | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell} from hz),
      indicator_of_mem (show z ∈ Prod.snd ⁻¹' Icc (v - Real.log R - 1) (v - Real.log R - 1 + 1) from hband),
      indicator_of_mem (show z.1 ∈ {s | stateRatio s < Real.exp 1 * R} from ht)]
  · unfold inverseArrivalBand
    rw [indicator_of_notMem (show z ∉ {z | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell} from hz)]
    exact zero_le

theorem regeneration_inverse_cutoff_band (h : ℝ) : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ L : ℝ, 0 ≤ L → ∀ v : ℝ,
      (∫⁻ z, stateBandReward (inverseWeightCutoff L) v h z ∂fullOccupation (embedOdd (regenerationState, 0))) ≤
        C * ENNReal.ofReal L := by
  obtain ⟨C, hC, hb⟩ := regeneration_uniform_band h
  refine ⟨C * 2, ENNReal.mul_lt_top hC (by norm_num), ?_⟩
  intro L hL v
  calc
    _ ≤ C * ∫⁻ s, inverseWeightCutoff L s ∂Erdos970Dependency.StateKernelInvariance.stateMeasure :=
      hb _ (inverseWeightCutoff_measurable L) v
    _ ≤ C * ENNReal.ofReal (2 * L) := mul_le_mul le_rfl (inverseWeightCutoff_mass_le hL) zero_le zero_le
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]

theorem regeneration_inverse_arrival_band : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ v R ell : ℝ, 0 < R → 1 ≤ ell →
      (∫⁻ z, inverseArrivalBand v R ell z ∂fullOccupation (embedOdd (regenerationState, 0))) ≤ C * ENNReal.ofReal R := by
  obtain ⟨C, hC, hb⟩ := regeneration_inverse_cutoff_band 1
  refine ⟨C * ENNReal.ofReal (Real.exp 1), ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top, ?_⟩
  intro v R ell hR hell
  calc
    _ ≤ ∫⁻ z, stateBandReward (inverseWeightCutoff (Real.exp 1 * R)) (v - Real.log R - 1) 1 z
        ∂fullOccupation (embedOdd (regenerationState, 0)) := lintegral_mono (inverseArrivalBand_le_costBand v hR hell)
    _ ≤ C * ENNReal.ofReal (Real.exp 1 * R) := hb _ (by positivity) _
    _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_pos 1).le, mul_assoc]

theorem first_odd_inverse_arrival_band (s : TransitionKernels.EvenState) (hs : s.1 ≤ 23 / 10)
    (v : ℝ) {R ell : ℝ} (hR : 0 < R) (hell : 1 ≤ ell) :
    (∫⁻ z, inverseArrivalBand v R ell z ∂costKernel (.inl s, 0)) ≤
      ENNReal.ofReal (firstDensityConstant * Real.exp 1) * ENNReal.ofReal R := by
  have hQ := inverseWeightCutoff_measurable (Real.exp 1 * R)
  calc
    _ ≤ ∫⁻ z, inverseWeightCutoff (Real.exp 1 * R) z.1 ∂costKernel (.inl s, 0) :=
      lintegral_mono (fun z => le_trans (inverseArrivalBand_le_costBand v hR hell z) (stateBandReward_le _ _ _ z))
    _ = ∫⁻ t : State, inverseWeightCutoff (Real.exp 1 * R) t ∂stateKernel (.inl s) := by
      rw [← Erdos970Dependency.ActualCycleOccupation.costKernel_map_state (.inl s, 0), lintegral_map hQ measurable_fst]
    _ ≤ ENNReal.ofReal (firstDensityConstant * (Real.exp 1 * R)) := first_odd_inverse_mass s hs (by positivity)
    _ = _ := by rw [← ENNReal.ofReal_mul (mul_pos firstDensityConstant_pos (Real.exp_pos 1)).le]; congr 1; ring

end NumberTheoryLean.RegeneratingInverseBands

end

section

namespace NumberTheoryLean.EvenBandBounds

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures RegenerationTails PairedCostGrouping
open OccupationDecomposition InitialOccupation CostPrefixTransport
open BandShiftTransport RegenerationBandBounds RegeneratingInverseBands
open Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.InitialStateDomination

theorem even_uniform_band (h : ℝ) : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ Q : State → ℝ≥0∞, Measurable Q → ∀ v : ℝ, ∀ s : EvenState,
      (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 →
      (∫⁻ z, stateBandReward Q v h z ∂prefixOccupation 2 (.inl s, 0)) ≤
        C * ∫⁻ t : State, Q t ∂stateMeasure := by
  obtain ⟨D, hD, hdom⟩ := initial_two_step_domination
  obtain ⟨B, hB, hb⟩ := regeneration_uniform_band (h + 5 * Real.log 3)
  refine ⟨D * B, ENNReal.mul_lt_top hD hB, ?_⟩
  intro Q hQ v s hsL hsU
  have ht := prefix_band_domination hQ 2 3 (.inl s) (.inr regenerationState) (hdom s hsL hsU) v h
  norm_num only [Nat.cast_ofNat] at ht
  rw [show h + 2 * Real.log 3 + 3 * Real.log 3 = h + 5 * Real.log 3 by ring] at ht
  calc
    _ ≤ D * ∫⁻ z, stateBandReward Q (v - 2 * Real.log 3) (h + 5 * Real.log 3) z
        ∂prefixOccupation 3 (.inr regenerationState, 0) := ht
    _ ≤ D * ∫⁻ z, stateBandReward Q (v - 2 * Real.log 3) (h + 5 * Real.log 3) z
        ∂fullOccupation (.inr regenerationState, 0) :=
      mul_le_mul le_rfl (lintegral_mono' (prefixOccupation_le_full 3 (by norm_num) (.inr regenerationState, 0)) le_rfl) zero_le zero_le
    _ ≤ D * (B * ∫⁻ t : State, Q t ∂stateMeasure) := mul_le_mul le_rfl (hb Q hQ _) zero_le zero_le
    _ = _ := (mul_assoc _ _ _).symm

theorem prefixOccupation_two : prefixOccupation 2 = fullOccupation ∘ₖ costKernel := by
  rw [prefixOccupation, pow_two]
  change inclusiveOccupation ∘ₖ (costKernel ∘ₖ costKernel) = _
  rw [← Kernel.comp_assoc, inclusive_comp_step]

theorem fullOccupation_first_and_later : fullOccupation = costKernel + prefixOccupation 2 := by
  rw [prefixOccupation_two]
  exact fullOccupation_unfold

end NumberTheoryLean.EvenBandBounds

end

section

namespace NumberTheoryLean.WeightedGapTail

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures PairedCostGrouping RegenerationTails OccupationDecomposition
open InvariantInverseWeights RegeneratingInverseBands

noncomputable def tailSeries (c : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) ^ 3 * Real.exp (-c * ((n : ℝ) + 1))

theorem tailSeries_nonneg (c : ℝ) (n : ℕ) : 0 ≤ tailSeries c n := by unfold tailSeries; positivity

theorem tailSeries_summable {c : ℝ} (hc : 0 < c) : Summable (tailSeries c) := by
  have h := (summable_nat_add_iff 2).mpr (Real.summable_pow_mul_exp_neg_nat_mul 3 hc)
  have h' := h.mul_left (Real.exp c)
  convert! h' using 1
  funext n
  simp only [tailSeries, Nat.cast_add, Nat.cast_ofNat]
  rw [mul_comm (Real.exp c), mul_assoc, ← Real.exp_add]
  congr 2
  ring

noncomputable def tailBudget (C : ℝ≥0∞) (c : ℝ) (N : ℕ) : ℝ≥0∞ :=
  C * ∑' k : ℕ, ENNReal.ofReal (tailSeries c (k + N))

theorem tailBudget_tendsto_zero {C : ℝ≥0∞} (hC : C ≠ ∞) {c : ℝ} (hc : 0 < c) :
    Tendsto (tailBudget C c) atTop (𝓝 0) := by
  have hs : (∑' n : ℕ, ENNReal.ofReal (tailSeries c n)) ≠ ∞ := (tailSeries_summable hc).tsum_ofReal_lt_top.ne
  have h := ENNReal.tendsto_sum_nat_add (fun n => ENNReal.ofReal (tailSeries c n)) hs
  change Tendsto (fun N : ℕ => C * ∑' k : ℕ, ENNReal.ofReal (tailSeries c (k + N))) atTop (𝓝 0)
  simpa only [mul_zero] using (ENNReal.Tendsto.const_mul (a := C) h (Or.inr hC))

noncomputable def tailReward (c v ell : ℝ) (N : ℕ) : CostState → ℝ≥0∞ :=
  {z | (N : ℝ) + 1 ≤ gapValue v z ∧ stateRatio z.1 < gapValue v z / ell}.indicator
    (fun z => ENNReal.ofReal ((gapValue v z) ^ 2 * Real.exp (-c * gapValue v z)) *
      (ENNReal.ofReal (stateWeight z.1))⁻¹)

theorem tailReward_measurable (c v ell : ℝ) (N : ℕ) : Measurable (tailReward c v ell N) := by
  have hg : Measurable (gapValue v) := Real.measurable_exp.comp (measurable_const.sub measurable_snd)
  exact ((ENNReal.measurable_ofReal.comp ((hg.pow_const 2).mul (Real.measurable_exp.comp (measurable_const.mul hg)))).mul
    (ENNReal.measurable_ofReal.comp (stateWeight_measurable.comp measurable_fst)).inv).indicator
      ((measurableSet_le measurable_const hg).inter
        (measurableSet_lt (stateRatio_measurable.comp measurable_fst) (hg.div_const ell)))

noncomputable def binCoefficient (c : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) ^ 2 * Real.exp (-c * ((n : ℝ) + 1))

theorem tailReward_le_band_sum {c : ℝ} (hc : 0 < c) (v ell : ℝ) (N : ℕ) (z : CostState) :
    tailReward c v ell N z ≤ ∑' k : ℕ,
      ENNReal.ofReal (binCoefficient c (k + N)) * inverseArrivalBand v ((k + N : ℕ) + 1) ell z := by
  classical
  by_cases hz : (N : ℝ) + 1 ≤ gapValue v z ∧ stateRatio z.1 < gapValue v z / ell
  · let r := gapValue v z
    have hr : 0 < r := Real.exp_pos _
    have hn : N + 1 ≤ ⌊r⌋₊ := (Nat.le_floor_iff hr.le).mpr (by exact_mod_cast hz.1)
    let k := ⌊r⌋₊ - (N + 1)
    have hk : k + N + 1 = ⌊r⌋₊ := by dsimp [k]; omega
    have hkR : ((k + N : ℕ) : ℝ) + 1 = (⌊r⌋₊ : ℝ) := by exact_mod_cast hk
    let R : ℝ := ((k + N : ℕ) : ℝ) + 1
    have hR1 : 1 ≤ R := by dsimp [R]; have hh := Nat.cast_nonneg' (α := ℝ) (k + N); linarith
    have hlow : R ≤ r := by rw [show R = (⌊r⌋₊ : ℝ) from hkR]; exact Nat.floor_le hr.le
    have hhigh : r < R + 1 := by rw [show R = (⌊r⌋₊ : ℝ) from hkR]; exact Nat.lt_floor_add_one r
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hupper : r ≤ Real.exp 1 * R := by nlinarith [mul_le_mul_of_nonneg_right he (by linarith : 0 ≤ R)]
    have hsq : r ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
    have hexp : Real.exp (-c * r) ≤ Real.exp (-c * R) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlow (by linarith))
    have hweight : r ^ 2 * Real.exp (-c * r) ≤ (R + 1) ^ 2 * Real.exp (-c * R) :=
      mul_le_mul hsq hexp (Real.exp_pos _).le (sq_nonneg _)
    have hA : R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell :=
      ⟨hlow, hupper, hz.2⟩
    calc
      _ = ENNReal.ofReal (r ^ 2 * Real.exp (-c * r)) * (ENNReal.ofReal (stateWeight z.1))⁻¹ :=
        by rw [tailReward, indicator_of_mem (show z ∈ {z : CostState | (N : ℝ) + 1 ≤ gapValue v z ∧ stateRatio z.1 < gapValue v z / ell} from hz)]
      _ ≤ ENNReal.ofReal ((R + 1) ^ 2 * Real.exp (-c * R)) * (ENNReal.ofReal (stateWeight z.1))⁻¹ :=
        mul_le_mul (ENNReal.ofReal_le_ofReal hweight) le_rfl zero_le zero_le
      _ = ENNReal.ofReal (binCoefficient c (k + N)) * inverseArrivalBand v ((k + N : ℕ) + 1) ell z := by
        rw [inverseArrivalBand, indicator_of_mem (show z ∈ {z : CostState | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell} from hA)]
        have hcoef : (R + 1) ^ 2 * Real.exp (-c * R) = binCoefficient c (k + N) := by
          dsimp [R, binCoefficient]
          ring
        rw [hcoef]
      _ ≤ _ := by
        simpa only [Nat.cast_add,Nat.cast_one] using
          (ENNReal.le_tsum (f := fun k : ℕ => ENNReal.ofReal (binCoefficient c (k+N)) *
            inverseArrivalBand v ((k+N : ℕ)+1) ell z) k)
  · rw [tailReward, indicator_of_notMem (show z ∉ {z : CostState | (N : ℝ) + 1 ≤ gapValue v z ∧ stateRatio z.1 < gapValue v z / ell} from hz)]
    exact zero_le

theorem weighted_tail_of_inverse_bands (μ : Measure CostState) (v ell : ℝ) {C : ℝ≥0∞}
    (hband : ∀ R : ℝ, 0 < R → (∫⁻ z, inverseArrivalBand v R ell z ∂μ) ≤ C * ENNReal.ofReal (R + 1))
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (∫⁻ z, tailReward c v ell N z ∂μ) ≤ tailBudget C c N := by
  calc
    _ ≤ ∫⁻ z, ∑' k : ℕ, ENNReal.ofReal (binCoefficient c (k + N)) *
        inverseArrivalBand v ((k + N : ℕ) + 1) ell z ∂μ := lintegral_mono (tailReward_le_band_sum hc v ell N)
    _ = ∑' k : ℕ, ENNReal.ofReal (binCoefficient c (k + N)) *
        (∫⁻ z, inverseArrivalBand v ((k + N : ℕ) + 1) ell z ∂μ) := by
      rw [lintegral_tsum (f := fun (k : ℕ) (z : CostState) => ENNReal.ofReal (binCoefficient c (k + N)) * inverseArrivalBand v (((k + N : ℕ) : ℝ) + 1) ell z) (fun k => (measurable_const.mul (inverseArrivalBand_measurable _ _ _)).aemeasurable)]
      apply tsum_congr
      intro k
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (binCoefficient c (k + N)) *
        (C * ENNReal.ofReal (((k + N : ℕ) : ℝ) + 1 + 1)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      exact mul_le_mul le_rfl (hband _ (by positivity)) zero_le zero_le
    _ = tailBudget C c N := by
      rw [tailBudget, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro k
      have hA : 0 ≤ binCoefficient c (k + N) := by unfold binCoefficient; positivity
      rw [mul_left_comm, ← ENNReal.ofReal_mul hA]
      congr 2
      dsimp [binCoefficient, tailSeries]
      ring

theorem regeneration_weighted_tail {c : ℝ} (hc : 0 < c) :
    ∃ b : ℕ → ℝ≥0∞, Tendsto b atTop (𝓝 0) ∧ ∀ N : ℕ, ∀ v ell : ℝ, 1 ≤ ell →
      (∫⁻ z, tailReward c v ell N z ∂fullOccupation (embedOdd (regenerationState, 0))) ≤ b N := by
  obtain ⟨C, hC, hb⟩ := regeneration_inverse_arrival_band
  refine ⟨tailBudget C c, tailBudget_tendsto_zero hC.ne hc, ?_⟩
  intro N v ell hell
  apply weighted_tail_of_inverse_bands _ v ell _ hc N
  intro R hR
  exact le_trans (hb v R ell hR hell)
    (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (by linarith : R ≤ R + 1)) zero_le zero_le)

end NumberTheoryLean.WeightedGapTail

end

section

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace ErdosHighRatioBandTail
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.RegenerationBandBounds NumberTheoryLean.BandShiftTransport
open NumberTheoryLean.CostPrefixTransport NumberTheoryLean.EvenBandBounds
open Erdos970Dependency.StateKernelInvariance

def highStates (T : ℝ) : Set State := {s | T ≤ stateRatio s}

noncomputable def highReward (T : ℝ) : State → ℝ≥0∞ :=
  (highStates T).indicator (fun _ => 1)

def highBand (T v h : ℝ) : Set CostState :=
  {z | T ≤ stateRatio z.1 ∧ z.2 ∈ Icc v (v+h)}

theorem highStates_measurable (T : ℝ) : MeasurableSet (highStates T) :=
  measurableSet_le measurable_const stateRatio_measurable

theorem highReward_measurable (T : ℝ) : Measurable (highReward T) :=
  measurable_const.indicator (highStates_measurable T)

theorem highBand_measurable (T v h : ℝ) : MeasurableSet (highBand T v h) :=
  (measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst)).inter
    (measurable_snd measurableSet_Icc)

theorem highReward_integral (μ : Measure State) (T : ℝ) :
    (∫⁻ s, highReward T s ∂μ) = μ (highStates T) := by
  rw [highReward, lintegral_indicator (highStates_measurable T)]
  simp

theorem highBand_integral (μ : Measure CostState) (T v h : ℝ) :
    (∫⁻ z, stateBandReward (highReward T) v h z ∂μ) = μ (highBand T v h) := by
  have he : stateBandReward (highReward T) v h =
      (highBand T v h).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext z
    by_cases ht : T ≤ stateRatio z.1 <;> by_cases hc : z.2 ∈ Icc v (v+h) <;>
      simp_all [stateBandReward, highReward, highStates, highBand, Set.indicator_apply]
  rw [he, lintegral_indicator (highBand_measurable T v h)]
  simp

theorem stateMeasure_tail_tendsto :
    Tendsto (fun T : ℝ => stateMeasure (highStates T)) atTop (𝓝 0) := by
  have hm : Antitone highStates := by
    intro T U hTU s hs
    exact hTU.trans hs
  have he : (⋂ T : ℝ, highStates T) = ∅ := by
    ext s
    simp only [mem_iInter, highStates, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro hs
    have h := hs (stateRatio s+1)
    linarith
  have ht := tendsto_measure_iInter_atTop
    (fun T => (highStates_measurable T).nullMeasurableSet (μ := stateMeasure)) hm
    (show ∃ T : ℝ, stateMeasure (highStates T) ≠ ∞ from ⟨0, measure_ne_top _ _⟩)
  simpa only [he, measure_empty, Function.comp_def] using ht

theorem later_band_tail_bound (h : ℝ) : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ T v : ℝ, ∀ s : EvenState, 199/100 ≤ s.1 → s.1 ≤ 23/10 →
      prefixOccupation 2 (.inl s,0) (highBand T v h) ≤ C*stateMeasure (highStates T) := by
  obtain ⟨C,hC,hb⟩ := even_uniform_band h
  refine ⟨C,hC,?_⟩
  intro T v s hsL hsU
  have ht := hb (highReward T) (highReward_measurable T) v s hsL hsU
  simpa only [highBand_integral, highReward_integral] using ht

end ErdosHighRatioBandTail

end

section

namespace NumberTheoryLean.EvenInverseBands

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open DerivativeWeights TransitionKernels FinitePathMeasures OccupationDecomposition
open CostPrefixTransport RegenerationBandBounds InvariantInverseWeights
open RegeneratingInverseBands FirstStepInverseWeight EvenBandBounds WeightedGapTail

theorem even_inverse_arrival_from_two : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ s : EvenState, (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 →
    ∀ v R ell : ℝ, 0 < R → 1 ≤ ell →
      (∫⁻ z, inverseArrivalBand v R ell z ∂prefixOccupation 2 (.inl s, 0)) ≤ C * ENNReal.ofReal R := by
  obtain ⟨B, hB, hb⟩ := even_uniform_band 1
  refine ⟨B * ENNReal.ofReal (2 * Real.exp 1), ENNReal.mul_lt_top hB ENNReal.ofReal_lt_top, ?_⟩
  intro s hsL hsU v R ell hR hell
  calc
    _ ≤ ∫⁻ z, stateBandReward (inverseWeightCutoff (Real.exp 1 * R)) (v - Real.log R - 1) 1 z
        ∂prefixOccupation 2 (.inl s, 0) := lintegral_mono (inverseArrivalBand_le_costBand v hR hell)
    _ ≤ B * ∫⁻ t : State, inverseWeightCutoff (Real.exp 1 * R) t
        ∂Erdos970Dependency.StateKernelInvariance.stateMeasure :=
      hb _ (inverseWeightCutoff_measurable _) _ s hsL hsU
    _ ≤ B * ENNReal.ofReal (2 * (Real.exp 1 * R)) :=
      mul_le_mul le_rfl (inverseWeightCutoff_mass_le (by positivity)) zero_le zero_le
    _ = _ := by
      rw [show 2 * (Real.exp 1 * R) = (2 * Real.exp 1) * R by ring,
        ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.exp 1), mul_assoc]

theorem even_future_inverse_arrival_band : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ s : EvenState, (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 →
    ∀ v R ell : ℝ, 0 < R → 1 ≤ ell →
      (∫⁻ z, inverseArrivalBand v R ell z ∂fullOccupation (.inl s, 0)) ≤ C * ENNReal.ofReal R := by
  obtain ⟨B, hB, hb⟩ := even_inverse_arrival_from_two
  refine ⟨ENNReal.ofReal (firstDensityConstant * Real.exp 1) + B,
    ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hB⟩, ?_⟩
  intro s hsL hsU v R ell hR hell
  rw [fullOccupation_first_and_later, _root_.add_apply, lintegral_add_measure]
  calc
    _ ≤ ENNReal.ofReal (firstDensityConstant * Real.exp 1) * ENNReal.ofReal R + B * ENNReal.ofReal R :=
      add_le_add (first_odd_inverse_arrival_band s hsU v hR hell) (hb s hsL hsU v R ell hR hell)
    _ = _ := (add_mul _ _ _).symm

theorem inverseArrivalBand_le_weight (v R ell : ℝ) (z : CostState) :
    inverseArrivalBand v R ell z ≤ (ENNReal.ofReal (stateWeight z.1))⁻¹ := by
  classical
  unfold inverseArrivalBand
  by_cases hz : R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell
  · rw [indicator_of_mem (show z ∈ {z | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell} from hz)]
  · rw [indicator_of_notMem (show z ∉ {z | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell} from hz)]
    exact zero_le

theorem starting_inverse_weight_le (s : EvenState) (hs : s.1 ≤ 23 / 10) :
    (ENNReal.ofReal (stateWeight (.inl s)))⁻¹ ≤ (ENNReal.ofReal (phiEven (23 / 10)))⁻¹ := by
  apply ENNReal.inv_le_inv.mpr
  apply ENNReal.ofReal_le_ofReal
  exact phiEven_strictAntiOn.antitoneOn (by change 1 < s.1; linarith [s.2]) (by norm_num) hs

theorem source_inverse_phi_band : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ s : EvenState, (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 →
    ∀ v R ell : ℝ, 0 < R → 1 ≤ ell →
      (∫⁻ z, inverseArrivalBand v R ell z ∂inclusiveOccupation (.inl s, 0)) ≤ C * ENNReal.ofReal (R + 1) := by
  obtain ⟨B, hB, hb⟩ := even_future_inverse_arrival_band
  let D := (ENNReal.ofReal (phiEven (23 / 10)))⁻¹
  have hD : D < ∞ := lt_top_iff_ne_top.mpr
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (phiEven_pos (by norm_num))).ne')
  refine ⟨D + B, ENNReal.add_lt_top.mpr ⟨hD, hB⟩, ?_⟩
  intro s hsL hsU v R ell hR hell
  rw [inclusiveOccupation, _root_.add_apply, lintegral_add_measure, Kernel.id_apply,
    lintegral_dirac' (.inl s, 0) (inverseArrivalBand_measurable v R ell)]
  calc
    _ ≤ D + B * ENNReal.ofReal R := add_le_add
      (le_trans (inverseArrivalBand_le_weight v R ell (.inl s, 0)) (starting_inverse_weight_le s hsU))
      (hb s hsL hsU v R ell hR hell)
    _ ≤ (D + B * ENNReal.ofReal R) + (D * ENNReal.ofReal R + B) := le_add_of_nonneg_right zero_le
    _ = (D + B) * ENNReal.ofReal (R + 1) := by
      rw [ENNReal.ofReal_add hR.le (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_one]
      ring

theorem source_exponential_reward_tail {c : ℝ} (hc : 0 < c) :
    ∃ b : ℕ → ℝ≥0∞, Tendsto b atTop (𝓝 0) ∧ ∀ N : ℕ, ∀ s : EvenState,
      (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 → ∀ v ell : ℝ, 1 ≤ ell →
      (∫⁻ z, tailReward c v ell N z ∂inclusiveOccupation (.inl s, 0)) ≤ b N := by
  obtain ⟨C, hC, hb⟩ := source_inverse_phi_band
  refine ⟨tailBudget C c, tailBudget_tendsto_zero hC.ne hc, ?_⟩
  intro N s hsL hsU v ell hell
  exact weighted_tail_of_inverse_bands _ v ell (fun R hR => hb s hsL hsU v R ell hR hell) hc N

end NumberTheoryLean.EvenInverseBands

end

end Erdos970

end OAI
