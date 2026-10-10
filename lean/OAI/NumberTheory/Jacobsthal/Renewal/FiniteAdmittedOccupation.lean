import OAI.NumberTheory.Jacobsthal.Estimates.SignedCompletedPowers
import OAI.NumberTheory.Jacobsthal.Partitions.ContinuousHighPartition
import OAI.NumberTheory.Jacobsthal.Paths.FlagMeasurePartition

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.OriginalHarmonicOccupation

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures AdmittedHarmonicPaths ArrivalKernelGeometry
open KernelExitBarrier KernelWeightTransform HarmonicWeightKernel
open InvariantInverseWeights CostPrefixTransport RegeneratingInverseBands

noncomputable def occupation (K : Kernel CostState CostState) : Kernel CostState CostState :=
  Kernel.sum (fun n : ℕ => K^n)

instance occupation_isSFinite (K : Kernel CostState CostState) [IsSFiniteKernel K] :
    IsSFiniteKernel (occupation K) := by unfold occupation; infer_instance

theorem restricted_occupation_at (K : Kernel CostState CostState) {A : Set CostState}
    (hA : MeasurableSet A) (hNo : ∀ z ∉ A, K z A = 0) (z : CostState) (hz : z ∈ A) :
    occupation (K.restrict hA) z = (occupation K z).restrict A := by
  classical
  have hpow : ∀ n : ℕ, ((K.restrict hA)^n) z = ((K^n) z).restrict A := by
    intro n
    cases n with
    | zero =>
      change Measure.dirac z = (Measure.dirac z).restrict A
      rw [restrict_dirac' hA, ite_eq_left hz]
    | succ n => rw [restricted_pow_eq K hA hNo]; rfl
  apply Measure.ext
  intro B hB
  simp only [occupation]
  rw [Kernel.sum_apply' _ _ hB, Measure.restrict_apply hB,
    Kernel.sum_apply' _ _ (hB.inter hA)]
  apply tsum_congr
  intro n
  rw [hpow, Measure.restrict_apply hB]

theorem admitted_occupation_transform (v ell : ℝ) :
    occupation (admittedHarmonic v ell) = conjugate (occupation (admittedTilted v ell)) harmonicWeight := by
  rw [occupation, admitted_weight_transform, conjugate_prefix_sum]
  rfl

noncomputable def gapSquaredWeight (v : ℝ) (z : CostState) : ℝ≥0∞ :=
  ENNReal.ofReal ((gapValue v z)^2 / stateWeight z.1)

theorem gapSquaredWeight_measurable (v : ℝ) : Measurable (gapSquaredWeight v) :=
  ENNReal.measurable_ofReal.comp (((gapValue_measurable v).pow_const 2).div
    (stateWeight_measurable.comp measurable_fst))

theorem scaled_harmonic_weight (v : ℝ) (z : CostState) :
    ENNReal.ofReal ((Real.exp v)^2) * harmonicWeight z = gapSquaredWeight v z := by
  change ENNReal.ofReal ((Real.exp v)^2) * ENNReal.ofReal (Real.exp (-2*z.2) / stateWeight z.1) = _
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  change (Real.exp v)^2 * (Real.exp (-2*z.2) / stateWeight z.1) = (Real.exp (v-z.2))^2 / stateWeight z.1
  rw [← mul_div_assoc]
  congr 1
  rw [pow_two, ← Real.exp_add, ← Real.exp_add, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem scaled_ratio (v : ℝ) (s : State) (z : CostState) :
    ENNReal.ofReal ((Real.exp v)^2 / stateWeight s) * (harmonicWeight z / harmonicWeight (s,0)) =
      gapSquaredWeight v z := by
  rw [div_eq_mul_inv (harmonicWeight z) (harmonicWeight (s,0)), initial_weight_inv]
  calc
    _ = (ENNReal.ofReal ((Real.exp v)^2 / stateWeight s) * ENNReal.ofReal (stateWeight s)) * harmonicWeight z := by ring
    _ = ENNReal.ofReal ((Real.exp v)^2) * harmonicWeight z := by
      rw [← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (stateWeight_pos s).le),
        div_mul_cancel₀ _ (stateWeight_pos s).ne']
    _ = _ := scaled_harmonic_weight v z

theorem scaled_occupation (v ell : ℝ) (s : State) {F : CostState → ℝ≥0∞} (hF : Measurable F) :
    ENNReal.ofReal ((Real.exp v)^2 / stateWeight s) *
      (∫⁻ z, F z ∂occupation (admittedHarmonic v ell) (s,0)) =
      ∫⁻ z, gapSquaredWeight v z * F z ∂occupation (admittedTilted v ell) (s,0) := by
  rw [admitted_occupation_transform, conjugate_lintegral _ harmonicWeight (s,0) hF]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro z
  rw [← mul_assoc, scaled_ratio]

theorem admitted_tilted_occupation (v ell : ℝ) (z : CostState) (hz : z ∈ arrivalSet v ell) :
    occupation (admittedTilted v ell) z = (inclusiveOccupation z).restrict (arrivalSet v ell) := by
  simpa only [occupation, admittedTilted, ← inclusiveOccupation_eq_prefix_sum] using
    restricted_occupation_at costKernel (arrivalSet_measurable v ell) (costKernel_no_reentry v ell) z hz

theorem scaled_occupation_arrival (v ell : ℝ) (s : State) (hs : (s,0) ∈ arrivalSet v ell)
    {F : CostState → ℝ≥0∞} (hF : Measurable F) :
    ENNReal.ofReal ((Real.exp v)^2 / stateWeight s) *
      (∫⁻ z, F z ∂occupation (admittedHarmonic v ell) (s,0)) =
      ∫⁻ z in arrivalSet v ell, gapSquaredWeight v z * F z ∂inclusiveOccupation (s,0) := by
  rw [scaled_occupation v ell s hF, admitted_tilted_occupation v ell (s,0) hs]

end NumberTheoryLean.OriginalHarmonicOccupation

end

section

namespace NumberTheoryLean.FiniteAdmittedOccupation

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures LowStateHorizon AdmittedHarmonicPaths ArrivalKernelGeometry
open OriginalHarmonicOccupation SignedCompletedPowers CompactTestMeasurable
open ContinuousHighPartition SubMarkovFlagPowers FlagMeasurePartition FlaggedOccupationBound

theorem occupation_eq_finite (K : Kernel CostState CostState) (z : CostState) (N : ℕ)
    (hzero : ∀ n,N ≤ n → (K^n) z = 0) : occupation K z = ∑ n ∈ range N,(K^n) z := by
  apply Measure.ext
  intro B hB
  rw [occupation,Kernel.sum_apply' _ _ hB,Measure.finsetSum_apply]
  apply tsum_eq_sum
  intro n hn
  have hN : N ≤ n := by
    have hh : ¬n < N := by simpa only [Finset.mem_range] using hn
    omega
  rw [hzero n hN]
  simp

theorem occupation_integral_eq_finite (K : Kernel CostState CostState) [IsFiniteKernel K]
    (z : CostState) (N : ℕ) (hzero : ∀ n,N ≤ n → (K^n) z = 0)
    {F : CostState → ℝ} (hF : Measurable F) {A : ℝ} (hbound : ∀ y,|F y| ≤ A) :
    (∫ y,F y ∂occupation K z) = ∑ n ∈ range N,∫ y,F y ∂(K^n) z := by
  rw [occupation_eq_finite K z N hzero]
  apply integral_finsetSum_measure
  intro n _hn
  let := finite_kernel_power K n
  exact bounded_integrable hF hbound

theorem admitted_low_signed_error (v ell S B : ℝ) (hell : 1 ≤ ell) (hS : 0 < S) (hB : 0 < B)
    (s : State) (hs : stateRatio s ≤ S)
    (hgap : RegeneratingInverseBands.gapValue v (s,0) ≤ (23/10:ℝ)*B)
    {F : CostState → ℝ} (hF : Measurable F) {A : ℝ} (hbound : ∀ y,|F y| ≤ A) :
    ENNReal.ofReal |(∫ y,F y ∂occupation (admittedTilted v ell) (s,0))-
      (∫ y,F y ∂occupation (lowKernel costKernel v ell S) (s,0))| ≤
      ∑' n : ℕ,∫⁻ y,selected (fun a => ENNReal.ofReal |F a|) y
        ∂((tiltedFlagged v ell S)^n) (FlaggedHarmonicPaths.initial S (s,0)) := by
  let M := ⌈RegeneratingInverseBands.gapValue v (s,0)/ell⌉₊
  let N := sourceHorizon S B
  let T := max M N
  have hfullzero : ∀ n,T ≤ n → ((admittedTilted v ell)^n) (s,0) = 0 := by
    intro n hn
    exact admitted_tilted_finite_height v (by linarith) (s,0) n ((le_max_left _ _).trans hn)
  have hlowzero : ∀ n,T ≤ n → ((lowKernel costKernel v ell S)^n) (s,0) = 0 := by
    intro n hn
    exact tilted_source_horizon v ell S B hell hS hB (s,0) hgap n ((le_max_right _ _).trans hn)
  let : IsFiniteKernel (lowKernel costKernel v ell S) := by unfold lowKernel; infer_instance
  rw [occupation_integral_eq_finite _ _ T hfullzero hF hbound,
    occupation_integral_eq_finite _ _ T hlowzero hF hbound]
  have hI : ∀ n ∈ range T,Integrable F (((admittedTilted v ell)^n) (s,0)) := by
    intro n _hn
    let := finite_kernel_power (admittedTilted v ell) n
    exact bounded_integrable hF hbound
  have h := signed_finite_difference (admittedTilted v ell) (high_measurable S) T (s,0) hF hI
  have he : goodKernel (admittedTilted v ell) (high_measurable S) = lowKernel costKernel v ell S :=
    good_admitted_eq_low costKernel v ell S
  rw [he] at h
  have hinit : FlaggedHarmonicPaths.initial S (s,0) = ((s,0),false) := by
    simp only [FlaggedHarmonicPaths.initial,ite_eq_right (not_lt.mpr hs)]
  rw [hinit]
  exact h.trans (ENNReal.sum_le_tsum (range T))

theorem low_occupation_integral_eq_source_sum (v ell S B : ℝ) (hell : 1 ≤ ell) (hS : 0 < S) (hB : 0 < B)
    (z : CostState) (hgap : RegeneratingInverseBands.gapValue v z ≤ (23/10:ℝ)*B)
    {F : CostState → ℝ} (hF : Measurable F) {A : ℝ} (hbound : ∀ y,|F y| ≤ A) :
    (∫ y,F y ∂occupation (lowKernel costKernel v ell S) z) =
      ∑ n ∈ range (sourceHorizon S B),∫ y,F y ∂((lowKernel costKernel v ell S)^n) z := by
  let : IsFiniteKernel (lowKernel costKernel v ell S) := by unfold lowKernel; infer_instance
  exact occupation_integral_eq_finite _ _ _ (tilted_source_horizon v ell S B hell hS hB z hgap) hF hbound

end NumberTheoryLean.FiniteAdmittedOccupation

end

end Erdos970

end OAI
