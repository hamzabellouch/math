import OAI.NumberTheory.Jacobsthal.Probability.ArrivalKernelGeometry

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.AdmittedHarmonicPaths

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open FinitePathMeasures RegeneratingInverseBands ArrivalKernelGeometry
open HarmonicWeightKernel KernelWeightTransform KernelExitBarrier

noncomputable def admittedTilted (v ell : ℝ) : Kernel CostState CostState :=
  costKernel.restrict (arrivalSet_measurable v ell)

noncomputable def admittedHarmonic (v ell : ℝ) : Kernel CostState CostState :=
  harmonicKernel.restrict (arrivalSet_measurable v ell)

instance admittedTilted_isFiniteKernel (v ell : ℝ) : IsFiniteKernel (admittedTilted v ell) := by
  unfold admittedTilted
  infer_instance

instance admittedHarmonic_isSFiniteKernel (v ell : ℝ) : IsSFiniteKernel (admittedHarmonic v ell) := by
  unfold admittedHarmonic
  infer_instance

theorem admitted_weight_transform (v ell : ℝ) :
    admittedHarmonic v ell = conjugate (admittedTilted v ell) harmonicWeight :=
  conjugate_restrict costKernel harmonicWeight (arrivalSet_measurable v ell)

theorem admitted_tilted_final_selection (v ell : ℝ) (n : ℕ) :
    (admittedTilted v ell) ^ (n + 1) = (costKernel ^ (n + 1)).restrict (arrivalSet_measurable v ell) :=
  restricted_pow_eq costKernel (arrivalSet_measurable v ell) (costKernel_no_reentry v ell) n

theorem admitted_harmonic_final_selection (v ell : ℝ) (n : ℕ) :
    (admittedHarmonic v ell) ^ (n + 1) = (harmonicKernel ^ (n + 1)).restrict (arrivalSet_measurable v ell) :=
  restricted_pow_eq harmonicKernel (arrivalSet_measurable v ell) (harmonicKernel_no_reentry v ell) n

theorem admitted_prefix_change_of_measure (v ell : ℝ) (n : ℕ) (s : State)
    {F : CostState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂((admittedHarmonic v ell) ^ n) (s, 0)) =
      ENNReal.ofReal (InvariantInverseWeights.stateWeight s) *
        ∫⁻ y, ENNReal.ofReal (Real.exp (-2 * y.2) / InvariantInverseWeights.stateWeight y.1) * F y
          ∂((admittedTilted v ell) ^ n) (s, 0) := by
  rw [admitted_weight_transform, conjugate_pow_lintegral _ harmonicWeight n (s, 0) hF, initial_weight_inv]
  rfl

theorem admitted_tilted_future_selection (v ell : ℝ) :
    Kernel.sum (fun n : ℕ => (admittedTilted v ell) ^ (n + 1)) =
      OccupationDecomposition.fullOccupation.restrict (arrivalSet_measurable v ell) :=
  restricted_future_sum costKernel (arrivalSet_measurable v ell) (costKernel_no_reentry v ell)

theorem admitted_harmonic_future_selection (v ell : ℝ) :
    Kernel.sum (fun n : ℕ => (admittedHarmonic v ell) ^ (n + 1)) =
      (Kernel.sum (fun n : ℕ => harmonicKernel ^ (n + 1))).restrict (arrivalSet_measurable v ell) :=
  restricted_future_sum harmonicKernel (arrivalSet_measurable v ell) (harmonicKernel_no_reentry v ell)

theorem admitted_step_gap_bound (K : Kernel CostState CostState) (v ell : ℝ)
    (hflow : ∀ z, ∀ᵐ y ∂K z, gapValue v z = gapValue v y + currentExponent v y) (z : CostState) :
    ∀ᵐ y ∂K.restrict (arrivalSet_measurable v ell) z, gapValue v y ≤ gapValue v z - ell := by
  rw [Kernel.restrict_apply]
  filter_upwards [ae_restrict_of_ae (hflow z), ae_restrict_mem (arrivalSet_measurable v ell)] with y hy ha
  change ell < currentExponent v y at ha
  linarith

theorem admitted_pow_gap_bound (K : Kernel CostState CostState) (v ell : ℝ)
    (hflow : ∀ z, ∀ᵐ y ∂K z, gapValue v z = gapValue v y + currentExponent v y)
    (n : ℕ) (z : CostState) :
    ∀ᵐ y ∂((K.restrict (arrivalSet_measurable v ell)) ^ n) z,
      gapValue v y ≤ gapValue v z - (n : ℝ) * ell := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero]
    change ∀ᵐ y ∂Measure.dirac z, gapValue v y ≤ gapValue v z - (0 : ℝ) * ell
    exact (ae_dirac_iff (p := fun y => gapValue v y ≤ gapValue v z - (0 : ℝ) * ell)
      (measurableSet_le (gapValue_measurable v) measurable_const)).mpr (by simp)
  | succ n ih =>
    have hp : (K.restrict (arrivalSet_measurable v ell)) ^ (n + 1) =
        (K.restrict (arrivalSet_measurable v ell)) ∘ₖ ((K.restrict (arrivalSet_measurable v ell)) ^ n) := pow_succ' _ _
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (measurableSet_le (gapValue_measurable v) measurable_const)
    filter_upwards [ih] with y hy
    filter_upwards [admitted_step_gap_bound K v ell hflow y] with t ht
    calc
      gapValue v t ≤ gapValue v y - ell := ht
      _ ≤ (gapValue v z - (n : ℝ) * ell) - ell := sub_le_sub_right hy ell
      _ = _ := by push_cast; ring

theorem admitted_pow_zero_of_height (K : Kernel CostState CostState) (v ell : ℝ)
    (hflow : ∀ z, ∀ᵐ y ∂K z, gapValue v z = gapValue v y + currentExponent v y)
    (n : ℕ) (z : CostState) (hn : gapValue v z ≤ (n : ℝ) * ell) :
    ((K.restrict (arrivalSet_measurable v ell)) ^ n) z = 0 := by
  have hf : ∀ᵐ y ∂((K.restrict (arrivalSet_measurable v ell)) ^ n) z, False := by
    filter_upwards [admitted_pow_gap_bound K v ell hflow n z] with y hy
    have hp : 0 < gapValue v y := Real.exp_pos _
    linarith
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true] using hf

theorem admitted_tilted_finite_height (v : ℝ) {ell : ℝ} (hell : 0 < ell) (z : CostState)
    (n : ℕ) (hn : ⌈gapValue v z / ell⌉₊ ≤ n) : ((admittedTilted v ell) ^ n) z = 0 := by
  apply admitted_pow_zero_of_height costKernel v ell (costKernel_gap_flow v) n z
  apply (div_le_iff₀ hell).mp
  exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)

theorem admitted_harmonic_finite_height (v : ℝ) {ell : ℝ} (hell : 0 < ell) (z : CostState)
    (n : ℕ) (hn : ⌈gapValue v z / ell⌉₊ ≤ n) : ((admittedHarmonic v ell) ^ n) z = 0 := by
  apply admitted_pow_zero_of_height harmonicKernel v ell (harmonicKernel_gap_flow v) n z
  apply (div_le_iff₀ hell).mp
  exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)

end NumberTheoryLean.AdmittedHarmonicPaths

end

end Erdos970

end OAI
