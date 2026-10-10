import OAI.NumberTheory.Jacobsthal.Analysis.ContinuousHighRemoval
import OAI.NumberTheory.Jacobsthal.Paths.FlaggedHarmonicPaths

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.AdmittedHighRemoval

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures ArrivalKernelGeometry AdmittedHarmonicPaths
open RegeneratingInverseBands FlaggedHarmonicPaths KernelMappedDomination

theorem pow_map_state (v ell S : ℝ) (n : ℕ) (z : FlagState) :
    (((FlaggedHarmonicPaths.kernel v ell S)^n) z).map Prod.fst =
      ((admittedHarmonic v ell)^n) z.1 := by
  exact mapped_pow_eq _ _ Prod.fst measurable_fst (kernel_map_state v ell S) n z

theorem pow_map_coordinates_le (v S : ℝ) {ell : ℝ} (hell : 0 ≤ ell) (n : ℕ) (z : FlagState) :
    (((FlaggedHarmonicPaths.kernel v ell S)^n) z).map (coordinates v) ≤
      ((ErdosPrimeInputs.HighPrefixKernel.kernel ell S)^n) (coordinates v z) :=
  mapped_pow_le _ _ (coordinates v) (coordinates_measurable v)
    (kernel_map_coordinates_le v S hell) n z

noncomputable def lowHighMass (v ell S : ℝ) (z : CostState) (K : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ((FlaggedHarmonicPaths.kernel v ell S)^n) (initial S z)
    {y : FlagState | y.2 = true ∧ gapValue v y.1 ≤ K}

noncomputable def reward (v c : ℝ) (y : FlagState) : ℝ≥0∞ :=
  if y.2 = true ∧ 0 ≤ gapValue v y.1 then ENNReal.ofReal (Real.exp (-c * gapValue v y.1)) else 0

noncomputable def rewardedHighMass (v ell S : ℝ) (z : CostState) (c : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ∫⁻ y, reward v c y ∂((FlaggedHarmonicPaths.kernel v ell S)^n) (initial S z)

theorem low_mass_le_unrestricted (v S : ℝ) {ell : ℝ} (hell : 0 ≤ ell) (z : CostState) (K : ℝ) :
    lowHighMass v ell S z K ≤ ErdosPrimeInputs.HighPrefixBounds.lowHighMass ell S
      (currentExponent v z) (gapValue v z) K := by
  unfold lowHighMass ErdosPrimeInputs.HighPrefixBounds.lowHighMass
  apply ENNReal.tsum_le_tsum
  intro n
  let A : Set ExponentState := {y | y.2.2 = true ∧ y.2.1 ≤ K}
  have hA : MeasurableSet A := by
    exact ((measurable_snd.comp measurable_snd) (measurableSet_singleton true)).inter
      (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const)
  have h := Measure.le_iff.mp (pow_map_coordinates_le v S hell n (initial S z)) A hA
  rw [Measure.map_apply (coordinates_measurable v) hA, initial_coordinates] at h
  exact h

theorem reward_mass_le_unrestricted (v S : ℝ) {ell : ℝ} (hell : 0 ≤ ell) (z : CostState) (c : ℝ) :
    rewardedHighMass v ell S z c ≤ ErdosPrimeInputs.HighPrefixBounds.rewardedHighMass ell S
      (currentExponent v z) (gapValue v z) c := by
  have h := mapped_prefix_sum_le (FlaggedHarmonicPaths.kernel v ell S)
    (ErdosPrimeInputs.HighPrefixKernel.kernel ell S) (coordinates v) (coordinates_measurable v)
    (kernel_map_coordinates_le v S hell) (initial S z)
    (ErdosPrimeInputs.HighPrefixBounds.reward_measurable c)
  rw [initial_coordinates] at h
  exact h

theorem low_gap_high_removal (K A : ℝ) : ∀ᶠ B : ℝ in atTop,
    ∀ v ell : ℝ, ∀ z : CostState, 1 ≤ ell → ell ≤ B → currentExponent v z = B →
      lowHighMass v ell ((Real.log B)^2) z K ≤ ENNReal.ofReal (B^(-A)) := by
  filter_upwards [ErdosPrimeInputs.ContinuousHighRemoval.low_gap_high_removal K A] with B hB
  intro v ell z hell hellB hexp
  calc
    _ ≤ ErdosPrimeInputs.HighPrefixBounds.lowHighMass ell ((Real.log B)^2)
        (currentExponent v z) (gapValue v z) K := low_mass_le_unrestricted v _ (by linarith) z K
    _ ≤ _ := by rw [hexp]; exact hB ell hell hellB (gapValue v z)

theorem rewarded_high_removal (c : ℝ) (hc : 0 < c) (A : ℝ) : ∀ᶠ B : ℝ in atTop,
    ∀ v ell : ℝ, ∀ z : CostState, 1 ≤ ell → ell ≤ B → currentExponent v z = B →
      rewardedHighMass v ell ((Real.log B)^2) z c ≤ ENNReal.ofReal (B^(-A)) := by
  filter_upwards [ErdosPrimeInputs.ContinuousHighRemoval.rewarded_high_removal c hc A] with B hB
  intro v ell z hell hellB hexp
  calc
    _ ≤ ErdosPrimeInputs.HighPrefixBounds.rewardedHighMass ell ((Real.log B)^2)
        (currentExponent v z) (gapValue v z) c := reward_mass_le_unrestricted v _ (by linarith) z c
    _ ≤ _ := by rw [hexp]; exact hB ell hell hellB (gapValue v z)

end NumberTheoryLean.AdmittedHighRemoval

end

end Erdos970

end OAI
