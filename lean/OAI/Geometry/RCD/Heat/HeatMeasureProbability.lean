import OAI.Geometry.RCD.Heat.HeatMeasureConservation

namespace OAI

/-! # Probability mass at every center for the constructed heat measure -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonMeasure_real_mass_one (t : ℝ) (ht : 0 < t) (x : X) :
    (hX.heatRadonMeasure hn p t ht x).real univ = 1 := by
  let μ := hausdorff n X
  let := hX.openPos K n
  let M (y : X) := (hX.heatRadonMeasure hn p t ht y).real univ
  have hM : Continuous M := (hX.heatRadonMeasure_mass_lipschitz hn p t ht).continuous
  have hM1 (y : X) : M y ≤ 1 := by
    have hh := ENNReal.toReal_mono ENNReal.one_ne_top (hX.heatRadonMeasure_mass_le_one hn p t ht y)
    simpa only [M, Measure.real, ENNReal.toReal_one] using hh
  let F := radialCompactTest x 1 zero_lt_one
  have hF0 (y : X) : 0 ≤ F y := (radialCutoff_bounds x 1 y).1
  have hmean := hX.heatRadonMeasure_mass_average hn p t ht F hF0
  let Z (y : X) := F y * (1 - M y)
  have hZ : Continuous Z := F.continuous.mul (continuous_const.sub hM)
  have hZs : HasCompactSupport Z := F.hasCompactSupport.mul_right
  have hZi : Integrable Z μ := hZ.integrable_of_hasCompactSupport hZs
  have hZ0 (y : X) : 0 ≤ Z y := mul_nonneg (hF0 y) (sub_nonneg.mpr (hM1 y))
  have hiFM : Integrable (fun y => F y * M y) μ :=
    (F.continuous.mul hM).integrable_of_hasCompactSupport F.hasCompactSupport.mul_right
  have hInt : (∫ y, Z y ∂μ) = 0 := by
    have heq : Z = (fun y => F y - F y * M y) := by funext y; dsimp [Z]; ring
    rw [heq, integral_sub F.integrable hiFM]
    change (∫ y, F y ∂μ) - (∫ y, F y * (hX.heatRadonMeasure hn p t ht y).real univ ∂μ) = 0
    rw [hmean, sub_self]
  have hae : Z =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hZ0 hZi).mp hInt
  have heq : Z = 0 := Measure.eq_of_ae_eq hae hZ continuous_const
  have hz := congrFun heq x
  have hf : F x = 1 := by
    exact radialCutoff_eq_one x zero_lt_one (by simp)
  change F x * (1 - M x) = 0 at hz
  rw [hf, one_mul] at hz
  change M x = 1
  linarith

theorem heatRadonMeasure_mass_one (t : ℝ) (ht : 0 < t) (x : X) :
    hX.heatRadonMeasure hn p t ht x univ = 1 := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
  simpa only [Measure.real, ENNReal.toReal_one] using hX.heatRadonMeasure_real_mass_one hn p t ht x

instance heatRadonMeasure_probability (t : ℝ) (ht : 0 < t) (x : X) :
    IsProbabilityMeasure (hX.heatRadonMeasure hn p t ht x) :=
  ⟨hX.heatRadonMeasure_mass_one hn p t ht x⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
