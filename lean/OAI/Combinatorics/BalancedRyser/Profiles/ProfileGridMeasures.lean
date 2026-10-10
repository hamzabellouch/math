import OAI.Combinatorics.BalancedRyser.Profiles.ProfileParameterGrids

namespace OAI

open scoped ENNReal Topology BigOperators
open MeasureTheory Set Filter TopologicalSpace

namespace Balanced.ProfileParameterGrids

noncomputable def rightGridMeasure (n : ℕ) : Measure ℝ :=
  ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ •
    ∑ i ∈ Finset.range (n + 1), Measure.dirac (((i + 1 : ℕ) : ℝ) / (n + 1))

instance rightGrid_probability (n : ℕ) : IsProbabilityMeasure (rightGridMeasure n) := by
  constructor
  simp only [rightGridMeasure, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

noncomputable def rightGrid (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨rightGridMeasure n, inferInstance⟩

noncomputable def unitUniform : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Icc (0 : ℝ) 1), by constructor; simp⟩

theorem integral_rightGrid (n : ℕ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(rightGrid n : Measure ℝ)) =
      (∑ i ∈ Finset.range (n + 1), f (((i + 1 : ℕ) : ℝ) / (n + 1))) / (n + 1) := by
  change (∫ x, f x ∂rightGridMeasure n) = _
  rw [rightGridMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ => integrable_dirac (by finiteness))]
  simp [ENNReal.toReal_add, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem integral_unitUniform (f : ℝ → ℝ) :
    (∫ x, f x ∂(unitUniform : Measure ℝ)) = ∫ x in (0 : ℝ)..1, f x := by
  change (∫ x in Icc (0 : ℝ) 1, f x) = _
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem tendsto_rightGrid : Tendsto rightGrid atTop (𝓝 unitUniform) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simp_rw [integral_rightGrid, integral_unitUniform]
  have h := (tendsto_right_grid (f := fun x : ℝ => f x)
    f.continuous.continuousOn).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h

noncomputable def powerGrid (γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ) : ProbabilityMeasure ℝ :=
  (rightGrid n).map
    (⟨fun value : ℝ => value ^ γ⁻¹,
      Real.continuous_rpow_const (inv_nonneg.mpr hγ)⟩ : C(ℝ, ℝ))

noncomputable def powerUniform (γ : ℝ) (hγ : 0 ≤ γ) : ProbabilityMeasure ℝ :=
  unitUniform.map
    (⟨fun value : ℝ => value ^ γ⁻¹,
      Real.continuous_rpow_const (inv_nonneg.mpr hγ)⟩ : C(ℝ, ℝ))

theorem integral_powerGrid (γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ) (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ x, f x ∂(powerGrid γ hγ n : Measure ℝ)) =
      (∑ i ∈ Finset.range (n + 1),
        f ((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹)) / (n + 1) := by
  change (∫ x, f x ∂(Measure.map (fun x : ℝ => x ^ γ⁻¹)
    (rightGrid n : Measure ℝ))) = _
  rw [integral_map
    (Real.continuous_rpow_const (inv_nonneg.mpr hγ)).measurable.aemeasurable
    f.continuous.aestronglyMeasurable, integral_rightGrid]

theorem tendsto_powerGrid (γ : ℝ) (hγ : 0 ≤ γ) :
    Tendsto (powerGrid γ hγ) atTop (𝓝 (powerUniform γ hγ)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    rightGrid unitUniform tendsto_rightGrid
    (Real.continuous_rpow_const (inv_nonneg.mpr hγ))

theorem integral_powerUniform {γ : ℝ} (hγ : 1 ≤ γ) (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ x, f x ∂(powerUniform γ (zero_le_one.trans hγ) : Measure ℝ)) =
      ∫ z in (0 : ℝ)..1, f z * (γ * z ^ (γ - 1)) := by
  change (∫ x, f x ∂(Measure.map (fun x : ℝ => x ^ γ⁻¹)
    (unitUniform : Measure ℝ))) = _
  rw [integral_map
    (Real.continuous_rpow_const (inv_nonneg.mpr (zero_le_one.trans hγ))).measurable.aemeasurable
    f.continuous.aestronglyMeasurable, integral_unitUniform]
  exact integral_power_grid_density f.continuous.continuousOn hγ

section Products

variable {P : Type*} [MeasurableSpace P] [TopologicalSpace P]
    [SecondCountableTopology P] [PseudoMetrizableSpace P] [OpensMeasurableSpace P]

theorem tendsto_rightGrid_prod {ν : ℕ → ProbabilityMeasure P} {nuLimit : ProbabilityMeasure P}
    (hν : Tendsto ν atTop (𝓝 nuLimit)) :
    Tendsto (fun n => (rightGrid n).prod (ν n)) atTop (𝓝 (unitUniform.prod nuLimit)) := by
  exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    (tendsto_rightGrid.prodMk_nhds hν)

theorem tendsto_powerGrid_prod (γ : ℝ) (hγ : 0 ≤ γ)
    {ν : ℕ → ProbabilityMeasure P} {nuLimit : ProbabilityMeasure P}
    (hν : Tendsto ν atTop (𝓝 nuLimit)) :
    Tendsto (fun n => (powerGrid γ hγ n).prod (ν n)) atTop
      (𝓝 ((powerUniform γ hγ).prod nuLimit)) := by
  exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    ((tendsto_powerGrid γ hγ).prodMk_nhds hν)

theorem rightGrid_prod_open_liminf {ν : ℕ → ProbabilityMeasure P} {nuLimit : ProbabilityMeasure P}
    (hν : Tendsto ν atTop (𝓝 nuLimit)) {U : Set (ℝ × P)} (hU : IsOpen U) :
    ((unitUniform.prod nuLimit : ProbabilityMeasure (ℝ × P)) : Measure (ℝ × P)) U ≤
      atTop.liminf (fun n =>
        (((rightGrid n).prod (ν n) : ProbabilityMeasure (ℝ × P)) : Measure (ℝ × P)) U) :=
  ProbabilityMeasure.le_liminf_measure_open_of_tendsto (tendsto_rightGrid_prod hν) hU

theorem powerGrid_prod_open_liminf (γ : ℝ) (hγ : 0 ≤ γ)
    {ν : ℕ → ProbabilityMeasure P} {nuLimit : ProbabilityMeasure P}
    (hν : Tendsto ν atTop (𝓝 nuLimit)) {U : Set (ℝ × P)} (hU : IsOpen U) :
    (((powerUniform γ hγ).prod nuLimit : ProbabilityMeasure (ℝ × P)) : Measure (ℝ × P)) U ≤
      atTop.liminf (fun n =>
        (((powerGrid γ hγ n).prod (ν n) : ProbabilityMeasure (ℝ × P)) : Measure (ℝ × P)) U) :=
  ProbabilityMeasure.le_liminf_measure_open_of_tendsto (tendsto_powerGrid_prod γ hγ hν) hU

end Products

end Balanced.ProfileParameterGrids

end OAI
