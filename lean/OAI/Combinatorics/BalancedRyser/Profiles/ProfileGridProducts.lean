import OAI.Combinatorics.BalancedRyser.Profiles.ProfileGridMeasures
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileWeakDetection

namespace OAI

open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Set Filter TopologicalSpace

namespace Balanced.ProfileParameterGrids

section Sections

variable {P : Type*} [MeasurableSpace P]

theorem rightGrid_prod_apply (n : ℕ) (ν : FiniteMeasure P)
    {s : Set (ℝ × P)} (hs : MeasurableSet s) :
    (((rightGrid n).toFiniteMeasure.prod ν : FiniteMeasure (ℝ × P)) :
      Measure (ℝ × P)) s =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range (n + 1),
        (ν : Measure P) {p | ((((i + 1 : ℕ) : ℝ) / (n + 1)), p) ∈ s} := by
  change (rightGridMeasure n).prod (ν : Measure P) s = _
  rw [Measure.prod_apply hs, rightGridMeasure, lintegral_smul_measure,
    lintegral_finsetSum_measure]
  simp only [lintegral_dirac, smul_eq_mul]
  rfl

theorem rightGrid_prod_real (n : ℕ) (ν : FiniteMeasure P)
    {s : Set (ℝ × P)} (hs : MeasurableSet s) :
    (((rightGrid n).toFiniteMeasure.prod ν : FiniteMeasure (ℝ × P)) :
      Measure (ℝ × P)).real s =
      (∑ i ∈ Finset.range (n + 1),
        (ν : Measure P).real {p | ((((i + 1 : ℕ) : ℝ) / (n + 1)), p) ∈ s}) /
        (n + 1) := by
  rw [Measure.real, rightGrid_prod_apply n ν hs, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp [ENNReal.toReal_add, Measure.real, div_eq_mul_inv, mul_comm]

theorem powerGrid_prod_apply (γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ) (ν : FiniteMeasure P)
    {s : Set (ℝ × P)} (hs : MeasurableSet s) :
    (((powerGrid γ hγ n).toFiniteMeasure.prod ν : FiniteMeasure (ℝ × P)) :
      Measure (ℝ × P)) s =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range (n + 1),
        (ν : Measure P) {p | (((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹), p) ∈ s} := by
  change (Measure.map (fun x : ℝ => x ^ γ⁻¹) (rightGridMeasure n)).prod
    (ν : Measure P) s = _
  rw [Measure.prod_apply hs, lintegral_map (measurable_measure_prodMk_left hs)
    (Real.continuous_rpow_const (inv_nonneg.mpr hγ)).measurable,
    rightGridMeasure, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac, smul_eq_mul]
  rfl

theorem powerGrid_prod_real (γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ) (ν : FiniteMeasure P)
    {s : Set (ℝ × P)} (hs : MeasurableSet s) :
    (((powerGrid γ hγ n).toFiniteMeasure.prod ν : FiniteMeasure (ℝ × P)) :
      Measure (ℝ × P)).real s =
      (∑ i ∈ Finset.range (n + 1),
        (ν : Measure P).real {p | (((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹), p) ∈ s}) /
        (n + 1) := by
  rw [Measure.real, powerGrid_prod_apply γ hγ n ν hs, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp [ENNReal.toReal_add, Measure.real, div_eq_mul_inv, mul_comm]

end Sections

section Limits

variable {P I : Type*} [Nonempty P] [MeasurableSpace P] [TopologicalSpace P]
    [SecondCountableTopology P] [PseudoMetrizableSpace P] [OpensMeasurableSpace P]
    {l : Filter I} {N : I → ℕ}
    {ν : I → FiniteMeasure P} {nuLimit : FiniteMeasure P}

theorem tendsto_rightGrid_finite_prod (hN : Tendsto N l atTop)
    (hν : Tendsto ν l (𝓝 nuLimit)) :
    Tendsto (fun i => (rightGrid (N i)).toFiniteMeasure.prod (ν i)) l
      (𝓝 (unitUniform.toFiniteMeasure.prod nuLimit)) := by
  apply ProfileWeakDetection.tendsto_finiteMeasure_prod _ hν
  exact ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp
    (tendsto_rightGrid.comp hN)

theorem tendsto_powerGrid_finite_prod (γ : ℝ) (hγ : 0 ≤ γ)
    (hN : Tendsto N l atTop) (hν : Tendsto ν l (𝓝 nuLimit)) :
    Tendsto (fun i => (powerGrid γ hγ (N i)).toFiniteMeasure.prod (ν i)) l
      (𝓝 ((powerUniform γ hγ).toFiniteMeasure.prod nuLimit)) := by
  apply ProfileWeakDetection.tendsto_finiteMeasure_prod _ hν
  exact ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp
    ((tendsto_powerGrid γ hγ).comp hN)

theorem rightGrid_section_liminf [l.NeBot] (hN : Tendsto N l atTop)
    (hν : Tendsto ν l (𝓝 nuLimit)) {s : Set (ℝ × P)} (hs : IsOpen s) :
    ((unitUniform.toFiniteMeasure.prod nuLimit : FiniteMeasure (ℝ × P)) :
      Measure (ℝ × P)).real s ≤
      l.liminf (fun a => (∑ i ∈ Finset.range (N a + 1),
        (ν a : Measure P).real {p | ((((i + 1 : ℕ) : ℝ) / (N a + 1)), p) ∈ s}) /
        (N a + 1)) := by
  have h := ProfileWeakDetection.finiteMeasureReal_le_liminf_open
    (tendsto_rightGrid_finite_prod hN hν) hs
  simpa only [rightGrid_prod_real _ _ hs.measurableSet] using h

theorem powerGrid_section_liminf [l.NeBot] (γ : ℝ) (hγ : 0 ≤ γ)
    (hN : Tendsto N l atTop) (hν : Tendsto ν l (𝓝 nuLimit))
    {s : Set (ℝ × P)} (hs : IsOpen s) :
    (((powerUniform γ hγ).toFiniteMeasure.prod nuLimit : FiniteMeasure (ℝ × P)) :
      Measure (ℝ × P)).real s ≤
      l.liminf (fun a => (∑ i ∈ Finset.range (N a + 1),
        (ν a : Measure P).real {p | (((((i + 1 : ℕ) : ℝ) / (N a + 1)) ^ γ⁻¹), p) ∈ s}) /
        (N a + 1)) := by
  have h := ProfileWeakDetection.finiteMeasureReal_le_liminf_open
    (tendsto_powerGrid_finite_prod γ hγ hN hν) hs
  simpa only [powerGrid_prod_real _ _ _ _ hs.measurableSet] using h

omit [Nonempty P] [PseudoMetrizableSpace P] in

theorem tendsto_probability_finite_prod_zero
    (μ : I → ProbabilityMeasure ℝ) (hν : Tendsto ν l (𝓝 0)) :
    Tendsto (fun a => (μ a).toFiniteMeasure.prod (ν a)) l (𝓝 0) := by
  apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
  have hmass := hν.mass
  simpa only [FiniteMeasure.mass_prod, ProbabilityMeasure.mass_toFiniteMeasure,
    one_mul, FiniteMeasure.zero_mass] using hmass

end Limits

end Balanced.ProfileParameterGrids

end OAI
