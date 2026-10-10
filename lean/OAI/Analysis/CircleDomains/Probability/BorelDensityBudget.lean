import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Borel density budgets for measurable families of finite measures. The
finite mass cap lets us use the jointly measurable kernel Radon–Nikodym
 derivative in Mathlib. -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X]

def BoundedDensityBudget (σ μ : Measure X) (mass energy : ℝ≥0∞) : Prop :=
  μ univ ≤ mass ∧ ∃ g : X → ℝ≥0∞,
    Measurable g ∧ μ = σ.withDensity g ∧ (∫⁻ x, g x ^ 2 ∂σ) ≤ energy

theorem measurableSet_boundedDensityBudget
    (μ : Z → Measure X) (hμ : Measurable μ)
    (σ : Measure X) [IsFiniteMeasure σ]
    (mass energy : ℝ≥0∞) (hmass : mass < ∞) :
    MeasurableSet {z | BoundedDensityBudget σ (μ z) mass energy} := by
  classical
  let A : Set Z := {z | μ z univ ≤ mass}
  have hA : MeasurableSet A :=
    measurableSet_le ((Measure.measurable_coe MeasurableSet.univ).comp hμ) measurable_const
  let κ : Kernel Z X := ⟨A.piecewise μ (fun _ => 0), hμ.piecewise hA measurable_const⟩
  let : IsFiniteKernel κ := ⟨⟨mass, hmass, fun z => by
    change A.piecewise μ (fun _ => 0) z univ ≤ mass
    by_cases hz : z ∈ A
    · change μ z univ ≤ mass at hz
      simpa only [Set.piecewise_eq_of_mem A μ _ hz] using hz
    · simp [Set.piecewise_eq_of_notMem A μ _ hz]⟩⟩
  let η : Kernel Z X := Kernel.const Z σ
  have heq (z : Z) (hz : z ∈ A) : κ z = μ z := by
    change A.piecewise μ (fun _ => 0) z = μ z
    exact Set.piecewise_eq_of_mem A μ _ hz
  have hrn (z : Z) : κ.rnDeriv η z =ᵐ[σ] (κ z).rnDeriv σ :=
    Kernel.rnDeriv_eq_rnDeriv_measure
  have hmeas : Measurable (fun z => ∫⁻ x, κ.rnDeriv η z x ^ 2 ∂σ) :=
    (Kernel.measurable_rnDeriv κ η).pow_const 2 |>.lintegral_prod_right'
  have hset : MeasurableSet {z | κ z ≪ σ ∧
      (∫⁻ x, κ.rnDeriv η z x ^ 2 ∂σ) ≤ energy} :=
    (Kernel.measurableSet_absolutelyContinuous κ η).inter
      (measurableSet_le hmeas measurable_const)
  convert hA.inter hset using 1
  ext z
  change BoundedDensityBudget σ (μ z) mass energy ↔
    z ∈ A ∧ κ z ≪ σ ∧ (∫⁻ x, κ.rnDeriv η z x ^ 2 ∂σ) ≤ energy
  constructor
  · rintro ⟨hz, g, hg, hμg, hge⟩
    have hk : κ z = σ.withDensity g := (heq z hz).trans hμg
    refine ⟨hz, hk ▸ withDensity_absolutelyContinuous _ _, ?_⟩
    have hrng : κ.rnDeriv η z =ᵐ[σ] g :=
      (hrn z).trans (by rw [hk]; exact Measure.rnDeriv_withDensity σ hg)
    apply le_trans (le_of_eq (lintegral_congr_ae ?_)) hge
    filter_upwards [hrng] with x hx
    exact congrArg (fun t : ℝ≥0∞ => t ^ 2) hx
  · rintro ⟨hz, hac, he⟩
    refine ⟨hz, κ.rnDeriv η z, Kernel.measurable_rnDeriv_right κ η z, ?_, he⟩
    rw [← heq z hz]
    exact ((withDensity_congr_ae (hrn z)).trans
      (Measure.withDensity_rnDeriv_eq (κ z) σ hac)).symm

end CircleDomainRigidity

end

end OAI
