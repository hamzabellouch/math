import OAI.Geometry.RCD.Sobolev.SobolevTestFunctional
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Quantitative local mass bounds from an actual Sobolev source functional -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] in
theorem sobolevSourceFunctional_bound (q ψ : SobolevSpace μ hQ) (ρ : Lp ℝ 2 μ) :
    |sobolevSourceFunctional μ hQ q ρ ψ| ≤ (2*‖q‖+‖ρ‖)*‖ψ‖ := by
  change |energyForm μ hQ q ψ+inner ℝ ρ (SobolevSpace.toLp μ hQ ψ)| ≤ _
  calc
    _ ≤ |energyForm μ hQ q ψ|+|inner ℝ ρ (SobolevSpace.toLp μ hQ ψ)| := abs_add_le _ _
    _ ≤ 2*‖q‖*‖ψ‖+‖ρ‖*‖SobolevSpace.toLp μ hQ ψ‖ :=
      add_le_add (energyForm_abs_le_norm μ hQ q ψ) (abs_real_inner_le_norm _ _)
    _ ≤ 2*‖q‖*‖ψ‖+‖ρ‖*‖ψ‖ := by
      gcongr
      exact SobolevSpace.norm_toLp_le μ hQ ψ
    _ = _ := by ring

theorem measure_mass_le_sobolev_source (q ψ : SobolevSpace μ hQ) (ρ : Lp ℝ 2 μ)
    (σ : Measure X) [IsFiniteMeasure σ] {S : Set X} (hS : MeasurableSet S)
    (v : X → ℝ) (hv : Continuous v) (hvc : HasCompactSupport v)
    (hv0 : ∀ x, 0 ≤ v x) (hv1 : ∀ x∈S, 1 ≤ v x)
    (he : (∫ x, v x ∂σ)=sobolevSourceFunctional μ hQ q ρ ψ) :
    σ.real S ≤ (2*‖q‖+‖ρ‖)*‖ψ‖ := by
  have hi : Integrable (S.indicator (fun _ : X => (1:ℝ))) σ :=
    (integrable_const 1).indicator hS
  have hvi : Integrable v σ := hv.integrable_of_hasCompactSupport hvc
  have hb : ∀ x, S.indicator (fun _ : X => (1:ℝ)) x ≤ v x := by
    intro x
    by_cases hx : x∈S
    · simpa only [Set.indicator_of_mem hx] using hv1 x hx
    · simpa only [Set.indicator_of_notMem hx] using hv0 x
  calc
    σ.real S = ∫ x, S.indicator (fun _ : X => (1:ℝ)) x ∂σ := by
      rw [integral_indicator hS]
      simp
    _ ≤ ∫ x, v x ∂σ := integral_mono hi hvi hb
    _ = sobolevSourceFunctional μ hQ q ρ ψ := he
    _ ≤ |sobolevSourceFunctional μ hQ q ρ ψ| := le_abs_self _
    _ ≤ _ := sobolevSourceFunctional_bound μ hQ q ψ ρ

end RegularPointCoordinates

end

end OAI
