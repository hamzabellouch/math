import OAI.Geometry.RCD.Heat.HeatDensityL1Continuity
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensityFinite

namespace OAI

/-! # Jointly measurable densities for the constructed heat family

A finite measure equivalent to Hausdorff measure permits use of the
kernel Radon--Nikodym theorem even when the space has infinite volume.
The chain rule returns a density relative to the original Hausdorff measure.
-/

open Set Filter MeasureTheory Metric TopologicalSpace ProbabilityTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

/-- A jointly measurable version of the actual heat densities. -/
def heatJointDensity (t : ℝ) (ht : 0 < t) (x y : X) : ℝ :=
  ((hX.heatMarkovKernel hn p t ht).rnDeriv
      (Kernel.const X (hausdorff n X).toFinite) x y *
    (hausdorff n X).toFinite.rnDeriv (hausdorff n X) y).toReal

theorem heatJointDensity_measurable (t : ℝ) (ht : 0 < t) :
    Measurable (fun xy : X × X => hX.heatJointDensity hn p t ht xy.1 xy.2) :=
  ((Kernel.measurable_rnDeriv _ _).mul
    ((Measure.measurable_rnDeriv _ _).comp measurable_snd)).ennreal_toReal

theorem heatJointDensity_nonneg (t : ℝ) (ht : 0 < t) (x y : X) :
    0 ≤ hX.heatJointDensity hn p t ht x y := ENNReal.toReal_nonneg

theorem heatJointDensity_ae (t : ℝ) (ht : 0 < t) (x : X) :
    hX.heatJointDensity hn p t ht x =ᵐ[hausdorff n X]
      hX.heatRadonDensity hn p t ht x := by
  let μ := hausdorff n X
  let κ := hX.heatMarkovKernel hn p t ht
  let η := Kernel.const X μ.toFinite
  have hr : κ.rnDeriv η x =ᵐ[μ] (κ x).rnDeriv μ.toFinite :=
    (absolutelyContinuous_toFinite μ).ae_le (Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η))
  have hc := Measure.rnDeriv_mul_rnDeriv
    ((hX.heatRadonMeasure_absolutelyContinuous hn p t ht x).trans (absolutelyContinuous_toFinite μ))
    (κ := μ)
  filter_upwards [hr, hc] with y hy hz
  change (κ.rnDeriv η x y * μ.toFinite.rnDeriv μ y).toReal =
    ((κ x).rnDeriv μ y).toReal
  rw [hy]
  exact congrArg ENNReal.toReal hz

theorem heatJointDensity_integrable (t : ℝ) (ht : 0 < t) (x : X) :
    Integrable (hX.heatJointDensity hn p t ht x) (hausdorff n X) :=
  (hX.heatRadonDensity_integrable hn p t ht x).congr (hX.heatJointDensity_ae hn p t ht x).symm

theorem heatJointDensity_mass_one (t : ℝ) (ht : 0 < t) (x : X) :
    (∫ y, hX.heatJointDensity hn p t ht x y ∂hausdorff n X) = 1 := by
  rw [integral_congr_ae (hX.heatJointDensity_ae hn p t ht x)]
  exact hX.heatRadonDensity_mass_one hn p t ht x

theorem heatJointDensity_integral_bounded (t : ℝ) (ht : 0 < t) (x : X)
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf : ∀ᵐ y ∂hausdorff n X, |f y| ≤ C) :
    (∫ y, hX.heatJointDensity hn p t ht x y * f y ∂hausdorff n X) =
      hX.boundedHeat hn p f ⟨C, hf⟩ t ht x := by
  calc
    _ = ∫ y, hX.heatRadonDensity hn p t ht x y * f y ∂hausdorff n X := by
      apply integral_congr_ae
      filter_upwards [hX.heatJointDensity_ae hn p t ht x] with y hy
      rw [hy]
    _ = _ := hX.heatRadonDensity_integral_bounded hn p t ht x f C hf

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
