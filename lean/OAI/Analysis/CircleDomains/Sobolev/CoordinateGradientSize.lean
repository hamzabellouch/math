import OAI.Analysis.CircleDomains.Sobolev.SphericalGradientEnergyNorm
import OAI.Analysis.CircleDomains.Selection.PhysicalRealCoordinate
import OAI.Analysis.CircleDomains.Modulus.CostPerturbation
import OAI.Analysis.CircleDomains.Probability.BandMeasure

namespace OAI

/-! The spherical Dirichlet norm is bounded by the two physical partial
norms used by the barrier construction, on the same measurable region. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem spherical_gradient_norm_le_partial_norms
    {μ : Measure (ℝ × ℝ)} {f : (ℝ × ℝ) → ℝ}
    (hf : MemLp (FiniteTransfer.planarGradient f) 2 μ) :
    Real.sqrt (∫x, FiniteTransfer.gradientEnergy f
      (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x ∂μ) ≤
      (eLpNorm (fun x => (fderiv ℝ f x) (1, 0)) 2 μ).toReal +
      (eLpNorm (fun x => (fderiv ℝ f x) (0, 1)) 2 μ).toReal := by
  rw [spherical_gradient_energy_eq_norms hf, Real.sqrt_le_iff]
  constructor
  · positivity
  · have hx := ENNReal.toReal_nonneg
      (a := eLpNorm (fun x => (fderiv ℝ f x) (1, 0)) 2 μ)
    have hy := ENNReal.toReal_nonneg
      (a := eLpNorm (fun x => (fderiv ℝ f x) (0, 1)) 2 μ)
    nlinarith [mul_nonneg hx hy]

theorem physical_coordinate_gradient_size_le
    {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Sphere) (π : Sphere → X) (Q : PhysicalRealCoordinate d π)
    {S : Set (ℝ × ℝ)} (hS : S ⊆ FiniteTransfer.realChartDomain d.physicalDomain)
    {A : ℝ≥0∞} (hA : A ≠ ∞)
    (hbound : ∀i : Fin 2, eLpNorm (fun x => (fderiv ℝ Q.physical x)
      (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict S) ≤ A) :
    Real.sqrt (∫x in S, FiniteTransfer.gradientEnergy Q.physical
      (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x) ≤ 2 * A.toReal := by
  have henergy := Q.physical_energy.mono_measure (Measure.restrict_mono_set volume hS)
  have hzero := ENNReal.toReal_mono hA (hbound 0)
  have hone := ENNReal.toReal_mono hA (hbound 1)
  have hroot := spherical_gradient_norm_le_partial_norms henergy
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero] at hzero hone
  linarith


theorem coordinate_band_counting_norm_le
    {X : Type*} [TopologicalSpace X] (U B : Set X) (u : X → ℝ)
    (m : X → ℝ≥0∞)
    (hband : ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[U] s) - liminf u (𝓝[U] s)) ≤ 4 * m s) :
    countingSquareNorm (B.indicator (fun s =>
      ENNReal.ofReal (limsup u (𝓝[U] s) - liminf u (𝓝[U] s)))) ≤
      4 * countingSquareNorm m := by
  classical
  rw [← countingSquareNorm_mul]
  apply countingSquareNorm_mono
  intro s
  by_cases hs : s ∈ B
  · simpa only [Set.indicator_of_mem hs] using hband s hs
  · simp only [Set.indicator_of_notMem hs]
    positivity

end CircleDomainRigidity

end

end OAI
