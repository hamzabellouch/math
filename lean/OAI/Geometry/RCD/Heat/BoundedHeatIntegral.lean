import OAI.Geometry.RCD.Heat.HeatRadonDensity
import OAI.Geometry.RCD.Heat.BoundedHeatLimit
import OAI.Geometry.RCD.Metric.BoundedContinuousL2Approximation

namespace OAI

/-! # Heat measure representation for all bounded L² data -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

/-- Uniform compact approximation and absolute continuity extend the
constructed measure representation to every bounded L² datum. -/
theorem heatRadonMeasure_integral_bounded (t : ℝ) (ht : 0 < t) (x : X)
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf : ∀ᵐ y ∂hausdorff n X, |f y| ≤ C) :
    (∫ y, f y ∂hX.heatRadonMeasure hn p t ht x) = hX.boundedHeat hn p f ⟨C, hf⟩ t ht x := by
  let μ := hausdorff n X
  let ν := hX.heatRadonMeasure hn p t ht x
  obtain ⟨F, hF, hlim⟩ := exists_bounded_continuous_L2_approximation μ f C hf
  have hb (i : ℕ) : ∀ᵐ y ∂μ, |compactTestToL2 μ (F i) y| ≤ C := by
    filter_upwards [compactTestToL2_coe μ (F i)] with y hy
    rw [hy]
    exact hF i y
  obtain ⟨s, hs, hsae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hrep : ∀ᵐ y ∂μ, ∀ i, compactTestToL2 μ (F i) y = F i y :=
    ae_all_iff.mpr (fun i => compactTestToL2_coe μ (F i))
  have hFa : ∀ᵐ y ∂μ, Tendsto (fun i => F (s i) y) atTop (𝓝 (f y)) := by
    filter_upwards [hsae, hrep] with y hy he
    simpa only [he] using hy
  have hFan : ∀ᵐ y ∂ν, Tendsto (fun i => F (s i) y) atTop (𝓝 (f y)) :=
    (hX.heatRadonMeasure_absolutelyContinuous hn p t ht x).ae_le hFa
  have hleft : Tendsto (fun i => ∫ y, F (s i) y ∂ν) atTop (𝓝 (∫ y, f y ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (C : ℝ))
    · intro i
      exact (F (s i)).continuous.aestronglyMeasurable
    · exact integrable_const _
    · intro i
      exact Eventually.of_forall fun y => hF (s i) y
    · exact hFan
  have hright := (hX.boundedHeat_tendsto hn p (fun i => compactTestToL2 μ (F i))
    f C hb hf hlim t ht x).comp hs.tendsto_atTop
  have heq (i : ℕ) : (∫ y, F (s i) y ∂ν) =
      hX.boundedHeat hn p (compactTestToL2 μ (F (s i))) ⟨C, hb (s i)⟩ t ht x :=
    hX.heatRadonMeasure_integral hn p t ht x (F (s i))
  have hright' : Tendsto (fun i => ∫ y, F (s i) y ∂ν) atTop
      (𝓝 (hX.boundedHeat hn p f ⟨C, hf⟩ t ht x)) := by
    simp_rw [heq]
    exact hright
  exact tendsto_nhds_unique hleft hright'

/-- The actual probability density represents all bounded L² heat data. -/
theorem heatRadonDensity_integral_bounded (t : ℝ) (ht : 0 < t) (x : X)
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf : ∀ᵐ y ∂hausdorff n X, |f y| ≤ C) :
    (∫ y, hX.heatRadonDensity hn p t ht x y * f y ∂hausdorff n X) =
      hX.boundedHeat hn p f ⟨C, hf⟩ t ht x := by
  change (∫ y, ((hX.heatRadonMeasure hn p t ht x).rnDeriv (hausdorff n X) y).toReal * f y
    ∂hausdorff n X) = _
  rw [integral_toReal_rnDeriv_mul (hX.heatRadonMeasure_absolutelyContinuous hn p t ht x)]
  exact hX.heatRadonMeasure_integral_bounded hn p t ht x f C hf

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
