import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianShell
import OAI.Geometry.TamingCompatibility.Functional.QuadraticShellLimit

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility
open Bundle Manifold ManifoldForms ManifoldVolume GeometricHilbert Set MeasureTheory Filter
open scoped Bundle Manifold ContDiff ENNReal Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel unitT2

theorem separating_probability_real_shell
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r →
      (∫ u, (1+(hermitianEDist J α hs ht x u.val.proj).toReal/r)⁻¹^6 ∂μ)/r^2 ≤ C := by
  obtain ⟨C,hC,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  refine ⟨8*C,by positivity,fun x r hr => ?_⟩
  have h := QuadraticShell.integral_profile_normalized_bound μ _
    (hermitianEDist_unit_measurable J α hs ht x) C hC (hgrowth x) hr
  simpa only [hermitian_profile_toReal J α hs ht _ _ hr] using h

theorem separating_probability_zero_density_tail
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (x : X) (hzero : Tendsto (fun r : ℝ =>
      μ.real {u : MetricUnit (hermitianMetric J α hs ht) |
        hermitianEDist J α hs ht x u.val.proj < ENNReal.ofReal r}/r^2)
      (𝓝[>] (0:ℝ)) (𝓝 0)) :
    Tendsto (fun r : ℝ =>
      (∫ u, (1+(hermitianEDist J α hs ht x u.val.proj).toReal/r)⁻¹^6 ∂μ)/r^2)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,hC,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  have h := QuadraticShell.integral_profile_normalized_zero μ _
    (hermitianEDist_unit_measurable J α hs ht x) C hC (hgrowth x) hzero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  exact hermitian_profile_toReal J α hs ht x u.val.proj hr

end TamingCompatibility

end
end

section
noncomputable section
namespace TamingCompatibility
open Bundle Manifold ManifoldForms ManifoldVolume GeometricHilbert Set MeasureTheory Filter
open scoped Bundle Manifold ContDiff ENNReal Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel unitT2

omit [ConnectedSpace X] in
lemma hermitian_real_shell_measurable
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] (r : ℝ) :
    Measurable (fun x : X =>
      (∫ u, (1+(hermitianEDist J α hs ht x u.val.proj).toReal/r)⁻¹^6 ∂μ)/r^2) := by
  have hp := (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp
    (continuous_subtype_val : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val))
  have hd : Measurable (fun p : X × MetricUnit (hermitianMetric J α hs ht) =>
      (hermitianEDist J α hs ht p.1 p.2.val.proj).toReal) :=
    (((hermitianEDist_continuous J α hs ht).comp
      (continuous_fst.prodMk (hp.comp continuous_snd))).measurable).ennreal_toReal
  have hm : StronglyMeasurable (fun p : X × MetricUnit (hermitianMetric J α hs ht) =>
      (1+(hermitianEDist J α hs ht p.1 p.2.val.proj).toReal/r)⁻¹^6) :=
    ((measurable_const.add (hd.div_const r)).inv.pow_const 6).stronglyMeasurable
  exact (hm.integral_prod_right.measurable).div_const _

theorem separating_probability_double_zero_density_tail
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (ν : Measure X) [IsFiniteMeasure ν]
    (hzero : ∀ᵐ x ∂ν, Tendsto (fun r : ℝ =>
      μ.real {u : MetricUnit (hermitianMetric J α hs ht) |
        hermitianEDist J α hs ht x u.val.proj < ENNReal.ofReal r}/r^2)
      (𝓝[>] (0:ℝ)) (𝓝 0)) :
    Tendsto (fun r : ℝ => ∫ x,
      (∫ u, (1+(hermitianEDist J α hs ht x u.val.proj).toReal/r)⁻¹^6 ∂μ)/r^2 ∂ν)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := separating_probability_real_shell J α hs ht μ hann
  have hm : ∀ᶠ r : ℝ in 𝓝[>] (0:ℝ), AEStronglyMeasurable (fun x : X =>
      (∫ u, (1+(hermitianEDist J α hs ht x u.val.proj).toReal/r)⁻¹^6 ∂μ)/r^2) ν :=
    Filter.Eventually.of_forall (fun r => (hermitian_real_shell_measurable J α hs ht μ r).aestronglyMeasurable)
  have hb : ∀ᶠ r : ℝ in 𝓝[>] (0:ℝ), ∀ᵐ x ∂ν,
      ‖(∫ u, (1+(hermitianEDist J α hs ht x u.val.proj).toReal/r)⁻¹^6 ∂μ)/r^2‖ ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (integral_nonneg (fun u => by positivity)) (sq_nonneg r))]
    exact hbound x r hr
  have hl : ∀ᵐ x ∂ν, Tendsto (fun r : ℝ =>
      (∫ u, (1+(hermitianEDist J α hs ht x u.val.proj).toReal/r)⁻¹^6 ∂μ)/r^2)
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    filter_upwards [hzero] with x hx
    exact separating_probability_zero_density_tail J α hs ht μ hann x hx
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence (fun _ : X => C) hm hb (integrable_const C) hl
end TamingCompatibility

end
end

end
end

end OAI
