import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianGlobalLower

namespace OAI

section
section

section
noncomputable section
open MeasureTheory Set

lemma probability_mass_bound_of_test {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {E : Set Y} (hE : MeasurableSet E)
    {f : Y → ℝ} (hf : Integrable f μ) (hzero : ∫ y, f y ∂μ = 0)
    {C c s : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hs : 0 < s)
    (hlower : ∀ y, -C ≤ f y) (hball : ∀ y ∈ E, c/s^2 ≤ f y) :
    μ.real E ≤ (C/c)*s^2 := by
  have hfi : Integrable (fun y => f y+C) μ := hf.add (integrable_const C)
  have hIi : Integrable (E.indicator (fun _ : Y => c/s^2)) μ :=
    (integrable_const _).indicator hE
  have hle : ∀ y, E.indicator (fun _ : Y => c/s^2) y ≤ f y+C := by
    intro y
    by_cases hy : y ∈ E
    · rw [indicator_of_mem hy]
      linarith [hball y hy]
    · rw [indicator_of_notMem hy]
      linarith [hlower y]
  have hmass := integral_mono hIi hfi hle
  rw [integral_indicator_const _ hE,integral_add hf (integrable_const C),hzero,
    integral_const] at hmass
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,zero_add] at hmass
  change μ.real E * (c/s^2) ≤ C at hmass
  have hsp : 0 < s^2 := sq_pos_of_pos hs
  have ht : μ.real E * c ≤ C*s^2 := by
    apply (div_le_iff₀ hsp).mp
    simpa only [mul_div_assoc] using hmass
  have he : (C/c)*s^2 = (C*s^2)/c := by ring
  rw [he]
  exact (le_div_iff₀ hc).mpr ht

end
end

section
noncomputable section
namespace TamingCompatibility
open Bundle Set MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
attribute [local instance] unitMeasurable unitBorel unitT2

omit [T2Space X] in
lemma unit_base_preimage_measurable
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    {K : Set X} (hK : _root_.IsClosed K) :
    MeasurableSet {u : MetricUnit g | u.val.proj ∈ K} := by
  exact (hK.preimage ((FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val)).measurableSet

omit [IsManifold Model ∞ X] [T2Space X] in
lemma inverse_chart_compact_image (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    IsCompact ((extChartAt Model p).symm '' K) :=
  hK.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hKT)
end TamingCompatibility

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)
variable (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)

attribute [local instance] unitMeasurable unitBorel unitT2

include hD hH hweak hB hdual hU hUD hτ hρ hφ hc hφD hK hKU hφone hR hK₀ hcenters in

theorem separating_probability_chart_mass
    (hR1 : 2*R ≤ 1)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r ≤ 2*R ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ K₀,
        μ.real {u : MetricUnit (hermitianMetric J α hs ht) |
          u.val.proj ∈ (extChartAt Model p.val).symm '' Metric.closedBall b s} ≤ C*s^2 := by
  obtain ⟨a,c,r,C,ha,hc',hr,hrR,hC,htest⟩ := exists_combined_unit_bounds
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1
  refine ⟨C/c,r,by positivity,hr,hrR,?_⟩
  intro s hsr b hb
  let β := combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
    ((hcenters b hb).trans (hKU.trans hUD))
  have hβc : IsClosed β.val := combinedForm_closed A J α hs ht H Gs p.val (D p)
    hφ hc hφD a hR hsr.1 b ((hcenters b hb).trans (hKU.trans hUD))
      (harmonicLift_closed A J α hs ht D hD H hH)
  have hβi : IsInvariant β.val J := combinedForm_invariant A J α hs ht H Gs p.val (D p)
    hφ hc hφD a hR hsr.1 b ((hcenters b hb).trans (hKU.trans hUD)) hweak
  let f := unitEvaluation J (hermitianMetric J α hs ht) β.val β.property
  have hf : Integrable f μ := f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hz : ∫ u, f u ∂μ = 0 := hann β hβc hβi
  have hballT : Metric.closedBall b s ⊆ (extChartAt Model p.val).target :=
    (Metric.closedBall_subset_closedBall (hsr.2.trans hrR)).trans
      ((hcenters b hb).trans (hKU.trans (hUD.trans (D p).domain_subset)))
  have hE := unit_base_preimage_measurable (hermitianMetric J α hs ht)
    (inverse_chart_compact_image p.val (isCompact_closedBall b s) hballT).isClosed
  exact probability_mass_bound_of_test μ hE hf hz hC hc' hsr.1
    (htest s hsr b hb).1 (htest s hsr b hb).2
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
