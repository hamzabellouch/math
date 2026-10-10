import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.CorrectedDdcOffCompact

namespace OAI

section
section

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

variable (q : A.centers) (σ : 𝓢(Space,ℝ))
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D q).domain)
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D q).domain)
    (hσ : ∀ z ∈ K, σ z * coordinateWeight A q z = 1)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (L : Set Space) (hL : IsCompact L) (hLU : L ⊆ U)
    (hoff : ∀ z ∈ U, (extChartAt Model p.val).symm z ∉ (extChartAt Model q.val).symm '' K)

include hD hH hweak hB hdual hK hσ hφone hK₀ hU hUD hτ hρ hL hLU hoff in

lemma logForm_off_source_uniform : ∃ C : ℝ, 0 ≤ C ∧
    ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
    ∀ y ∈ L, ∀ v : Space, chartMetric J α p.val y v v = 1 →
    ‖ManifoldForms.pullback
      (logForm A J α hs ht H Gs q.val (D q) hφ hc hφD hR hsr.1 b
        ((hcenters b hb).trans hKD)).val
      (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v]‖ ≤ C := by
  obtain ⟨C₀,hC₀,hsource⟩ := logSource_dual_uniform A J α hs ht D hD q σ hφ hc hφD
    K hK hKD hσ hφone R hR K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,hobserver⟩ := correctedDdc_off_source_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ L hL hLU
  refine ⟨C₁*C₀,by positivity,?_⟩
  intro s hsr b hb y hy v hv
  have hsupport : tsupport (scalarChartLift q.val
      (HermitianRadial.translatedCutoffLog
        (hermitianCenterExtension J q.val (D q) hφ hc hφD) R s b)) ⊆
      (extChartAt Model q.val).symm '' K :=
    chartLift_tsupport_subset q.val (HermitianRadial.translatedCutoffLog_compact _ hR s b)
      ((HermitianRadial.translatedCutoffLog_support _ hR s b).trans (hcenters b hb))
      (hKD.trans (D q).domain_subset)
  have he := hobserver y hy v hv _
    (scalarChartLift_smooth q.val
      (HermitianRadial.translatedCutoffLog_smooth _ R hsr.1 b)
      (HermitianRadial.translatedCutoffLog_compact _ hR s b)
      (((HermitianRadial.translatedCutoffLog_support _ hR s b).trans
        ((hcenters b hb).trans hKD)).trans (D q).domain_subset))
    (fun z hz h => hoff z hz (hsupport h))
  exact he.trans (mul_le_mul_of_nonneg_left (hsource s hsr b hb) hC₁)

include hD hH hweak hB hdual hK hσ hφone hK₀ hU hUD hτ hρ hL hLU hoff in

lemma sqrtForm_off_source_uniform : ∃ C : ℝ, 0 ≤ C ∧
    ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
    ∀ y ∈ L, ∀ v : Space, chartMetric J α p.val y v v = 1 →
    ‖ManifoldForms.pullback
      (sqrtForm A J α hs ht H Gs q.val (D q) hφ hc hφD hR hsr.1 b
        ((hcenters b hb).trans hKD)).val
      (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v]‖ ≤ C := by
  obtain ⟨C₀,hC₀,hsource⟩ := sqrtSource_dual_uniform A J α hs ht D hD q σ hφ hc hφD
    K hK hKD hσ hφone R hR K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,hobserver⟩ := correctedDdc_off_source_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ L hL hLU
  refine ⟨C₁*C₀,by positivity,?_⟩
  intro s hsr b hb y hy v hv
  have hsupport : tsupport (scalarChartLift q.val
      (HermitianRadial.translatedCutoffSqrt
        (hermitianCenterExtension J q.val (D q) hφ hc hφD) R s b)) ⊆
      (extChartAt Model q.val).symm '' K :=
    chartLift_tsupport_subset q.val (HermitianRadial.translatedCutoffSqrt_compact _ hR s b)
      ((HermitianRadial.translatedCutoffSqrt_support _ hR s b).trans (hcenters b hb))
      (hKD.trans (D q).domain_subset)
  have he := hobserver y hy v hv _
    (scalarChartLift_smooth q.val
      (HermitianRadial.translatedCutoffSqrt_smooth _ R hsr.1 b)
      (HermitianRadial.translatedCutoffSqrt_compact _ hR s b)
      (((HermitianRadial.translatedCutoffSqrt_support _ hR s b).trans
        ((hcenters b hb).trans hKD)).trans (D q).domain_subset))
    (fun z hz h => hoff z hz (hsupport h))
  exact he.trans (mul_le_mul_of_nonneg_left (hsource s hsr b hb) hC₁)
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume Set Filter
open scoped Manifold ContDiff Topology SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hs in
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exists_coordinate_observer (p : A.centers) {z : Space} (hz : z ∈ (D p).domain)
    (hwz : coordinateWeight A p z ≠ 0) :
    ∃ τ ρ : 𝓢(Space,ℝ), ∃ U : Set Space,
      IsOpen U ∧ z ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ y ∈ U, τ y * coordinateWeight A p y = 1) ∧
      (∀ y ∈ U, ρ y = chartDensity J α p.val y) := by
  obtain ⟨τ,-,-,V,hV,hzV,hVD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hz hwz
  obtain ⟨ζ,hζ,hζV,U,hU,hzU,hUV,hζone⟩ := SchwartzCutoff.exists_one_near hV hzV
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset)
    (ζ.smooth ⊤) hζ (hζV.trans hVD)
  refine ⟨τ,ρ,U,hU,hzU,hUV.trans hVD,fun y hy => hτ y (hUV hy),?_⟩
  intro y hy
  simp only [ρ,SchwartzCutoff.schwartz_apply,hζone y hy,one_smul]

include hD in
include hs in
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma exists_observer_at {O : Set X} (hO : IsOpen O) {x : X} (hx : x ∈ O) :
    ∃ p : A.centers, x ∈ (extChartAt Model p.val).source ∧
      ∃ τ ρ : 𝓢(Space,ℝ), ∃ U : Set Space,
      IsOpen U ∧ extChartAt Model p.val x ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ y ∈ U, τ y * coordinateWeight A p y = 1) ∧
      (∀ y ∈ U, ρ y = chartDensity J α p.val y) ∧
      (∀ y ∈ U, (extChartAt Model p.val).symm y ∈ O) := by
  obtain ⟨p,hp,hz⟩ := exists_nonzero_weight_chart A J α ht D hD x
  have hxp : x ∈ (extChartAt Model p.val).source :=
    (D p).source_subset (hD p (subset_closure hp))
  have hwz : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxp] using hp
  obtain ⟨τ,ρ,V,hV,hzV,hVD,hτ,hρ⟩ := exists_coordinate_observer A J α hs ht D p hz hwz
  have hpre : IsOpen ((extChartAt Model p.val).target ∩ (extChartAt Model p.val).symm ⁻¹' O) :=
    (continuousOn_extChartAt_symm p.val).isOpen_inter_preimage (isOpen_extChartAt_target p.val) hO
  refine ⟨p,hxp,τ,ρ,V ∩ ((extChartAt Model p.val).target ∩ (extChartAt Model p.val).symm ⁻¹' O),
    hV.inter hpre,⟨hzV,(D p).domain_subset hz,?_⟩,
    fun _ hy => hVD hy.1,fun y hy => hτ y hy.1,fun y hy => hρ y hy.1,fun _ hy => hy.2.2⟩
  simpa only [mem_preimage,(extChartAt Model p.val).left_inv hxp] using hx
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
