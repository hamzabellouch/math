import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeScalarRaw

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame GeometricChart ManifoldLocalization ManifoldVolume
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

lemma pairing_coordinateTest (a : TwoForm X)
    {q : Space → HodgeNormalSymbol.W} (hqD : tsupport q ⊆ D.domain) (z : Space) :
    MetricForms.pairing (coordinateMetric J α ht p z) (ManifoldForms.pullback a (extChartAt Model p).symm z)
      (coordinateTest J α ht p D q z) = ⟪rawVector J α ht p D a z,q z⟫ := by
  by_cases hzq : z ∈ tsupport q
  · rw [← coordinates_pairing _ (by simp [Space]) _ (D.frame_gram z (hqD hzq))]
    change ⟪rawVector J α ht p D a z, coordinates (fun i => D.frame i z)
      (reconstruct (coordinateMetric J α ht p z) (fun i => D.frame i z) (q z))⟫ = _
    rw [coordinates_reconstruct _ _ (D.frame_gram z (hqD hzq))]
  · have hq := image_eq_zero_of_notMem_tsupport hzq
    rw [coordinateTest_zero J α ht p D hq,MetricForms.pairing_zero_right,hq,inner_zero_right]

variable [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (hs : IsSmooth α)
include hs in
lemma pairing_manifoldTest_integral {a : TwoForm X} (ha : IsSmooth a)
    {q : Space → HodgeNormalSymbol.W}
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain) :
    (∫ x, GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q) x ∂geometricVolume A J α) =
    ∫ z, chartDensity J α p z *
      ⟪rawVector J α ht p D a z,q z⟫ := by
  let f := GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q)
  have hfc : Continuous f := (GeometricAdjoint.pairing_two_smooth J α hs ht ha
    (manifoldTest_smooth J α hs ht p D hq hc hqD)).continuous
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have hfK : tsupport f ⊆ (extChartAt Model p).symm '' tsupport q := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    apply hx
    change MetricForms.pairing (E := Space) (GeometricAdjoint.pointMetric J α ht x) (a x)
      (manifoldTest J α ht p D q x) = 0
    rw [manifoldTest_zero_off J α ht p D q hn]
    exact MetricForms.pairing_zero_right (E := Space) _ _
  have hfsource : tsupport f ⊆ (extChartAt Model p).source := by
    rintro x hx
    obtain ⟨z,hz,rfl⟩ := hfK hx
    exact (extChartAt Model p).map_target (D.domain_subset (hqD hz))
  change (∫ x, f x ∂geometricVolume A J α) = _
  rw [integral_geometricVolume_coordinate A J α hs ht p f hfc hfsource,
    ← integral_indicator (isOpen_extChartAt_target p).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ (extChartAt Model p).target
  · rw [indicator_of_mem hz]
    change chartDensity J α p z * GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q)
      ((extChartAt Model p).symm z) = _
    rw [← pairing_chart J α ht p (Or.inr rfl) a (manifoldTest J α ht p D q) hz]
    rw [pullback_manifoldTest J α ht p D q hz,pairing_coordinateTest J α ht p D a hqD z]
  · rw [indicator_of_notMem hz]
    have hqz : q z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (D.domain_subset (hqD h)))
    simp only [hqz,inner_zero_right,mul_zero]

end TamingCompatibility.HodgeChart

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open TemperedDistribution
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma product_embed_schwartz {n : ℕ} (ρ : 𝓢(E,ℝ)) (q : 𝓢(E,R n)) :
    SchwartzMap.smulLeftCLM (C n) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
      (SchwartzMap.postcompCLM (embed n) q) =
    SchwartzMap.postcompCLM (embed n) (SchwartzMap.smulLeftCLM (R n) ρ q) := by
  ext z i
  simp only [SchwartzMap.smulLeftCLM_apply (SchwartzMap.postcompCLM Complex.ofRealCLM ρ).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply ρ.hasTemperateGrowth,SchwartzMap.postcompCLM_apply,embed_apply,
    PiLp.smul_apply,Complex.ofRealCLM_apply,smul_eq_mul,Complex.ofReal_mul]
end TamingCompatibility.ComplexMatrix

namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

omit [T2Space X] in
lemma hodge_smooth_pair (f v : PreL2 A J α hs ht true) :
    ⟪hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht f),
      hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht v)⟫ =
    ∫ x, GeometricAdjoint.pairing J α ht f.val v.val x ∂geometricVolume A J α := by
  change ⟪smoothL2 A J α hs ht true f,smoothL2 A J α hs ht true v⟫ = _
  rw [(smoothL2 A J α hs ht true).inner_map_map,preL2_inner]
  rfl

lemma hodge_rhs_component_test (p : A.centers) (f : PreL2 A J α hs ht true)
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (g : 𝓢(Space,HodgeNormalSymbol.W))
    (hg : ∀ z ∈ U, g z = chartDensity J α p.val z • rawVector J α ht p.val (D p).toData f.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 6) :
    (⟪hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht f),hodgeInclusion A J α hs ht
      (hodgeSmooth A J α hs ht (hodgeTest A J α hs ht D p (componentTest j φ)
        (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) =
    ((SchwartzMap.postcompCLM (embed 6) g : 𝓢'(Space,C 6))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j := by
  rw [hodge_smooth_pair,embedded_component_apply]
  congr 1
  change (∫ x, GeometricAdjoint.pairing J α ht f.val
    (manifoldTest J α ht p.val (D p).toData (componentTest j φ)) x ∂geometricVolume A J α) = _
  rw [pairing_manifoldTest_integral J α ht p.val (D p).toData A hs f.property
    ((componentTest j φ).smooth ⊤) (full_componentTest_compact j φ hc)
    ((full_componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport φ
  · rw [hg z (hφU hz),real_inner_smul_left]
  · have hφz := image_eq_zero_of_notMem_tsupport hz
    simp [componentTest_apply,hφz]

lemma hodge_raw_weighted_pair (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 6) (u : hodgeEnergy A J α hs ht) :
    ((smulLeftCLM (C 6) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
      (hodgeRawDistribution A J α hs ht D hD p τ u))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
    (⟪hodgeInclusion A J α hs ht u,hodgeInclusion A J α hs ht
      (hodgeSmooth A J α hs ht (hodgeTest A J α hs ht D p (componentTest j φ)
        (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  let v := hodgeTest A J α hs ht D p (componentTest j φ)
    (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD))
  let P := smulLeftCLM (C 6) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
  have hLc : Continuous (fun w => (P (hodgeRawDistribution A J α hs ht D hD p τ w)
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j) :=
    continuous_system_eval (hodgeRawDistribution A J α hs ht D hD p τ) P _ j
  have hRc : Continuous (fun w => (⟪hodgeInclusion A J α hs ht w,
      hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht v)⟫ : ℂ)) :=
    Complex.continuous_ofReal.comp ((hodgeInclusion A J α hs ht).continuous.inner continuous_const)
  refine (hodgeSmooth_dense A J α hs ht).induction_on u (isClosed_eq hLc hRc) ?_
  intro f
  change (P (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))
    (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j = _
  rw [hodgeRawDistribution_smooth]
  dsimp only [P]
  rw [product_schwartz,product_embed_schwartz]
  symm
  apply hodge_rhs_component_test A J α hs ht D p f hUD _ ?_ φ hc hφU j
  intro z hz
  rw [SchwartzMap.smulLeftCLM_apply ρ.hasTemperateGrowth]
  change ρ z • (SchwartzMap.smulLeftCLM HodgeNormalSymbol.W τ
    (realVectorSchwartz A J α ht (fun q => (D q).toData) hD p (⟨f.val,f.property⟩ : smoothForms X 2))) z = _
  rw [hρ z hz]
  congr 1
  exact cutoff_realVector_raw A J α ht (fun q => (D q).toData) hD p f τ (hUD hz) (hτ z hz)
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
