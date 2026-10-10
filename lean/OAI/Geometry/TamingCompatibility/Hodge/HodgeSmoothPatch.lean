import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeTestPairing

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X)
  (D : GeometricChart.Data J α ht p)
lemma rawVector_fun_smul (ρ : X → ℝ) (a : TwoForm X) (z : Space) :
    rawVector J α ht p D (fun x => ρ x • a x) z =
      ρ ((extChartAt Model p).symm z) • rawVector J α ht p D a z := by
  ext j
  rfl

lemma manifoldTest_eq (b : TwoForm X) (q : Space → HodgeNormalSymbol.W)
    (hqD : tsupport q ⊆ D.domain)
    (hraw : ∀ z ∈ D.domain, q z = rawVector J α ht p D b z)
    (hbzero : ∀ x ∉ (extChartAt Model p).symm '' D.domain, b x = 0) :
    manifoldTest J α ht p D q = b := by
  funext x
  by_cases hx : x ∈ (extChartAt Model p).symm '' D.domain
  · obtain ⟨z,hz,rfl⟩ := hx
    apply form_eq_of_chart_pullback p _ _ ((extChartAt Model p).map_target (D.domain_subset hz))
    rw [(extChartAt Model p).right_inv (D.domain_subset hz)]
    change ManifoldForms.pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm z =
      ManifoldForms.pullback b (extChartAt Model p).symm z
    rw [pullback_manifoldTest J α ht p D q (D.domain_subset hz)]
    exact (congrArg (HodgeFrame.reconstruct (coordinateMetric J α ht p z)
      (fun i => D.frame i z)) (hraw z hz)).trans (rawVector_expansion J α ht p D b hz)
  · rw [hbzero x hx,manifoldTest_zero_off J α ht p D q]
    exact fun h => hx ((image_mono hqD) h)
end TamingCompatibility.HodgeChart
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)

def hodgeMultiply (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (a : PreL2 A J α hs ht true) : PreL2 A J α hs ht true :=
  ⟨fun x => ρ x • a.val x,a.property.fun_smul hρ⟩

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma hodge_exists_patch (p : A.centers) {U : Set Space} (hU : IsOpen U)
    (hUD : U ⊆ (D p).domain) {z : Space} (hz : z ∈ U)
    (g : Space →ᵇ C 6) (hg : ContDiff ℝ ∞ (g : Space → C 6)) :
    ∃ W : Set Space, IsOpen W ∧ z ∈ W ∧ W ⊆ U ∧ ∃ w : PreL2 A J α hs ht true,
      ∀ y ∈ W, rawVector J α ht p.val (D p).toData w.val y = retract 6 (g y) := by
  obtain ⟨η,hc,hηU,W,hW,hzW,hWU,hη⟩ := SchwartzCutoff.exists_one_near hU hz
  let q : Space → HodgeNormalSymbol.W := fun y => η y • retract 6 (g y)
  have hq : ContDiff ℝ ∞ q := (η.smooth ⊤).smul ((retract 6).contDiff.comp hg)
  have hqs : tsupport q ⊆ tsupport η := tsupport_smul_subset_left _ _
  have hqc : HasCompactSupport q := hc.of_isClosed_subset (isClosed_tsupport q) hqs
  let ψ := hqc.toSchwartzMap hq
  let w := hodgeTest A J α hs ht D p ψ hqc (hqs.trans (hηU.trans hUD))
  refine ⟨W,hW,hzW,hWU,w,fun y hy => ?_⟩
  change rawVector J α ht p.val (D p).toData (manifoldTest J α ht p.val (D p).toData q) y = _
  rw [rawVector_manifoldTest J α ht p.val (D p).toData q (hUD (hWU hy))]
  change η y • retract 6 (g y) = _
  rw [hη y hy,one_smul]

omit [MeasurableSpace X] [BorelSpace X] in
lemma hodge_supported_test (p : A.centers) {U : Set Space} (hU : IsOpen U)
    (hUD : U ⊆ (D p).domain) (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (hρU : ∀ x ∈ tsupport ρ, x ∈ (extChartAt Model p.val).source ∧ extChartAt Model p.val x ∈ U)
    (a : PreL2 A J α hs ht true) :
    ∃ q : 𝓢(Space,HodgeNormalSymbol.W), ∃ hc : HasCompactSupport (q : Space → HodgeNormalSymbol.W),
      ∃ hqU : tsupport q ⊆ U,
        hodgeTest A J α hs ht D p q hc (hqU.trans hUD) = hodgeMultiply A J α hs ht ρ hρ a := by
  let K := (extChartAt Model p.val) '' tsupport ρ
  have hK : IsCompact K := (isClosed_tsupport ρ).isCompact.image_of_continuousOn
    ((continuousOn_extChartAt p.val).mono (fun x hx => (hρU x hx).1))
  have hKU : K ⊆ U := by rintro _ ⟨x,hx,rfl⟩; exact (hρU x hx).2
  obtain ⟨η,hηc,hηU,hηone⟩ := SchwartzCutoff.exists_one_on_compact hK hU hKU
  let b := hodgeMultiply A J α hs ht ρ hρ a
  let q := SchwartzCutoff.schwartz (D p).domain_open (rawVector_smooth J α ht p.val (D p).toData b.property)
    (η.smooth ⊤) hηc (hηU.trans hUD)
  have hqc : HasCompactSupport (q : Space → HodgeNormalSymbol.W) := SchwartzCutoff.compact hηc
  have hqU : tsupport q ⊆ U := (tsupport_smul_subset_left _ _).trans hηU
  refine ⟨q,hqc,hqU,?_⟩
  apply Subtype.ext
  change manifoldTest J α ht p.val (D p).toData q = b.val
  apply manifoldTest_eq J α ht p.val (D p).toData b.val q (hqU.trans hUD)
  · intro z hz
    change η z • rawVector J α ht p.val (D p).toData (fun x => ρ x • a.val x) z =
      rawVector J α ht p.val (D p).toData (fun x => ρ x • a.val x) z
    rw [rawVector_fun_smul]
    by_cases hr : ρ ((extChartAt Model p.val).symm z) = 0
    · simp only [hr,zero_smul,smul_zero]
    · rw [hηone z ⟨(extChartAt Model p.val).symm z,subset_closure hr,
        (extChartAt Model p.val).right_inv ((D p).domain_subset hz)⟩,one_smul]
  · intro x hx
    change ρ x • a.val x = 0
    have hz : ρ x = 0 := by
      by_contra hn
      have hh := hρU x (subset_closure hn)
      exact hx ⟨extChartAt Model p.val x,hUD hh.2,(extChartAt Model p.val).left_inv hh.1⟩
    rw [hz,zero_smul]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open ComplexMatrix Set Filter MeasureTheory TemperedDistribution
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodge_local_pairing_eq (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * GeometricChart.coordinateWeight A p z = 1)
    (u : hodgeEnergy A J α hs ht) (g : Space →ᵇ C 6)
    (hg : ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ U →
      hodgeRawDistribution A J α hs ht D hD p τ u χ = EuclideanSobolev.boundedDistribution g χ)
    (w : PreL2 A J α hs ht true)
    (hw : ∀ z ∈ U, rawVector J α ht p.val (D p).toData w.val z = retract 6 (g z))
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 6) :
    ⟪hodgeInclusion A J α hs ht u,smoothL2 A J α hs ht true
      (hodgeTest A J α hs ht D p (componentTest j φ)
        (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD)))⟫ =
    ⟪smoothL2 A J α hs ht true w,smoothL2 A J α hs ht true
      (hodgeTest A J α hs ht D p (componentTest j φ)
        (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD)))⟫ := by
  obtain ⟨η,hηc,hηU,hηone⟩ := SchwartzCutoff.exists_one_on_compact hc hU hφU
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset)
    (η.smooth ⊤) hηc (hηU.trans hUD)
  have hρ : ∀ z ∈ tsupport φ, ρ z = chartDensity J α p.val z := by
    intro z hz
    change η z * chartDensity J α p.val z = _
    rw [hηone z hz,one_mul]
  let θ := SchwartzMap.smulLeftCLM ℝ ρ φ
  let ψ := SchwartzMap.postcompCLM Complex.ofRealCLM θ
  have hθ : tsupport θ ⊆ tsupport φ := (SchwartzMap.tsupport_smulLeftCLM_subset ρ φ).trans inter_subset_left
  have hψ : tsupport ψ ⊆ tsupport θ := tsupport_comp_subset (map_zero Complex.ofRealCLM) θ
  have he := hg ψ (hc.of_isClosed_subset (isClosed_tsupport ψ) (hψ.trans hθ))
    (hψ.trans (hθ.trans hφU))
  have hp := hodge_raw_weighted_pair A J α hs ht D hD p τ ρ (hφU.trans hUD)
    (fun z hz => hτ z (hφU hz)) hρ φ hc Subset.rfl j u
  have hψeq : SchwartzMap.smulLeftCLM ℂ (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ) = ψ := by
    ext z
    simp only [SchwartzMap.smulLeftCLM_apply (SchwartzMap.postcompCLM Complex.ofRealCLM ρ).hasTemperateGrowth,
      SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,smul_eq_mul,ψ,θ,
      SchwartzMap.smulLeftCLM_apply ρ.hasTemperateGrowth,Complex.ofReal_mul]
  rw [smulLeftCLM_apply_apply,hψeq,he] at hp
  have hr := congrArg Complex.re hp
  rw [bounded_real_component,Complex.ofReal_re] at hr
  rw [hodgeInclusion_smooth] at hr
  rw [← hr,(smoothL2 A J α hs ht true).inner_map_map,preL2_inner]
  change _ = ∫ x, GeometricAdjoint.pairing J α ht w.val
    (manifoldTest J α ht p.val (D p).toData (componentTest j φ)) x ∂geometricVolume A J α
  rw [pairing_manifoldTest_integral J α ht p.val (D p).toData A hs w.property
    ((componentTest j φ).smooth ⊤) (full_componentTest_compact j φ hc)
    ((full_componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [θ,SchwartzMap.smulLeftCLM_apply ρ.hasTemperateGrowth,smul_eq_mul]
  rw [componentTest_inner]
  by_cases hz : z ∈ tsupport φ
  · rw [hρ z hz,hw z (hφU hz),retract_apply]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hz]
    ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
