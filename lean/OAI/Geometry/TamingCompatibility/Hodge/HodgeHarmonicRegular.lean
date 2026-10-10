import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgePairAllTests

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodge_harmonic_raw_all_orders (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) (u : hodgeEnergy A J α hs ht)
    (hu : hodgeWeakDerivative A J α hs ht u = 0) :
    ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ n : ℕ, MemSobolevLoc V n (hodgeRawDistribution A J α hs ht D hD p τ u) := by
  obtain ⟨φ,hφ,hφU,W,hW,hqW,hWU,hφone⟩ := SchwartzCutoff.exists_one_near hU hq
  have hφD := hφU.trans hUD
  let a := patchA J α ht p.val (D p).toData (φ.smooth ⊤) hφ hφD
  let b := patchB J α hs ht p.val (D p).toData (φ.smooth ⊤) hφ hφD
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset) (φ.smooth ⊤) hφ hφD
  have ha : ∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p).toData i z := by
    intro z hz i
    simp only [a,patchA,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hb : ∀ z ∈ W, b z = normalB J α ht p.val (D p).toData z := by
    intro z hz
    simp only [b,patchB,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hρ : ∀ z ∈ W, ρ z = chartDensity J α p.val z := by
    intro z hz
    simp only [ρ,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  let ζ : 𝓢(Space,ℂ) := 0
  let G := fun i j z => ρ z*φ z*φ z*GeometricChart.normalMetric J α ht p.val (D p).toData i j z
  have hG : ∀ i j, G i j q = chartDensity J α p.val q * ∑ t, (D p).frame t q i * (D p).frame t q j := by
    intro i j
    simp only [G,hρ q hqW,hφone q hqW,one_mul,GeometricChart.normalMetric,
      LocalMatrixOperator.frameCovector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      star_trivial,mul_comm]
  obtain ⟨V,hV,hqV,hVW,hall⟩ := full_shifted_square_uniform_regular hW q hqW
    (coordinateMetric J α ht p.val q) (fun i => (D p).frame i q)
    ((D p).frame_gram q (hUD hq)) a b ρ ζ G
    (patchA_polarized J α ht p.val (D p).toData (φ.smooth ⊤) hφ hφD ρ)
    (chartDensity J α p.val q) (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hq))) hG
  refine ⟨V,hV,hqV,hVW.trans hWU,fun n => ?_⟩
  apply (hall n _
    (memSobolevLoc_one_of_global (hodgeRawDistribution_H1 A J α hs ht D hD p τ u) W) ?_).mono
    (by simp)
  intro χ hc hχW
  have hz : smulLeftCLM (C 6) χ (fullShiftedSquare a b ρ ζ
      (hodgeRawDistribution A J α hs ht D hD p τ u)) = 0 := by
    rw [← map_zero (smulLeftCLM (C 6) χ)]
    apply localize_eq_of_real_tests _ χ hc hχW
    intro ψ hψ hψW
    ext j
    change (ComplexMatrix.square EuclideanEnergy.e a b ρ
      (hodgeRawDistribution A J α hs ht D hD p τ u)
      (SchwartzMap.postcompCLM Complex.ofRealCLM ψ)) j +
      (smulLeftCLM (C 6) 0 (hodgeRawDistribution A J α hs ht D hD p τ u)
        (SchwartzMap.postcompCLM Complex.ofRealCLM ψ)) j = 0
    rw [hodge_raw_square_energy A J α hs ht D hD p τ hW (hWU.trans hUD)
      (fun z hz => hτ z (hWU hz)) a b ρ ha hb hρ ψ hψ hψW j u,hu,inner_zero_left]
    have ht0 : SchwartzMap.smulLeftCLM ℂ (0 : 𝓢(Space,ℂ))
        (SchwartzMap.postcompCLM Complex.ofRealCLM ψ) = 0 := by
      ext z
      rw [SchwartzMap.smulLeftCLM_apply (0 : 𝓢(Space,ℂ)).hasTemperateGrowth]
      exact zero_smul _ _
    simp only [Complex.ofReal_zero,zero_add,TemperedDistribution.smulLeftCLM_apply_apply]
    change ((hodgeRawDistribution A J α hs ht D hD p τ u)
      (SchwartzMap.smulLeftCLM ℂ (0 : 𝓢(Space,ℂ))
        (SchwartzMap.postcompCLM Complex.ofRealCLM ψ))) j = 0
    rw [ht0,map_zero]
    rfl
  rw [hz]
  simpa only [map_zero] using (0 : 𝓢(Space,C 6)).memSobolev (s := (n:ℝ)) (p := 2)
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set HilbertSobolev ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodge_harmonic_local_smooth (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) (u : hodgeEnergy A J α hs ht)
    (hu : hodgeWeakDerivative A J α hs ht u = 0) :
    ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧ ∃ g : Space →ᵇ C 6,
      ContDiff ℝ ∞ (g : Space → C 6) ∧ ∀ χ : 𝓢(Space,ℂ),
        HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
        smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ u) =
          smulLeftCLM (C 6) χ (EuclideanSobolev.boundedDistribution g) := by
  obtain ⟨W,hW,hqW,hWU,hall⟩ :=
    hodge_harmonic_raw_all_orders A J α hs ht D hD p τ hU hUD hτ q hq u hu
  obtain ⟨V,hV,hqV,hVW,g,hg,he⟩ := exists_local_smooth_representative hW hqW hall
  exact ⟨V,hV,hqV,hVW.trans hWU,g,hg,he⟩
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open HilbertSobolev
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in
lemma hodge_harmonic_weak_patch (u : hodgeEnergy A J α hs ht)
    (hu : hodgeWeakDerivative A J α hs ht u = 0) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ w : PreL2 A J α hs ht true,
      ∀ (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ), tsupport ρ ⊆ V →
        ∀ a : PreL2 A J α hs ht true,
          ⟪hodgeInclusion A J α hs ht u,smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ a)⟫ =
          ⟪smoothL2 A J α hs ht true w,smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ a)⟫ := by
  obtain ⟨p,hp,hxp⟩ := exists_nonzero_weight_chart A J α ht (fun p => (D p).toData) hD x
  have hxs : x ∈ (extChartAt Model p.val).source := (A.subordinate p) (subset_closure hp)
  have hw : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxs] using hp
  obtain ⟨τ,-,-,U,hU,hxU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hxp hw
  obtain ⟨V,hV,hxV,hVU,g,hgs,hgd⟩ := hodge_harmonic_local_smooth A J α hs ht D hD p τ
    hU hUD hτ (extChartAt Model p.val x) hxU u hu
  obtain ⟨W,hW,hxW,hWV,w,hw⟩ := hodge_exists_patch A J α hs ht D p hV (hVU.trans hUD) hxV g hgs
  let Z := (extChartAt Model p.val).source ∩ (extChartAt Model p.val) ⁻¹' W
  have hZ : IsOpen Z := (continuousOn_extChartAt p.val).isOpen_inter_preimage (isOpen_extChartAt_source p.val) hW
  refine ⟨Z,hZ,⟨hxs,hxW⟩,w,fun ρ hρ hρZ a => ?_⟩
  obtain ⟨q,hqc,hqW,hq⟩ := hodge_supported_test A J α hs ht D p hW
    (hWV.trans (hVU.trans hUD)) ρ hρ hρZ a
  rw [← hq]
  refine hodge_pair_all_tests_eq A J α hs ht D p (hWV.trans (hVU.trans hUD)) _ _ ?_ q hqc hqW
  intro φ hc hφW k
  exact hodge_local_pairing_eq A J α hs ht D hD p τ hW (hWV.trans (hVU.trans hUD))
    (fun z hz => hτ z (hVU (hWV hz))) _ g
    (fun χ hc hχ => tests_eq_of_localize hV hgd χ hc (hχ.trans hWV)) w hw φ hc hφW k
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
