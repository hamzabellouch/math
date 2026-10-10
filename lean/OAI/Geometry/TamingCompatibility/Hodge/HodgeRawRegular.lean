import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeResolvent

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

lemma hodge_resolvent_raw_gain (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) (r : ℝ) (hr : 0 < r) :
    ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ (n : ℕ) (f : hodgeEnergy A J α hs ht),
      MemSobolevLoc U n (hodgeRawDistribution A J α hs ht D hD p τ f) →
      MemSobolevLoc V ((n:ℝ)+2) (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht f))) := by
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
  let ζ := ((r^2)⁻¹:ℂ) • SchwartzMap.postcompCLM Complex.ofRealCLM ρ
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
  refine ⟨V,hV,hqV,hVW.trans hWU,fun n f hf => ?_⟩
  apply hall n _
    (memSobolevLoc_one_of_global (hodgeRawDistribution_H1 A J α hs ht D hD p τ _) W)
  intro χ hc hχW
  rw [hodge_resolvent_distribution A J α hs ht D hD p τ hW (hWU.trans hUD)
    (fun z hz => hτ z (hWU hz)) a b ρ ha hb hρ r hr f χ hc hχW]
  rw [map_smul,coefficient_products_commute]
  exact MemSobolev.smul _ (EuclideanSobolevOperators.memSobolev_nat_product n _
    (hf χ hc (hχW.trans hWU)))
end TamingCompatibility.GeometricHilbert

end
end

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

def hodgeRegularizedGraph (r : ℝ) (hr : 0 < r) :
    L2 A J α hs ht true →L[ℝ] hodgeEnergy A J α hs ht :=
  (hodgeWeakSolution A J α hs ht r hr).comp (hodgeResolvent A J α hs ht r ^ 2)

omit [T2Space X] in
lemma hodgeRegularizedGraph_inclusion (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    hodgeInclusion A J α hs ht (hodgeRegularizedGraph A J α hs ht r hr f) =
      hodgeRegularization A J α hs ht r f := by
  change hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr
    (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f))) = _
  rw [← ContinuousLinearMap.comp_apply,← hodgeResolvent_eq A J α hs ht r hr]
  rfl

lemma hodgeRegularization_raw_H5 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ τ : 𝓢(Space,ℝ), ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ (D p).domain ∧
      (∀ z ∈ V, τ z * coordinateWeight A p z = 1) ∧
      ∀ f : L2 A J α hs ht true, MemSobolevLoc V 5
        (hodgeRawDistribution A J α hs ht D hD p τ
          (hodgeRegularizedGraph A J α hs ht r hr f)) := by
  obtain ⟨τ,-,-,U,hU,hqU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hq hwq
  obtain ⟨W,hW,hqW,hWU,hWgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
    hU hUD hτ q hqU r hr
  obtain ⟨V,hV,hqV,hVW,hVgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
    hW (hWU.trans hUD) (fun z hz => hτ z (hWU hz)) q hqW r hr
  refine ⟨τ,V,hV,hqV,hVW.trans (hWU.trans hUD),fun z hz => hτ z (hWU (hVW hz)),?_⟩
  intro f
  let u₁ := hodgeWeakSolution A J α hs ht r hr f
  let u₂ := hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht u₁)
  have h₁ : MemSobolevLoc U (1:ℝ) (hodgeRawDistribution A J α hs ht D hD p τ u₁) :=
    memSobolevLoc_one_of_global (hodgeRawDistribution_H1 A J α hs ht D hD p τ u₁) U
  have h₂ : MemSobolevLoc W (3:ℝ) (hodgeRawDistribution A J α hs ht D hD p τ u₂) := by
    simpa only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num] using hWgain 1 u₁ (by simpa only [Nat.cast_one] using h₁)
  have h₃ := hVgain 3 u₂ (by simpa only [Nat.cast_ofNat] using h₂)
  have he₁ : hodgeInclusion A J α hs ht u₁ = hodgeResolvent A J α hs ht r f := by
    exact congrArg (fun L => L f) (hodgeResolvent_eq A J α hs ht r hr).symm
  have he₂ : hodgeInclusion A J α hs ht u₂ =
      hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f) := by
    change hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr _) = _
    rw [← ContinuousLinearMap.comp_apply,← hodgeResolvent_eq A J α hs ht r hr,he₁]
  rw [he₂] at h₃
  change MemSobolevLoc V 5 (hodgeRawDistribution A J α hs ht D hD p τ
    (hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f))))
  simpa only [Nat.cast_ofNat,show (3:ℝ)+2=5 by norm_num] using h₃
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
