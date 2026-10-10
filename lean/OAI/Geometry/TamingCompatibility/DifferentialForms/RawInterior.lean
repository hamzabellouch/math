import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.MetricSquareRegularity
import OAI.Geometry.TamingCompatibility.Charts.InverseCutoff
import OAI.Geometry.TamingCompatibility.Functional.WeakNormal

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma raw_interior_regular (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U)
    (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) :
    ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧ ∀ n : ℕ,
      MemSobolevLoc V n (rawDistribution A J α hs ht D hD p τ u) := by
  obtain ⟨φ,hφ,hφU,W,hW,hqW,hWU,hφone⟩ := SchwartzCutoff.exists_one_near hU hq
  have hφD := hφU.trans hUD
  let a := patchA J α ht p.val (D p) (φ.smooth ⊤) hφ hφD
  let b := patchB J α hs ht p.val (D p) (φ.smooth ⊤) hφ hφD
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset) (φ.smooth ⊤) hφ hφD
  have ha : ∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p) i z := by
    intro z hz i
    simp only [a,patchA,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hb : ∀ z ∈ W, b z = normalB J α ht p.val (D p) z := by
    intro z hz
    simp only [b,patchB,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hρ : ∀ z ∈ W, ρ z = chartDensity J α p.val z := by
    intro z hz
    simp only [ρ,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  let g : 𝓢(Space,EuclideanEnergy.Pair) := SchwartzCutoff.schwartz (D p).domain_open
    (((contDiffOn_const (c := (2 : ℝ))).mul ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset)).smul
      (rawPair_smooth J α ht p.val (D p) f.val.property)) (φ.smooth ⊤) hφ hφD
  have hg : ∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z := by
    intro z hz
    simp only [g,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
    rfl
  have hf (n : ℕ) : MemSobolevLoc W n (square EuclideanEnergy.e a b ρ
      (rawDistribution A J α hs ht D hD p τ u)) := by
    intro χ hc hχW
    rw [raw_square_source A J α hs ht D hD p τ hW (hWU.trans hUD)
      (fun z hz => hτ z (hWU hz)) a b ρ ha hb hρ f u heq g hg χ hc hχW]
    exact schwartz_memSobolevLoc (SchwartzMap.postcompCLM (embed 2) g) n W χ hc hχW
  let G := fun i j z => ρ z*φ z*φ z*GeometricChart.normalMetric J α ht p.val (D p) i j z
  have hG : ∀ i j, G i j q = chartDensity J α p.val q * ∑ t, (D p).frame t q i * (D p).frame t q j := by
    intro i j
    simp only [G,hρ q hqW,hφone q hqW,one_mul,GeometricChart.normalMetric,
      LocalMatrixOperator.frameCovector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      star_trivial,mul_comm]
  obtain ⟨V,hV,hqV,hVW,hall⟩ := metric_square_regular hW q hqW
    (coordinateMetric J α ht p.val q) (fun i => (D p).frame i q)
    ((D p).frame_gram q (hUD hq)) a b ρ G
    (patchA_polarized J α ht p.val (D p) (φ.smooth ⊤) hφ hφD ρ)
    (chartDensity J α p.val q) (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hq))) hG
    (memSobolevLoc_one_of_global (rawDistribution_H1 A J α hs ht D hD p τ u) W) hf
  exact ⟨V,hV,hqV,hVW.trans hWU,hall⟩

end TamingCompatibility.GeometricHilbert

end

end OAI
