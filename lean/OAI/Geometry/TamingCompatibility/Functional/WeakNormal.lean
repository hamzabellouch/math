import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.WeakNormalEquation
import OAI.Geometry.TamingCompatibility.Charts.RealTestLocality

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma smooth_energy_pair (f v : antiPre A J α hs ht) :
    ⟪smoothL2 A J α hs ht true f.val,
      energyInclusion A J α hs ht (antiToEnergy A J α hs ht v)⟫ =
    ∫ x, GeometricAdjoint.pairing J α ht f.val.val v.val.val x ∂geometricVolume A J α := by
  change ⟪smoothL2 A J α hs ht true f.val,smoothL2 A J α hs ht true v.val⟫ = _
  rw [(smoothL2 A J α hs ht true).inner_map_map,preL2_inner]
  rfl

lemma rhs_component_test (p : A.centers) (f : antiPre A J α hs ht)
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (g : 𝓢(Space,EuclideanEnergy.Pair))
    (hg : ∀ z ∈ U, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) :
    (⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) =
    ((SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j := by
  rw [smooth_energy_pair,embedded_component_apply]
  congr 1
  change (∫ x, GeometricAdjoint.pairing J α ht f.val.val
    (manifoldTest J α ht p.val (D p) (componentTest j φ)) x ∂geometricVolume A J α) = _
  rw [pairing_manifoldTest_integral J α ht p.val (D p) A hs f.val.property f.property
    ((componentTest j φ).smooth ⊤) (componentTest_compact j φ hc)
    ((componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport φ
  · rw [hg z (hφU hz),real_inner_smul_left]
    rw [componentTest_inner]
    fin_cases j <;> simp [componentTest_apply,rawPair,EuclideanEnergy.pair] <;> ring
  · have hφz := image_eq_zero_of_notMem_tsupport hz
    simp [componentTest_apply,hφz]

lemma raw_square_source (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
    (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p) i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p) z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫)
    (g : 𝓢(Space,EuclideanEnergy.Pair))
    (hg : ∀ z ∈ U, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z)
    (χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) (hχU : tsupport χ ⊆ U) :
    smulLeftCLM (C 2) χ (ComplexMatrix.square EuclideanEnergy.e a b ρ
      (rawDistribution A J α hs ht D hD p τ u)) =
    smulLeftCLM (C 2) χ (SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2)) := by
  apply localize_eq_of_real_tests _ χ hc hχU
  intro φ hφ hφU
  ext j
  rw [raw_square_energy A J α hs ht D hD p τ hU hUD hτ a b ρ ha hb hρ φ hφ hφU j u,heq]
  exact rhs_component_test A J α hs ht D p f hUD g hg φ hφ hφU j

end TamingCompatibility.GeometricHilbert

end

end OAI
