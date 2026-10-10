import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.WeightedRawPairing

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma local_pairing_eq (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (u : antiEnergy A J α hs ht) (g : Space →ᵇ C 2)
    (hg : ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ U →
      rawDistribution A J α hs ht D hD p τ u χ = EuclideanSobolev.boundedDistribution g χ)
    (w : antiPre A J α hs ht) (hw : ∀ z ∈ U,
      rawPair J α ht p.val (D p) w.val.val z = retract 2 (g z))
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) :
    ⟪energyInclusion A J α hs ht u,energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ =
    ⟪smoothL2 A J α hs ht true w.val,energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ := by
  let θ := densityTest A J α hs ht D p φ hc (hφU.trans hUD)
  let ψ := SchwartzMap.postcompCLM Complex.ofRealCLM θ
  have hθ : tsupport θ ⊆ tsupport φ := densityTest_support A J α hs ht D p φ hc (hφU.trans hUD)
  have hψ : tsupport ψ ⊆ tsupport θ := tsupport_comp_subset (map_zero Complex.ofRealCLM) θ
  have he := hg ψ (hc.of_isClosed_subset (isClosed_tsupport ψ) (hψ.trans hθ))
    (hψ.trans (hθ.trans hφU))
  have hp := raw_component_pair A J α hs ht D hD p τ hUD hτ φ hc hφU j u
  change (rawDistribution A J α hs ht D hD p τ u ψ) j = _ at hp
  rw [he] at hp
  have hr := congrArg Complex.re hp
  rw [bounded_real_component,Complex.ofReal_re] at hr
  rw [← hr,smooth_energy_pair]
  change _ = ∫ x, GeometricAdjoint.pairing J α ht w.val.val
    (manifoldTest J α ht p.val (D p) (componentTest j φ)) x ∂geometricVolume A J α
  rw [pairing_manifoldTest_integral J α ht p.val (D p) A hs w.val.property w.property
    ((componentTest j φ).smooth ⊤) (componentTest_compact j φ hc)
    ((componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  change (φ z * (2*chartDensity J α p.val z)) * (g z j).re = _
  by_cases hz : z ∈ tsupport φ
  · have hzraw := congrArg (fun v : EuclideanEnergy.Pair => v j) (hw z (hφU hz))
    rw [← retract_apply 2 (g z) j,← hzraw]
    fin_cases j <;> simp [rawPair,EuclideanEnergy.pair,componentTest_apply] <;> ring
  · simp [image_eq_zero_of_notMem_tsupport hz,componentTest_apply]

end TamingCompatibility.GeometricHilbert

end

end OAI
