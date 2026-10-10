import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.BoundedDistribution
import OAI.Geometry.TamingCompatibility.Functional.NormalPatch
import OAI.Geometry.TamingCompatibility.Functional.WeakNormal

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def densityTest (p : A.centers) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) (hφD : tsupport φ ⊆ (D p).domain) : 𝓢(Space,ℝ) :=
  SchwartzCutoff.schwartz (D p).domain_open
    ((contDiffOn_const (c := (2:ℝ))).mul ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset))
    (φ.smooth ⊤) hc hφD

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma densityTest_apply (p : A.centers) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) (hφD : tsupport φ ⊆ (D p).domain) (z : Space) :
    densityTest A J α hs ht D p φ hc hφD z = φ z * (2*chartDensity J α p.val z) := rfl

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma densityTest_support (p : A.centers) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) (hφD : tsupport φ ⊆ (D p).domain) :
    tsupport (densityTest A J α hs ht D p φ hc hφD) ⊆ tsupport φ :=
  tsupport_smul_subset_left _ _

lemma smooth_raw_component_pair (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) (w : antiPre A J α hs ht) :
    (rawDistribution A J α hs ht D hD p τ (antiToEnergy A J α hs ht w)
      (SchwartzMap.postcompCLM Complex.ofRealCLM (densityTest A J α hs ht D p φ hc (hφU.trans hUD)))) j =
    (⟪energyInclusion A J α hs ht (antiToEnergy A J α hs ht w),energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  rw [rawDistribution_smooth,embedded_component_apply]
  change _ = (⟪smoothL2 A J α hs ht true w.val,energyInclusion A J α hs ht
    (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
      (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ)
  rw [smooth_energy_pair]
  congr 1
  change _ = ∫ x, GeometricAdjoint.pairing J α ht w.val.val
    (manifoldTest J α ht p.val (D p) (componentTest j φ)) x ∂geometricVolume A J α
  rw [pairing_manifoldTest_integral J α ht p.val (D p) A hs w.val.property w.property
    ((componentTest j φ).smooth ⊤) (componentTest_compact j φ hc)
    ((componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [componentTest_inner,densityTest_apply]
  by_cases hz : z ∈ tsupport φ
  · rw [cutoff_realPair_raw A J α ht D hD p w.val τ (hUD (hφU hz)) (hτ z (hφU hz))]
    fin_cases j <;> simp [rawPair,EuclideanEnergy.pair,componentTest_apply] <;> ring
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp [componentTest_apply,image_eq_zero_of_notMem_tsupport hz]

lemma raw_component_pair (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) (u : antiEnergy A J α hs ht) :
    (rawDistribution A J α hs ht D hD p τ u
      (SchwartzMap.postcompCLM Complex.ofRealCLM (densityTest A J α hs ht D p φ hc (hφU.trans hUD)))) j =
    (⟪energyInclusion A J α hs ht u,energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  let ψ := SchwartzMap.postcompCLM Complex.ofRealCLM (densityTest A J α hs ht D p φ hc (hφU.trans hUD))
  let v := testAnti A J α hs ht D p (componentTest j φ)
    (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))
  have hLc : Continuous (fun w => (rawDistribution A J α hs ht D hD p τ w ψ) j) := by
    generalize rawDistribution A J α hs ht D hD p τ = L
    exact (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp
      ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) (C 2) ψ).continuous.comp L.continuous)
  have hRc : Continuous (fun w => (⟪energyInclusion A J α hs ht w,
      energyInclusion A J α hs ht (antiToEnergy A J α hs ht v)⟫ : ℂ)) :=
    Complex.continuous_ofReal.comp ((energyInclusion A J α hs ht).continuous.inner continuous_const)
  exact (antiToEnergy_dense A J α hs ht).induction_on u (isClosed_eq hLc hRc)
    (fun w => smooth_raw_component_pair A J α hs ht D hD p τ hUD hτ φ hc hφU j w)

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open MeasureTheory
open scoped SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] {n : ℕ}

lemma bounded_real_component (g : D →ᵇ C n) (φ : 𝓢(D,ℝ)) (j : Fin n) :
    ((EuclideanSobolev.boundedDistribution g
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j).re =
      ∫ x, φ x * (g x j).re := by
  rw [EuclideanSobolev.boundedDistribution_apply]
  let L : C n →L[ℝ] ℝ := Complex.reCLM ∘L (EuclideanSpace.proj j).restrictScalars ℝ
  have hi : Integrable (fun x => (SchwartzMap.postcompCLM Complex.ofRealCLM φ) x • g x) :=
    (SchwartzMap.postcompCLM Complex.ofRealCLM φ).integrable.smul_of_top_left g.memLp_top
  change L (∫ x, (SchwartzMap.postcompCLM Complex.ofRealCLM φ) x • g x) = _
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [L]

end TamingCompatibility.ComplexMatrix

end
end

end
end
end

end OAI
