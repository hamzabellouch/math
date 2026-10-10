import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeLocalEvaluation
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothingKernel

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace LocalHodgeSmoothing
variable {p : A.centers} {q : Space} {r : ℝ} {hr : 0 < r}
variable (L : LocalHodgeSmoothing A J α hs ht D hD p q r hr)

omit [T2Space X] in

lemma representative_on_test (f : L2 A J α hs ht true) (ψ : 𝓢(Space,ℂ))
    (hψ : tsupport ψ ⊆ L.neighborhood) :
    boundedDistribution (L.representative f) ψ =
      hodgeRawDistribution A J α hs ht D hD p L.reciprocal
        (hodgeRegularizedGraph A J α hs ht r hr f) ψ := by
  rw [L.representative_spec]
  change hodgeRawDistribution A J α hs ht D hD p L.reciprocal
    (hodgeRegularizedGraph A J α hs ht r hr f) (SchwartzMap.smulLeftCLM ℂ L.cutoff ψ) = _
  congr 1
  ext z
  rw [SchwartzMap.smulLeftCLM_apply L.cutoff.hasTemperateGrowth]
  change L.cutoff z • ψ z = ψ z
  by_cases hz : z ∈ tsupport ψ
  · rw [L.cutoff_eq z (hψ hz),one_smul]
  · rw [image_eq_zero_of_notMem_tsupport hz,smul_zero]

def realEvaluation (z : Space) : L2 A J α hs ht true →L[ℝ] HodgeNormalSymbol.W :=
  (retract 6).comp (L.evaluation z)

omit [T2Space X] in
lemma realEvaluation_continuous : Continuous L.realEvaluation :=
  continuous_const.clm_comp L.evaluation_continuous

omit [T2Space X] in
lemma realEvaluation_apply (z : Space) (f : L2 A J α hs ht true) (j : Fin 6) :
    L.realEvaluation z f j = (L.representative f z j).re := rfl

def regularizeLocal (μ : Measure Space) (v : Space → HodgeNormalSymbol.W) :
    L2 A J α hs ht true := HilbertKernel.regularize μ L.realEvaluation v

omit [T2Space X] in
lemma regularizeLocal_pair (μ : Measure Space) (v : Space → HodgeNormalSymbol.W)
    (hv : Integrable (fun z => (L.realEvaluation z).adjoint (v z)) μ)
    (f : L2 A J α hs ht true) :
    ⟪L.regularizeLocal μ v,f⟫ = ∫ z, ⟪v z,L.realEvaluation z f⟫ ∂μ :=
  HilbertKernel.regularize_pair μ L.realEvaluation v hv f

def localKernel {p' : A.centers} {q' : Space}
    (M : LocalHodgeSmoothing A J α hs ht D hD p' q' r hr) (z w : Space) :
    HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.W :=
  HilbertKernel.kernel L.realEvaluation M.realEvaluation z w

omit [T2Space X] in
lemma localKernel_continuous {p' : A.centers} {q' : Space}
    (M : LocalHodgeSmoothing A J α hs ht D hD p' q' r hr) :
    Continuous (fun zw : Space × Space => L.localKernel M zw.1 zw.2) :=
  HilbertKernel.kernel_continuous L.realEvaluation_continuous M.realEvaluation_continuous

omit [T2Space X] in
lemma localKernel_adjoint {p' : A.centers} {q' : Space}
    (M : LocalHodgeSmoothing A J α hs ht D hD p' q' r hr) (z w : Space) :
    (L.localKernel M z w).adjoint = M.localKernel L w z :=
  HilbertKernel.kernel_adjoint L.realEvaluation M.realEvaluation z w

omit [T2Space X] in
lemma regularizeLocal_kernel_pair {p' : A.centers} {q' : Space}
    (M : LocalHodgeSmoothing A J α hs ht D hD p' q' r hr)
    (μ ν : Measure Space) (v w : Space → HodgeNormalSymbol.W)
    (hv : Integrable (fun z => (L.realEvaluation z).adjoint (v z)) μ)
    (hw : Integrable (fun z => (M.realEvaluation z).adjoint (w z)) ν) :
    ⟪L.regularizeLocal μ v,M.regularizeLocal ν w⟫ =
      ∫ z, ∫ y, ⟪v z,L.localKernel M z y (w y)⟫ ∂ν ∂μ :=
  HilbertKernel.regularize_kernel_pair μ ν L.realEvaluation M.realEvaluation v w hv hw
end LocalHodgeSmoothing
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace LocalHodgeSmoothing
variable {p : A.centers} {q : Space} {r : ℝ} {hr : 0 < r}
variable (L : LocalHodgeSmoothing A J α hs ht D hD p q r hr)

lemma realEvaluation_pair (f : L2 A J α hs ht true)
    (ρ : 𝓢(Space,ℝ)) {U : Set Space} (hUL : U ⊆ L.neighborhood)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 6) :
    ⟪hodgeRegularization A J α hs ht r f,hodgeInclusion A J α hs ht
      (hodgeSmooth A J α hs ht (hodgeTest A J α hs ht D p (componentTest j φ)
        (full_componentTest_compact j φ hc)
        ((full_componentTest_support j φ).trans (hφU.trans (hUL.trans L.neighborhood_subset)))))⟫ =
        ∫ z, chartDensity J α p.val z * φ z * L.realEvaluation z f j := by
  let θ := SchwartzMap.smulLeftCLM ℝ ρ φ
  let ψ := SchwartzMap.postcompCLM Complex.ofRealCLM θ
  have hθ : tsupport θ ⊆ tsupport φ := (SchwartzMap.tsupport_smulLeftCLM_subset ρ φ).trans inter_subset_left
  have hψ : tsupport ψ ⊆ tsupport θ := tsupport_comp_subset (map_zero Complex.ofRealCLM) θ
  have he := L.representative_on_test f ψ (hψ.trans (hθ.trans (hφU.trans hUL)))
  have hp := hodge_raw_weighted_pair A J α hs ht D hD p L.reciprocal ρ
    (hUL.trans L.neighborhood_subset) (fun z hz => L.reciprocal_eq z (hUL hz))
    hρ φ hc hφU j (hodgeRegularizedGraph A J α hs ht r hr f)
  have hψeq : SchwartzMap.smulLeftCLM ℂ (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ) = ψ := by
    ext z
    simp only [SchwartzMap.smulLeftCLM_apply (SchwartzMap.postcompCLM Complex.ofRealCLM ρ).hasTemperateGrowth,
      SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,smul_eq_mul,ψ,θ,
      SchwartzMap.smulLeftCLM_apply ρ.hasTemperateGrowth,Complex.ofReal_mul]
  rw [smulLeftCLM_apply_apply,hψeq,← he,hodgeRegularizedGraph_inclusion] at hp
  have hrp := congrArg Complex.re hp
  rw [bounded_real_component,Complex.ofReal_re] at hrp
  rw [← hrp]
  apply integral_congr_ae
  filter_upwards [] with z
  change θ z * (L.representative f z j).re = _
  rw [SchwartzMap.smulLeftCLM_apply ρ.hasTemperateGrowth,L.realEvaluation_apply]
  change (ρ z * φ z) * (L.representative f z j).re = _
  by_cases hz : z ∈ tsupport φ
  · rw [hρ z (hφU hz)]
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp only [mul_zero,zero_mul]
end LocalHodgeSmoothing
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
