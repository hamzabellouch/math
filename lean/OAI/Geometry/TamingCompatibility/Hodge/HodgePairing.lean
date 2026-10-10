import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.LocalDDStarEstimate
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeClosedResolvent
import OAI.Geometry.TamingCompatibility.Hodge.HodgeHarmonicSmooth

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def hodgeCubeRepresents (r : ℝ) (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ)
    (U : L2 A J α hs ht true) : Prop :=
  ∀ a : PreL2 A J α hs ht true,
    ⟪U,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)⟫ = F a

include D hD in
lemma hodgeCubeRepresents_annihilates_closed (r : ℝ) (hr : 0 < r)
    (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) (U : L2 A J α hs ht true)
    (hU : hodgeCubeRepresents A J α hs ht r F U)
    (hF : ∀ a : PreL2 A J α hs ht true, IsClosed a.val → F a = 0)
    (b : PreL2 A J α hs ht true) (hbc : IsClosed b.val) :
    ⟪U,smoothL2 A J α hs ht true b⟫ = 0 := by
  obtain ⟨a,ha,hac,_⟩ := hodgeRegularization_smooth_closed_exact A J α hs ht D hD r hr b
  have hi := hodgeRegularization_smooth_inverse A J α hs ht r hr b a ha
  rw [← hi,hU a]
  exact hF a (hac.mpr hbc)

include D hD in
lemma hodgeCubeRepresents_star_weakClosed (r : ℝ) (hr : 0 < r)
    (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) (V : L2 A J α hs ht true)
    (hV : hodgeCubeRepresents A J α hs ht r F V)
    (hF : ∀ ξ : PreL2 A J α hs ht false, F (hodgePreD A J α hs ht ξ) = 0) :
    l2Star A J α hs ht V ∈ hodgeWeakClosedL2 A J α hs ht := by
  intro ξ
  rw [l2Star_inner,← smoothL2_preD]
  obtain ⟨a,ha,_,hae⟩ := hodgeRegularization_smooth_closed_exact A J α hs ht D hD r hr
    (hodgePreD A J α hs ht ξ)
  have hi := hodgeRegularization_smooth_inverse A J α hs ht r hr (hodgePreD A J α hs ht ξ) a ha
  have he : hodgeIsExact A J α hs ht a := hae.mpr ⟨ξ,rfl⟩
  obtain ⟨η,hη⟩ := he
  rw [← hi,hV a,hη]
  exact hF η

include D hD in

theorem hodge_regularized_zero_pairing (r : ℝ) (hr : 0 < r)
    (F F' : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) (U V : L2 A J α hs ht true)
    (hU : hodgeCubeRepresents A J α hs ht r F U)
    (hV : hodgeCubeRepresents A J α hs ht r F' V)
    (hF : ∀ a : PreL2 A J α hs ht true, IsClosed a.val → F a = 0)
    (hF' : ∀ ξ : PreL2 A J α hs ht false, F' (hodgePreD A J α hs ht ξ) = 0) :
    ⟪U,l2Star A J α hs ht V⟫ = 0 := by
  exact hodge_pair_weakClosed_eq_zero A J α hs ht D hD U (l2Star A J α hs ht V)
    (hodgeCubeRepresents_annihilates_closed A J α hs ht D hD r hr F U hU hF)
    (hodgeCubeRepresents_star_weakClosed A J α hs ht D hD r hr F' V hV hF')

attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {A J α hs ht D hD} {r : ℝ} {hr : 0 < r}
variable (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma regularize_cubeRepresents (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] :
    hodgeCubeRepresents A J α hs ht r (unitMeasureCurrent J g μ) (C.regularize g μ) := by
  intro a
  exact C.regularize_smoothShift_cube g μ a
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix

def antiPairSelector : C 6 →L[ℂ] C 2 := unit 2 6 0 1 + unit 2 6 1 2
end TamingCompatibility.ComplexMatrix
namespace TamingCompatibility.HodgeChart
open GeometricChart ManifoldForms ManifoldLocalization ComplexMatrix Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [CompactSpace X] in
lemma scalar_pair_zero (p : A.centers) (a : TwoForm X) (z : Space) :
    GeometricChart.scalar A J α ht D p a 2 z = HodgeChart.scalar A J α ht D p a 1 z := rfl
omit [CompactSpace X] in
lemma scalar_pair_one (p : A.centers) (a : TwoForm X) (z : Space) :
    GeometricChart.scalar A J α ht D p a 3 z = HodgeChart.scalar A J α ht D p a 2 z := rfl

lemma realPairSchwartz_from_full (p : A.centers) (f : smoothForms X 2) :
    SchwartzMap.postcompCLM (embed 2) (realPairSchwartz A J α ht D hD p f) =
      SchwartzMap.postcompCLM antiPairSelector (scalarVectorLinear A J α ht D hD p f) := by
  rw [← realVectorSchwartz_embed A J α ht D hD p f]
  ext z i
  fin_cases i <;> simp [antiPairSelector,realPairSchwartz_apply,realVectorSchwartz_apply,
    EuclideanEnergy.pair,scalar_pair_zero,scalar_pair_one]
end TamingCompatibility.HodgeChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ComplexMatrix GeometricChart
open TemperedDistribution EuclideanSobolevOperators HilbertSobolev
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma weightedRawRHS_full_distribution (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (f : antiPre A J α hs ht) :
    (SchwartzMap.postcompCLM (embed 2)
      (weightedRawRHS A J α hs ht (fun p => (D p).toData) hD p τ ρ f) : 𝓢'(Space,C 2)) =
      (2:ℂ) • smulLeftCLM (C 2) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
        (fiberMap antiPairSelector
          (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f.val))) := by
  rw [hodgeRawDistribution_smooth,fiberMap_schwartz,product_schwartz,← map_smul]
  congr 1
  ext z i
  have hp := HodgeChart.realPairSchwartz_from_full A J α ht (fun p => (D p).toData) hD p f.val
  rw [← HodgeChart.realVectorSchwartz_embed A J α ht (fun p => (D p).toData) hD p f.val] at hp
  have hpz := congrArg (fun a : 𝓢(Space,C 2) => a z i) hp
  fin_cases i <;> simp [antiPairSelector] at hpz <;>
    simp [weightedRawRHS,antiPairSelector,
      SchwartzMap.smulLeftCLM_apply_apply ρ.hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.postcompCLM Complex.ofRealCLM ρ).hasTemperateGrowth,
      hpz]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
