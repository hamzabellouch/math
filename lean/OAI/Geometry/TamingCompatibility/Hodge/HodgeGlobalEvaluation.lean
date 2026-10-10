import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.GeometricSeparatingProbability
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothingCover
import OAI.Geometry.TamingCompatibility.Hodge.HodgeLocalKernel

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Bundle Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def evaluationTerm (i : C.centers) (j : Fin 6) (u : MetricUnit g) :
    L2 A J α hs ht true →L[ℝ] ℝ :=
  unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property u •
    (EuclideanSpace.proj j).comp ((C.patch i).smoothing.realEvaluation
      (extChartAt Model (C.patch i).chart.val u.val.proj))

lemma evaluationTerm_continuous (i : C.centers) (j : Fin 6) :
    Continuous (C.evaluationTerm g i j) := by
  have hb : Continuous (fun u : MetricUnit g => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u.val.proj ∈ tsupport (C.partition i)
  · have hchart : ContinuousAt (fun v : MetricUnit g => extChartAt Model (C.patch i).chart.val v.val.proj) u :=
      ((continuousOn_extChartAt _ _ (C.subordinate i hu).1).continuousAt
        ((isOpen_extChartAt_source _).mem_nhds (C.subordinate i hu).1)).comp (f := fun v : MetricUnit g => v.val.proj) hb.continuousAt
    exact ((unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property).continuous.continuousAt).smul
      (continuousAt_const.clm_comp ((C.patch i).smoothing.realEvaluation_continuous.continuousAt.comp hchart))
  · apply (continuousAt_const (y := (0 : L2 A J α hs ht true →L[ℝ] ℝ))).congr_of_eventuallyEq
    have hn : ∀ᶠ v : MetricUnit g in 𝓝 u, v.val.proj ∉ tsupport (C.partition i) :=
      hb.continuousAt.eventually ((isClosed_tsupport (C.partition i)).isOpen_compl.mem_nhds hu)
    filter_upwards [hn] with v hv
    unfold evaluationTerm
    have hz : unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property v = 0 := by
      change eval (C.basisForm i j).val v.val.proj v.val.2 (J.endomorphism v.val.proj v.val.2) = 0
      change (C.basisForm i j).val v.val.proj ![v.val.2,J.endomorphism v.val.proj v.val.2] = 0
      rw [C.basisForm_zero i j hv]
      rfl
    rw [hz,zero_smul]

def evaluation (u : MetricUnit g) : L2 A J α hs ht true →L[ℝ] ℝ :=
  ∑ i : C.centers, ∑ j : Fin 6, C.evaluationTerm g i j u

lemma evaluation_continuous : Continuous (C.evaluation g) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact C.evaluationTerm_continuous g i j

def continuousEvaluation : C(MetricUnit g,L2 A J α hs ht true →L[ℝ] ℝ) :=
  ⟨C.evaluation g,C.evaluation_continuous g⟩
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def l2StarIsometry : L2 A J α hs ht true →ₗᵢ[ℝ] L2 A J α hs ht true :=
  ⟨(l2Star A J α hs ht).toLinearMap,l2Star_norm A J α hs ht⟩

def hodgeAmbientStar : HodgeGraphSpace A J α hs ht →ₗᵢ[ℝ] HodgeGraphSpace A J α hs ht :=
  LinearIsometry.withLpProdMap 2 (l2StarIsometry A J α hs ht)
    (LinearIsometryEquiv.withLpProdComm 2 ℝ (L2 A J α hs ht false)
      (L2 A J α hs ht false)).toLinearIsometry

lemma hodgeAmbientStar_graph (a : PreL2 A J α hs ht true) :
    hodgeAmbientStar A J α hs ht (hodgeGraph A J α hs ht a) =
      hodgeGraph A J α hs ht (preStar A J α hs ht a) := by
  apply (WithLp.linearEquiv 2 ℝ _).injective
  apply Prod.ext
  · exact l2Star_smooth A J α hs ht a
  · apply (WithLp.linearEquiv 2 ℝ _).injective
    change (smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht a)),
      smoothL2 A J α hs ht false (hodgeDelta A J α hs ht a)) =
      (smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht a)),
      smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht (preStar A J α hs ht a))))
    rw [preStar_square]

lemma hodgeAmbientStar_square (v : HodgeGraphSpace A J α hs ht) :
    hodgeAmbientStar A J α hs ht (hodgeAmbientStar A J α hs ht v) = v := by
  apply (WithLp.linearEquiv 2 ℝ _).injective
  apply Prod.ext
  · exact l2Star_square A J α hs ht v.fst
  · rfl

lemma hodgeAmbientStar_mem (u : hodgeEnergy A J α hs ht) :
    hodgeAmbientStar A J α hs ht u.val ∈ hodgeEnergy A J α hs ht := by
  have hc : _root_.IsClosed {v : HodgeGraphSpace A J α hs ht |
      hodgeAmbientStar A J α hs ht v ∈ hodgeEnergy A J α hs ht} :=
    (LinearMap.range (hodgeGraph A J α hs ht)).isClosed_topologicalClosure.preimage
      (hodgeAmbientStar A J α hs ht).continuous
  apply (closure_minimal ?_ hc) u.property
  rintro _ ⟨a,rfl⟩
  change hodgeAmbientStar A J α hs ht (hodgeGraph A J α hs ht a) ∈ hodgeEnergy A J α hs ht
  rw [hodgeAmbientStar_graph]
  exact subset_closure ⟨_,rfl⟩

def hodgeDomainStar : hodgeEnergy A J α hs ht →ₗᵢ[ℝ] hodgeEnergy A J α hs ht where
  toFun u := ⟨hodgeAmbientStar A J α hs ht u.val,hodgeAmbientStar_mem A J α hs ht u⟩
  map_add' u v := Subtype.ext ((hodgeAmbientStar A J α hs ht).map_add u.val v.val)
  map_smul' c u := Subtype.ext ((hodgeAmbientStar A J α hs ht).map_smul c u.val)
  norm_map' u := (hodgeAmbientStar A J α hs ht).norm_map u.val

lemma hodgeDomainStar_square (u : hodgeEnergy A J α hs ht) :
    hodgeDomainStar A J α hs ht (hodgeDomainStar A J α hs ht u) = u :=
  Subtype.ext (hodgeAmbientStar_square A J α hs ht u.val)

lemma hodgeInclusion_star (u : hodgeEnergy A J α hs ht) :
    hodgeInclusion A J α hs ht (hodgeDomainStar A J α hs ht u) =
      l2Star A J α hs ht (hodgeInclusion A J α hs ht u) := rfl

lemma hodgeDerivative_star_inner (u v : hodgeEnergy A J α hs ht) :
    ⟪hodgeWeakDerivative A J α hs ht (hodgeDomainStar A J α hs ht u),
      hodgeWeakDerivative A J α hs ht (hodgeDomainStar A J α hs ht v)⟫ =
      ⟪hodgeWeakDerivative A J α hs ht u,hodgeWeakDerivative A J α hs ht v⟫ := by
  change ⟪u.val.snd.snd,v.val.snd.snd⟫ + ⟪u.val.snd.fst,v.val.snd.fst⟫ =
    ⟪u.val.snd.fst,v.val.snd.fst⟫ + ⟪u.val.snd.snd,v.val.snd.snd⟫
  exact add_comm _ _

lemma hodgeDerivative_star_adjoint (u v : hodgeEnergy A J α hs ht) :
    ⟪hodgeWeakDerivative A J α hs ht (hodgeDomainStar A J α hs ht u),
      hodgeWeakDerivative A J α hs ht v⟫ =
      ⟪hodgeWeakDerivative A J α hs ht u,
        hodgeWeakDerivative A J α hs ht (hodgeDomainStar A J α hs ht v)⟫ := by
  conv_lhs => rw [← hodgeDomainStar_square A J α hs ht v]
  exact hodgeDerivative_star_inner A J α hs ht u (hodgeDomainStar A J α hs ht v)
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
