import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalEvaluation
import OAI.Geometry.TamingCompatibility.Hodge.HodgeRegularization

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

lemma realEvaluation_smooth (f : L2 A J α hs ht true)
    (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a)
    {z : Space} (hz : z ∈ L.neighborhood) :
    L.realEvaluation z f = rawVector J α ht p.val (D p).toData a.val z := by
  have hg : hodgeRegularizedGraph A J α hs ht r hr f = hodgeSmooth A J α hs ht a := by
    apply hodgeInclusion_injective A J α hs ht
    rw [hodgeRegularizedGraph_inclusion,hodgeInclusion_smooth,ha]
  let b := SchwartzMap.smulLeftCLM HodgeNormalSymbol.W L.reciprocal
    (realVectorSchwartz A J α ht (fun q => (D q).toData) hD p a)
  let c := SchwartzMap.smulLeftCLM HodgeScalar.F L.cutoff (SchwartzMap.postcompCLM (embed 6) b)
  have he : L.representative f = c.toBoundedContinuousFunction := by
    apply boundedDistributionCLM_injective
    rw [boundedDistributionCLM_apply,boundedDistributionCLM_apply,L.representative_spec]
    change smulLeftCLM HodgeScalar.F L.cutoff
      (hodgeRawDistribution A J α hs ht D hD p L.reciprocal
        (hodgeRegularizedGraph A J α hs ht r hr f)) = _
    rw [hg,hodgeRawDistribution_smooth,product_schwartz,boundedDistribution_schwartz]
  ext j
  rw [L.realEvaluation_apply,he]
  change (c z j).re = _
  have hb : b z = rawVector J α ht p.val (D p).toData a.val z :=
    cutoff_realVector_raw A J α ht (fun q => (D q).toData) hD p a L.reciprocal
      (L.neighborhood_subset hz) (L.reciprocal_eq z hz)
  simp only [c,SchwartzMap.smulLeftCLM_apply L.cutoff.hasTemperateGrowth,
    L.cutoff_eq z hz,one_smul,SchwartzMap.postcompCLM_apply,hb,embed_apply,Complex.ofReal_re]
end LocalHodgeSmoothing
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma evaluationTerm_smooth_sum (i : C.centers) (u : MetricUnit g)
    (f : L2 A J α hs ht true) (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a) :
    ∑ j : Fin 6, C.evaluationTerm g i j u f =
      C.partition i u.val.proj * unitEvaluation J g a.val a.property u := by
  classical
  by_cases hu : u.val.proj ∈ tsupport (C.partition i)
  · have he := C.basisForm_expansion i a.val hu
    have he' := congrArg (fun b => b ![u.val.2,J.endomorphism u.val.proj u.val.2]) he
    simp only [ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul] at he'
    change ∑ j : Fin 6, unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property u *
      ((C.patch i).smoothing.realEvaluation (extChartAt Model (C.patch i).chart.val u.val.proj) f) j = _
    rw [(C.patch i).smoothing.realEvaluation_smooth f a ha (C.subordinate i hu).2]
    simpa only [unitEvaluation,ContinuousMap.coe_mk,eval,mul_comm] using he'
  · have hp := image_eq_zero_of_notMem_tsupport hu
    rw [hp,zero_mul]
    apply Finset.sum_eq_zero
    intro j _
    change unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property u * _ = 0
    have hz : unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property u = 0 := by
      change (C.basisForm i j).val u.val.proj ![u.val.2,J.endomorphism u.val.proj u.val.2] = 0
      rw [C.basisForm_zero i j hu]
      rfl
    rw [hz,zero_mul]

lemma evaluation_smooth (u : MetricUnit g) (f : L2 A J α hs ht true)
    (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a) :
    C.evaluation g u f = unitEvaluation J g a.val a.property u := by
  classical
  simp only [evaluation,sum_apply]
  simp_rw [C.evaluationTerm_smooth_sum g _ u f a ha]
  rw [← Finset.sum_mul]
  have hp : ∑ i : C.centers, C.partition i u.val.proj = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using C.partition.sum_eq_one (mem_univ u.val.proj)
  rw [hp,one_mul]
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

def hodgePreD : PreL2 A J α hs ht false →ₗ[ℝ] PreL2 A J α hs ht true where
  toFun a := ⟨exteriorDerivative a.val,a.property.exteriorDerivative⟩
  map_add' a b := Subtype.ext (exteriorDerivative_add a.property b.property)
  map_smul' c a := Subtype.ext (exteriorDerivative_smul c a.val)

def hodgeLaplacian : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true :=
  (hodgePreD A J α hs ht).comp (hodgeDelta A J α hs ht) +
    (preStar A J α hs ht).toLinearMap.comp ((hodgePreD A J α hs ht).comp
      ((hodgeDelta A J α hs ht).comp (preStar A J α hs ht).toLinearMap))

lemma hodgeLaplacian_apply (a : PreL2 A J α hs ht true) :
    hodgeLaplacian A J α hs ht a =
      hodgePreD A J α hs ht (hodgeDelta A J α hs ht a) +
        preStar A J α hs ht (hodgePreD A J α hs ht
          (hodgeDelta A J α hs ht (preStar A J α hs ht a))) := rfl

lemma smoothL2_preD (a : PreL2 A J α hs ht false) :
    smoothL2 A J α hs ht true (hodgePreD A J α hs ht a) = testDerivative A J α hs ht a := rfl

lemma hodgeLaplacian_green_weak (a : PreL2 A J α hs ht true)
    (v : hodgeEnergy A J α hs ht) :
    ⟪smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a),
      hodgeInclusion A J α hs ht v⟫ =
      ⟪hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht a),
        hodgeWeakDerivative A J α hs ht v⟫ := by
  rw [hodgeLaplacian_apply,map_add,inner_add_left,← l2Star_smooth,
    smoothL2_preD,smoothL2_preD]
  change ⟪testDerivative A J α hs ht (hodgeDelta A J α hs ht a),v.val.fst⟫ +
    ⟪l2Star A J α hs ht (testDerivative A J α hs ht
      (hodgeDelta A J α hs ht (preStar A J α hs ht a))),v.val.fst⟫ = _
  rw [hodgeEnergy_weak,hodgeEnergy_weak_star]
  rfl

lemma hodgeLaplacian_green (a b : PreL2 A J α hs ht true) :
    ⟪smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a),smoothL2 A J α hs ht true b⟫ =
      ⟪hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht a),
        hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht b)⟫ :=
  hodgeLaplacian_green_weak A J α hs ht a (hodgeSmooth A J α hs ht b)

lemma hodgeLaplacian_nonnegative (a : PreL2 A J α hs ht true) :
    0 ≤ ⟪smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a),smoothL2 A J α hs ht true a⟫ := by
  rw [hodgeLaplacian_green]
  exact real_inner_self_nonneg

lemma hodgeLaplacian_symmetric (a b : PreL2 A J α hs ht true) :
    ⟪smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a),smoothL2 A J α hs ht true b⟫ =
      ⟪smoothL2 A J α hs ht true a,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht b)⟫ := by
  calc
    _ = ⟪hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht a),
        hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht b)⟫ :=
      hodgeLaplacian_green A J α hs ht a b
    _ = ⟪hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht b),
        hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht a)⟫ := real_inner_comm _ _
    _ = ⟪smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht b),smoothL2 A J α hs ht true a⟫ :=
      (hodgeLaplacian_green A J α hs ht b a).symm
    _ = _ := real_inner_comm _ _

lemma hodgeLaplacian_star (a : PreL2 A J α hs ht true) :
    hodgeLaplacian A J α hs ht (preStar A J α hs ht a) =
      preStar A J α hs ht (hodgeLaplacian A J α hs ht a) := by
  rw [hodgeLaplacian_apply,hodgeLaplacian_apply,map_add,preStar_square,preStar_square]
  exact add_comm _ _
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
