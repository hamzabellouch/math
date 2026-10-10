import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Dpos
import OAI.Geometry.TamingCompatibility.Charts.MetricCalculus

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open scoped RealInnerProductSpace
open NormalJets GeometricNormalCharts
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma metricOperator_inner (M : MetricTensor (V := V)) (u v : V) :
    ⟪metricOperator M u,v⟫ = M u v := by
  simp only [metricOperator_apply, InnerProductSpace.toDual_symm_apply]

lemma cometric_eq_frame (M : MetricTensor (V := V)) (B : V ≃L[ℝ] V)
    (hB : ∀ u v, M (B u) (B v) = ⟪u,v⟫) :
    cometric M = B.toContinuousLinearMap ∘L B.toContinuousLinearMap.adjoint := by
  have hM (u v : V) : M u v = ⟪B.symm u,B.symm v⟫ := by
    simpa only [B.apply_symm_apply] using hB (B.symm u) (B.symm v)
  have hc : metricOperator M ∘L (B.toContinuousLinearMap ∘L B.toContinuousLinearMap.adjoint) =
      ContinuousLinearMap.id ℝ V := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℝ
    intro v
    change ⟪metricOperator M (B (B.toContinuousLinearMap.adjoint u)),v⟫ = ⟪u,v⟫
    rw [metricOperator_inner,hM,B.symm_apply_apply,ContinuousLinearMap.adjoint_inner_left]
    change ⟪u,B (B.symm v)⟫ = _
    rw [B.apply_symm_apply]
  have hi : Function.Injective (metricOperator M) := by
    intro u v he
    have hh (w) := congrArg (fun f : V => ⟪f,w⟫) he
    simp only [metricOperator_inner,hM] at hh
    apply B.symm.injective
    apply ext_inner_right ℝ
    intro z
    simpa only [B.symm_apply_apply] using hh (B z)
  apply ContinuousLinearMap.inverse_eq hc
  apply ContinuousLinearMap.ext
  intro u
  apply hi
  have hh := congrArg (fun f : V →L[ℝ] V => f (metricOperator M u)) hc
  exact hh

lemma frameMap_adjoint_basis (b : Fin 4 → V) (i : Fin 4) :
    (frameMap b).adjoint (EuclideanSpace.basisFun (Fin 4) ℝ i) =
      LocalMatrixOperator.frameCovector b i := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left]
  simp [frameMap_apply,LocalMatrixOperator.frameCovector,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct]

lemma principal_eq_frame (g : MetricModel.Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (i j : Fin 4) :
    principal g.bilinear i j =
      ⟪LocalMatrixOperator.frameCovector b i,LocalMatrixOperator.frameCovector b j⟫ := by
  have he := cometric_eq_frame g.bilinear (frameEquiv g b hb) (frameMap_metric g b hb)
  rw [principal,he]
  change ⟪frameMap b ((frameMap b).adjoint _),_⟫ = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [frameMap_adjoint_basis,frameMap_adjoint_basis]

lemma principal_pullback_frame (M : MetricTensor (V := V)) (B L : V ≃L[ℝ] V)
    (hB : ∀ u v, M (B u) (B v) = ⟪u,v⟫) (i j : Fin 4) :
    principal (MetricDensity.pullMetric M L.toContinuousLinearMap) i j =
      ⟪(B.toContinuousLinearMap.adjoint ∘L L.symm.toContinuousLinearMap.adjoint)
          (EuclideanSpace.basisFun (Fin 4) ℝ i),
        (B.toContinuousLinearMap.adjoint ∘L L.symm.toContinuousLinearMap.adjoint)
          (EuclideanSpace.basisFun (Fin 4) ℝ j)⟫ := by
  have hBL : ∀ u v, MetricDensity.pullMetric M L.toContinuousLinearMap
      ((B.trans L.symm) u) ((B.trans L.symm) v) = ⟪u,v⟫ := by
    intro u v
    change M (L (L.symm (B u))) (L (L.symm (B v))) = _
    simpa only [L.apply_symm_apply] using hB u v
  rw [principal,cometric_eq_frame _ (B.trans L.symm) hBL]
  change ⟪(B.trans L.symm).toContinuousLinearMap
    ((B.trans L.symm).toContinuousLinearMap.adjoint _),_⟫ = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have he : (B.trans L.symm).toContinuousLinearMap =
      L.symm.toContinuousLinearMap ∘L B.toContinuousLinearMap := rfl
  rw [he,ContinuousLinearMap.adjoint_comp]

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
