import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricDensity
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricTensor

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity
open scoped ContDiff RealInnerProductSpace
abbrev V := EuclideanSpace ℝ (Fin 4)
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace
abbrev EMetric := (InnerProductSpace.toDual ℝ V).toContinuousLinearMap

def volumeDensity (M : MetricTensor (V := V)) : ℝ :=
  MetricDensity.density (MetricDensity.gram (stdOrthonormalBasis ℝ V).toBasis M)

lemma gram_euclidean : MetricDensity.gram (stdOrthonormalBasis ℝ V).toBasis EMetric = 1 := by
  ext i j
  simp [MetricDensity.gram, EMetric, Matrix.one_apply, OrthonormalBasis.inner_eq_ite]

lemma volumeDensity_euclidean : volumeDensity EMetric = 1 := by
  simp [volumeDensity, gram_euclidean, MetricDensity.density]

lemma detGram_contDiff : ContDiff ℝ ∞ (fun M : MetricTensor (V := V) =>
    (MetricDensity.gram (stdOrthonormalBasis ℝ V).toBasis M).det) := by
  rw [← contDiffOn_univ]
  exact MetricDensity.contDiffOn_det (fun i j =>
    ((contDiffOn_id.clm_apply contDiffOn_const).clm_apply contDiffOn_const))

lemma volumeDensity_contDiffAt : ContDiffAt ℝ ∞ volumeDensity EMetric := by
  apply detGram_contDiff.contDiffAt.sqrt
  simp [gram_euclidean]

def metricOperator : MetricTensor (V := V) →L[ℝ] (V →L[ℝ] V) :=
  (ContinuousLinearMap.compL ℝ V (V →L[ℝ] ℝ) V)
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearMap

lemma metricOperator_apply (M : MetricTensor (V := V)) (u : V) :
    metricOperator M u = (InnerProductSpace.toDual ℝ V).symm (M u) := rfl

lemma metricOperator_euclidean : metricOperator EMetric = ContinuousLinearMap.id ℝ V := by
  apply ContinuousLinearMap.ext
  intro u
  exact (InnerProductSpace.toDual ℝ V).symm_apply_apply u

def cometric (M : MetricTensor (V := V)) : V →L[ℝ] V :=
  ContinuousLinearMap.inverse (metricOperator M)

lemma cometric_euclidean : cometric EMetric = ContinuousLinearMap.id ℝ V := by
  rw [cometric, metricOperator_euclidean]
  exact ContinuousLinearMap.inverse_id

lemma cometric_contDiffAt : ContDiffAt ℝ ∞ cometric EMetric := by
  apply ContDiffAt.comp EMetric _ metricOperator.contDiff.contDiffAt
  rw [metricOperator_euclidean]
  exact contDiffAt_map_inverse (ContinuousLinearEquiv.refl ℝ V)

def principal (M : MetricTensor (V := V)) (i j : Fin 4) : ℝ :=
  ⟪cometric M (EuclideanSpace.basisFun (Fin 4) ℝ i),
    EuclideanSpace.basisFun (Fin 4) ℝ j⟫

lemma principal_euclidean (i j : Fin 4) : principal EMetric i j = if i=j then 1 else 0 := by
  simp [principal, cometric_euclidean, EuclideanSpace.inner_single_left]

lemma principal_contDiffAt (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun M : MetricTensor (V := V) => principal M i j) EMetric :=
  ContDiffAt.inner ℝ (cometric_contDiffAt.clm_apply contDiffAt_const) contDiffAt_const

lemma jets (m : V → MetricTensor (V := V)) (hm : ContDiffAt ℝ ∞ m 0)
    (hm0 : m 0 = EMetric) (hd : fderiv ℝ m 0 = 0) :
    ContDiffAt ℝ ∞ (fun z => volumeDensity (m z)) 0 ∧
    volumeDensity (m 0) = 1 ∧
    fderiv ℝ (fun z => volumeDensity (m z)) 0 = 0 ∧
    (∀ i j, ContDiffAt ℝ ∞ (fun z => principal (m z) i j) 0 ∧
      principal (m 0) i j = (if i=j then 1 else 0) ∧
      fderiv ℝ (fun z => principal (m z) i j) 0 = 0) := by
  have hd' : HasFDerivAt m (0 : V →L[ℝ] MetricTensor (V := V)) 0 := by
    rw [← hd]
    exact (hm.differentiableAt (by simp)).hasFDerivAt
  have hv : ContDiffAt ℝ ∞ volumeDensity (m 0) := by rw [hm0]; exact volumeDensity_contDiffAt
  refine ⟨hv.comp 0 hm, by rw [hm0,volumeDensity_euclidean], ?_, ?_⟩
  · simpa only [Function.comp_def, ContinuousLinearMap.comp_zero] using
      ((hv.differentiableAt (by simp)).hasFDerivAt.comp 0 hd').fderiv
  · intro i j
    have hp : ContDiffAt ℝ ∞ (fun M => principal M i j) (m 0) := by
      rw [hm0]; exact principal_contDiffAt i j
    refine ⟨hp.comp 0 hm, by rw [hm0,principal_euclidean], ?_⟩
    simpa only [Function.comp_def, ContinuousLinearMap.comp_zero] using
      ((hp.differentiableAt (by simp)).hasFDerivAt.comp 0 hd').fderiv

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end
end
end
end
end
end
end

end OAI
