import OAI.Geometry.Relativity.CKS.LocalConstraints
import OAI.Geometry.Relativity.CKS.ConstraintLocalInverse

namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CKSIntrinsicConstraints
lemma full_rank_physical_constraints_pullback
    {f : PhysicalPoint → PhysicalPoint} {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ f y)
    (hb : Function.Bijective (fderiv ℝ f x))
    (hdata : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ G (f y) ∧
      ContDiffAt ℝ ∞ K (f y) ∧ (G (f y)).PosDef)
    (hKsym : (K (f x)).IsHermitian) :
    (physicalMetricJet (coordinatePullback f G) x).energy
      (physicalTensorJet (coordinatePullback f K) x) =
      (physicalMetricJet G (f x)).energy (physicalTensorJet K (f x)) ∧
    CKSLocalBending.momentumSq (physicalMetricJet (coordinatePullback f G) x)
      (physicalTensorJet (coordinatePullback f K) x) =
      CKSLocalBending.momentumSq (physicalMetricJet G (f x)) (physicalTensorJet K (f x)) := by
  obtain ⟨e,he,hx,hs,hi⟩ := exists_smooth_local_inverse hf hb
  have ht : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ G y ∧ ContDiffAt ℝ ∞ K y ∧ (G y).PosDef := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx),
      (e.tendsto_symm hx).eventually hdata] with y hy hd
    rw [← he,e.right_inv hy] at hd
    exact hd
  have hp : ∀ᶠ y in 𝓝 (e x), (G y).PosDef := ht.mono fun _ h => h.2.2
  have hE : ∀ᶠ y in 𝓝 (e x), SmoothOrthonormalAt G (matrixFrame G) y := by
    filter_upwards [ht,hp.eventually_nhds] with y hy hpy
    exact actual_matrix_frame hy.1 hpy
  rw [← he] at hi hKsym ⊢
  exact ⟨local_coordinate_energy_pullback e G K (matrixFrame G) hx hs hi hE
    ht.self_of_nhds.2.1 hKsym,
    local_coordinate_momentumSq_pullback e G K (matrixFrame G) hx hs hi hE ht.self_of_nhds.2.1⟩

def physicalMap (f : E → E) : PhysicalPoint → PhysicalPoint :=
  CKSCartesianOuter.toPoint ∘ f ∘ CKSCartesianOuter.toPoint.symm

lemma physicalMap_smooth {f : E → E} {x : E} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (physicalMap f) (CKSCartesianOuter.toPoint x) := by
  exact CKSCartesianOuter.toPoint.contDiff.contDiffAt.comp _
    (hf.comp _ CKSCartesianOuter.toPoint.symm.contDiff.contDiffAt)
lemma physicalMap_fderiv {f : E → E} {y : PhysicalPoint}
    (hf : DifferentiableAt ℝ f (CKSCartesianOuter.toPoint.symm y)) :
    fderiv ℝ (physicalMap f) y = CKSCartesianOuter.toPoint.toContinuousLinearMap.comp
      ((fderiv ℝ f (CKSCartesianOuter.toPoint.symm y)).comp
        CKSCartesianOuter.toPoint.symm.toContinuousLinearMap) := by
  simp only [physicalMap,fderiv_comp y CKSCartesianOuter.toPoint.differentiableAt
    (hf.comp y CKSCartesianOuter.toPoint.symm.differentiableAt),
    fderiv_comp y hf CKSCartesianOuter.toPoint.symm.differentiableAt,ContinuousLinearEquiv.fderiv]
lemma physicalMap_bijective_fderiv {f : E → E} {x : E}
    (hf : DifferentiableAt ℝ f x) (hb : Function.Bijective (fderiv ℝ f x)) :
    Function.Bijective (fderiv ℝ (physicalMap f) (CKSCartesianOuter.toPoint x)) := by
  rw [physicalMap_fderiv (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf),
    ContinuousLinearEquiv.symm_apply_apply]
  exact CKSCartesianOuter.toPoint.bijective.comp (hb.comp CKSCartesianOuter.toPoint.symm.bijective)
lemma spatialCoefficients_function_pullback (f : E → E) (A : SpatialTensor) {y : PhysicalPoint}
    (hf : DifferentiableAt ℝ f (CKSCartesianOuter.toPoint.symm y)) :
    coordinatePullback (physicalMap f) (spatialCoefficients A) y =
      spatialCoefficients (spatialTensorPullback f A) y := by
  ext i j
  unfold coordinatePullback
  rw [spatialCoefficients_pair,physicalMap_fderiv hf]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply,physicalMap,Function.comp_apply]
  rfl

lemma full_rank_spatial_constraints_pullback
    {f : E → E} {A B : SpatialTensor} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ f y)
    (hb : Function.Bijective (fderiv ℝ f x))
    (hdata : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ A (f y) ∧ ContDiffAt ℝ ∞ B (f y) ∧
      (∀ v w, A (f y) v w = A (f y) w v) ∧
      (∀ v : E, v ≠ 0 → 0 < A (f y) v v))
    (hBsym : ∀ v w, B (f x) v w = B (f x) w v) :
    spatialEnergy (spatialTensorPullback f A) (spatialTensorPullback f B) x =
      spatialEnergy A B (f x) ∧
    coordinateMomentumNorm (spatialTensorPullback f A) (spatialTensorPullback f B) x =
      coordinateMomentumNorm A B (f x) := by
  have ht := CKSCartesianOuter.toPoint.symm.continuous.continuousAt (x := CKSCartesianOuter.toPoint x)
  have hf' : ∀ᶠ y in 𝓝 (CKSCartesianOuter.toPoint x), ContDiffAt ℝ ∞ (physicalMap f) y := by
    filter_upwards [ht.eventually (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf)] with y hy
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using physicalMap_smooth hy
  have hd : ∀ᶠ y in 𝓝 (CKSCartesianOuter.toPoint x),
      ContDiffAt ℝ ∞ (spatialCoefficients A) (physicalMap f y) ∧
      ContDiffAt ℝ ∞ (spatialCoefficients B) (physicalMap f y) ∧
      (spatialCoefficients A (physicalMap f y)).PosDef := by
    filter_upwards [ht.eventually (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hdata)] with y hy
    exact ⟨spatialCoefficients_smooth hy.1,spatialCoefficients_smooth hy.2.1,
      spatialCoefficients_positive hy.2.2.1 hy.2.2.2⟩
  have heq (G : SpatialTensor) :
      coordinatePullback (physicalMap f) (spatialCoefficients G) =ᶠ[𝓝 (CKSCartesianOuter.toPoint x)]
        spatialCoefficients (spatialTensorPullback f G) := by
    filter_upwards [ht.eventually (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf)] with y hy
    exact spatialCoefficients_function_pullback f G (hy.differentiableAt (by simp))
  have hBs : (spatialCoefficients B (physicalMap f (CKSCartesianOuter.toPoint x))).IsHermitian := by
    simpa only [physicalMap,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using
      spatialCoefficients_symmetric hBsym
  obtain ⟨hC,hQ⟩ := full_rank_physical_constraints_pullback hf'
    (physicalMap_bijective_fderiv (hf.self_of_nhds.differentiableAt (by simp)) hb) hd hBs
  rw [physicalMetricJet_congr (heq A),physicalTensorJet_congr (heq B)] at hC hQ
  refine ⟨?_,?_⟩
  · simpa only [spatialEnergy,physicalMap,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using hC
  · simpa only [coordinateMomentumNorm,physicalMap,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using congrArg Real.sqrt hQ
end CKSIntrinsicConstraints

end

end OAI
