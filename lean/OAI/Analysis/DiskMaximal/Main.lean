import OAI.Analysis.DiskMaximal.AbsoluteContinuity

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace CenteredDiskEndpoint
open WeakSobolev

lemma hasGradient_iff_hasWeakGradient {f : Plane → ℝ} {g : Plane → Plane}
    (hf : LocallyIntegrable f) (hg : Integrable g) :
    HasGradient (μ := volume) f g ↔ HasWeakGradient f g := by
  constructor
  · intro hw φ hφ hc i
    simpa only [testPartial,EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul]
      using hw φ hφ hc (EuclideanSpace.single i 1)
  · intro hw φ hφ hc v
    have hv : v=∑ i : Fin 2,v i • EuclideanSpace.single i 1 := by
      simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
        ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v).symm
    have hleft i : Integrable (fun x => f x*testPartial φ i x) :=
      hf.integrable_smul_right_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ _)
    have hright i : Integrable (fun x => g x i*φ x) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hg).locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
    have hd x : f x*fderiv ℝ φ x v=∑ i : Fin 2,v i*(f x*testPartial φ i x) := by
      conv_lhs => rw [hv]
      simp only [_root_.map_sum,map_smul,smul_eq_mul,Finset.mul_sum,testPartial]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hi x : ⟪g x,v⟫*φ x=∑ i : Fin 2,v i*(g x i*φ x) := by
      conv_lhs => rw [hv]
      simp only [inner_sum,real_inner_smul_right,EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hd,hi]
    rw [integral_finsetSum _ (fun i _ => (hleft i).const_mul _),
      integral_finsetSum _ (fun i _ => (hright i).const_mul _)]
    simp only [integral_const_mul,hw φ hφ hc,Finset.sum_neg_distrib,mul_neg]

/-- The coordinate isometry preserves Euclidean, not max-product, norms. -/
def complexPlane : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

lemma integrable_comp_complexPlane {F : Type*} [NormedAddCommGroup F] {f : Plane → F} :
    Integrable (fun z => f (complexPlane z)) ↔ Integrable f :=
  complexPlane.measurePreserving.integrable_comp_emb complexPlane.toMeasurableEquiv.measurableEmbedding

lemma integrable_comp_complexPlane_symm {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} :
    Integrable (fun x => f (complexPlane.symm x)) ↔ Integrable f :=
  complexPlane.symm.measurePreserving.integrable_comp_emb complexPlane.symm.toMeasurableEquiv.measurableEmbedding

lemma locallyIntegrable_comp_complexPlane {f : Plane → ℝ} :
    LocallyIntegrable (fun z => f (complexPlane z)) ↔ LocallyIntegrable f := by
  have h := locallyIntegrable_map_homeomorph complexPlane.toHomeomorph (f := f) (μ := volume)
  change LocallyIntegrable f (Measure.map complexPlane volume) ↔ LocallyIntegrable (fun z => f (complexPlane z)) at h
  rw [complexPlane.measurePreserving.map_eq] at h
  exact h.symm

lemma gradientNorm_comp_complexPlane (g : Plane → Plane) :
    (∫ z,‖complexPlane.symm (g (complexPlane z))‖)=gradientNorm g := by
  simp only [LinearIsometryEquiv.norm_map,gradientNorm]
  exact complexPlane.measurePreserving.integral_comp complexPlane.toMeasurableEquiv.measurableEmbedding (fun x => ‖g x‖)

lemma gradientNorm_comp_complexPlane_symm (G : ℂ → ℂ) :
    gradientNorm (fun x => complexPlane (G (complexPlane.symm x)))=∫ z,‖G z‖ := by
  simp only [LinearIsometryEquiv.norm_map,gradientNorm]
  exact complexPlane.symm.measurePreserving.integral_comp complexPlane.symm.toMeasurableEquiv.measurableEmbedding (fun z => ‖G z‖)
end CenteredDiskEndpoint

namespace CenteredDiskEndpoint
open WeakSobolev DiskMaximalTools

/-- Equality of the actual all-real-radius operators, including the normalization
and absolute values. This bridge has no regularity assumption on the input. -/
lemma maximalComplex_comp_complexPlane (f : Plane → ℝ) (z : ℂ) :
    maximalComplex (fun w => f (complexPlane w)) z=maximal f (complexPlane z) := by
  rw [maximalComplex_eq_all_radii,maximal]
  apply iSup_congr
  intro r
  apply iSup_congr
  intro hr
  rw [absoluteDiskAverage,absoluteMeasure,withDensity_apply _ measurableSet_ball,
    volume_disk_real z hr.le]
  congr 1
  have h := complexPlane.measurePreserving.setLIntegral_comp_emb
    complexPlane.toMeasurableEquiv.measurableEmbedding (fun x => ENNReal.ofReal |f x|) (Metric.ball z r)
  rw [complexPlane.image_ball] at h
  exact h

lemma maximalComplexReal_comp_complexPlane (f : Plane → ℝ) :
    DiskMaximalTools.maximalComplexReal (fun w => f (complexPlane w)) = fun z => maximalReal f (complexPlane z) := by
  funext z
  exact congrArg ENNReal.toReal (maximalComplex_comp_complexPlane f z)

theorem main_endpoint : EndpointStatement := by
  obtain ⟨C,hC,hendpoint⟩ := SobolevBand.complex_endpoint
  refine ⟨C,hC.le,?_⟩
  intro f g hf hg hw
  let f' := fun z => f (complexPlane z)
  let g' := fun z => complexPlane.symm (g (complexPlane z))
  have hf' : Integrable f' := integrable_comp_complexPlane.mpr hf
  have hg0 : Integrable (fun z => g (complexPlane z)) := integrable_comp_complexPlane.mpr hg
  have hg' : Integrable g' := complexPlane.symm.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hg0
  have hw0 : HasGradient (μ := volume) f g := (hasGradient_iff_hasWeakGradient hf.locallyIntegrable hg).mpr hw
  have hw' : HasGradient (μ := volume) f' g' := hw0.comp_isometry complexPlane
  obtain ⟨hM',G',hG'i,hwG',hbound⟩ := hendpoint f' g' hf' hg' hw'
  have he : maximalComplexReal f'=fun z => maximalReal f (complexPlane z) := maximalComplexReal_comp_complexPlane f
  rw [he] at hM'
  have hM : LocallyIntegrable (maximalReal f) := locallyIntegrable_comp_complexPlane.mp hM'
  let G := fun x => complexPlane (G' (complexPlane.symm x))
  have hG0 : Integrable (fun x => G' (complexPlane.symm x)) := integrable_comp_complexPlane_symm.mpr hG'i
  have hG : Integrable G := complexPlane.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hG0
  have hwG0 := hwG'.comp_isometry complexPlane.symm
  have hwG : HasWeakGradient (maximalReal f) G := by
    apply (hasGradient_iff_hasWeakGradient hM hG).mp
    simpa only [he,complexPlane.apply_symm_apply,LinearIsometryEquiv.symm_symm] using hwG0
  refine ⟨ae_maximal_ne_top hf,hM,inW11Loc_of_gradient hM hG hwG,G,hG,hwG,?_⟩
  rw [show gradientNorm G=∫ z,‖G' z‖ from gradientNorm_comp_complexPlane_symm G']
  exact hbound.trans_eq (congrArg (fun v => C*v) (gradientNorm_comp_complexPlane g))
end CenteredDiskEndpoint

end

end OAI
