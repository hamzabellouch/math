import OAI.Analysis.CircleDomains.Sobolev.WeakPairL2
import OAI.Analysis.CircleDomains.Sobolev.WeakBarrierEstimate

namespace OAI

/-! Measurability of the actual barrier differential follows from the
two scalar Sobolev witnesses and the reference differential. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem continuous_plane_covector_comp : Continuous
    (fun p : (EuclideanPlane →L[ℝ] ℝ) × (EuclideanPlane →L[ℝ] EuclideanPlane) => p.1.comp p.2) :=
  ((ContinuousLinearMap.compL ℝ EuclideanPlane EuclideanPlane ℝ).continuous.comp
    continuous_fst).clm_apply continuous_snd

 theorem joint_barrier_differential_measurable {U : Set EuclideanPlane}
    {u v : EuclideanPlane → ℝ} (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    {H : EuclideanPlane → EuclideanPlane} (hH : AEStronglyMeasurable H (volume.restrict U))
    {DH : EuclideanPlane → EuclideanPlane →L[ℝ] EuclideanPlane}
    (hDH : AEStronglyMeasurable DH (volume.restrict U))
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ) :
    AEStronglyMeasurable (fun x =>
      (fderiv ℝ Φ (planePair (u x) (v x))).comp
        (weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x))-
      (fderiv ℝ Φ (H x)).comp (DH x)) (volume.restrict U) := by
  have ha := ((hΦ.continuous_fderiv one_ne_zero).comp
    (continuous_planePair hu hv)).aestronglyMeasurable (μ := volume) |>.restrict (s := U)
  have hb := (hΦ.continuous_fderiv one_ne_zero).comp_aestronglyMeasurable hH
  have hd := continuous_weakPairDifferential.comp_aestronglyMeasurable
    (Wu.weakGrad_memLp.aestronglyMeasurable.prodMk Wv.weakGrad_memLp.aestronglyMeasurable)
  exact (continuous_plane_covector_comp.comp_aestronglyMeasurable (ha.prodMk hd)).sub
    (continuous_plane_covector_comp.comp_aestronglyMeasurable (hb.prodMk hDH))

end CircleDomainRigidity

end

end OAI
