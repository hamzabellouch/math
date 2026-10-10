import OAI.Analysis.CircleDomains.Sobolev.WeakCovectorGradient
import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneSobolev

namespace OAI

/-! Identify the weak gradient of an actual local Sobolev witness with
its classical differential when the represented scalar is smooth. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def localSobolevChangeDomain {U V : Set EuclideanPlane} {f : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 f U) (h : U = V) :
    DeGiorgi.MemW1pWitness 2 f V where
  memLp := by simpa only [← h] using W.memLp
  weakGrad := W.weakGrad
  weakGrad_component_memLp := fun i => by simpa only [← h] using W.weakGrad_component_memLp i
  isWeakGrad := by simpa only [← h] using W.isWeakGrad

 theorem smooth_weak_gradient_ae {U : Set EuclideanPlane} (hU : IsOpen U)
    {f : EuclideanPlane → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hD : MemLp (fderiv ℝ f) 2 (volume.restrict U))
    (W : DeGiorgi.MemW1pWitness 2 f U) :
    W.weakGrad =ᵐ[volume.restrict U] fun x => planeCovectorGradient (fderiv ℝ f x) := by
  have hp (i : Fin 2) : MemLp
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 (volume.restrict U) := by
    have hm : Continuous (fun L : EuclideanPlane →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) :=
      continuous_id.clm_apply continuous_const
    apply hD.norm.of_le (hm.comp_aestronglyMeasurable hD.aestronglyMeasurable)
    exact Eventually.of_forall (fun x => by
      simpa only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_norm] using
        (fderiv ℝ f x).le_opNorm (EuclideanSpace.single i 1))
  let V := smoothPlaneSobolevWitness hU hf W.memLp hp
  have he := W.ae_eq hU V
  filter_upwards [he] with x hx
  rw [hx]
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;> simp [V, smoothPlaneSobolevWitness, planeCovectorGradient]

end CircleDomainRigidity

end

end OAI
