import OAI.Analysis.CircleDomains.Sobolev.SobolevRepresentative
import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

namespace OAI

/-! Smoothness on an open plane set and integrable partial derivatives give
an actual Sobolev witness. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem integrable_plane_mul_of_continuousOn
    {U : Set EuclideanPlane} (hU : IsOpen U) {f φ : EuclideanPlane → ℝ}
    (hf : ContinuousOn f U) (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ U) : Integrable (fun x => f x * φ x) :=
  ((hf.mul hφ.continuousOn).continuous_of_tsupport_subset hU
    (tsupport_mul_subset_right.trans hsub)).integrable_of_hasCompactSupport hs.mul_left

 theorem weakPartial_of_smooth_on
    {U : Set EuclideanPlane} (hU : IsOpen U) {f : EuclideanPlane → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) f U := by
  intro φ hφ hs hsub
  let v : EuclideanPlane := EuclideanSpace.single i 1
  have hdf : ContinuousOn (fun x => fderiv ℝ f x v) U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_plane_mul_of_continuousOn hU hdf hφ.continuous hs hsub)
    (integrable_plane_mul_of_continuousOn hU hf.continuousOn hdφ
      (hs.fderiv_apply (𝕜 := ℝ) v) ((tsupport_fderiv_apply_subset ℝ v).trans hsub))
    (integrable_plane_mul_of_continuousOn hU hf.continuousOn hφ.continuous hs hsub)
    (fun x hx => (hf.contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt (by norm_num))
    (fun x _ => hφ.differentiable (by simp) x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hn : x ∉ tsupport (fun y => fderiv ℝ φ y v) :=
      fun h => hx (hsub ((tsupport_fderiv_apply_subset ℝ v) h))
    rw [image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y v) hn, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h)), mul_zero])]
  exact he

 def smoothPlaneSobolevWitness
    {U : Set EuclideanPlane} (hU : IsOpen U) {f : EuclideanPlane → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (hL : MemLp f 2 (volume.restrict U))
    (hD : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
      2 (volume.restrict U)) : DeGiorgi.MemW1pWitness 2 f U where
  memLp := hL
  weakGrad := fun x => WithLp.toLp 2 (fun i => fderiv ℝ f x (EuclideanSpace.single i 1))
  weakGrad_component_memLp := hD
  isWeakGrad := weakPartial_of_smooth_on hU hf

end CircleDomainRigidity

namespace DeGiorgi

 def MemW1pWitness.sub
    {U : Set CircleDomainRigidity.EuclideanPlane} {u v : CircleDomainRigidity.EuclideanPlane → ℝ}
    (hu : MemW1pWitness 2 u U) (hv : MemW1pWitness 2 v U) :
    MemW1pWitness 2 (fun x => u x - v x) U :=
  (hu.add (hv.smul (-1))).congr_ae (Eventually.of_forall fun x => by ring)

end DeGiorgi

end

end OAI
