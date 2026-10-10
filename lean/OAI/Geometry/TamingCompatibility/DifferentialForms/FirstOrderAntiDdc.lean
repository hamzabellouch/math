import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Linear

namespace OAI


noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dc (J : E → E →L[ℝ] E) (f : E → ℝ) (x : E) : Form (E := E) 1 :=
  ofSubsingletonLIE (0 : Fin 1) (-(fderiv ℝ f x).comp (J x))

lemma extDeriv_dc_apply {J : E → E →L[ℝ] E} {f : E → ℝ} {x : E}
    (hdf : DifferentiableAt ℝ (fderiv ℝ f) x) (hJ : DifferentiableAt ℝ J x) (u v : E) :
    extDeriv (dc J f) x ![u,v] =
      -(fderiv ℝ (fderiv ℝ f) x u (J x v)) + fderiv ℝ (fderiv ℝ f) x v (J x u) +
      fderiv ℝ f x ((fderiv ℝ J x v) u - (fderiv ℝ J x u) v) := by
  let L := (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.hasFDerivAt.comp x ((hdf.hasFDerivAt.clm_comp hJ.hasFDerivAt).neg)
  have hd : fderiv ℝ (dc J f) x =
      L.comp (-((ContinuousLinearMap.compL ℝ E E ℝ (fderiv ℝ f x)).comp (fderiv ℝ J x) +
        ((ContinuousLinearMap.compL ℝ E E ℝ).flip (J x)).comp (fderiv ℝ (fderiv ℝ f) x))) :=
    h.fderiv
  rw [extDeriv_one,hd]
  simp [L,ofSubsingletonLIE,map_sub]
  ring

lemma anti_ddc_first_order {J : E → E →L[ℝ] E} {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hJ : DifferentiableAt ℝ J x)
    (hJJ : ∀ v, J x (J x v) = -v) (u v : E) :
    (extDeriv (dc J f) x ![u,v] - extDeriv (dc J f) x ![J x u,J x v])/2 =
      (1/2:ℝ) * fderiv ℝ f x
        ((fderiv ℝ J x v) u - (fderiv ℝ J x u) v +
          (fderiv ℝ J x (J x u)) (J x v) - (fderiv ℝ J x (J x v)) (J x u)) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [extDeriv_dc_apply hdf hJ,extDeriv_dc_apply hdf hJ,hJJ,hJJ]
  simp only [map_neg,neg_neg,map_sub,map_add]
  have hsym := hf.isSymmSndFDerivAt (by simp)
  rw [hsym (J x u) v,hsym (J x v) u]
  ring
end TamingCompatibility.ExteriorForms

end

end OAI
