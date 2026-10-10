import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import OAI.Geometry.NodalSets.Model

namespace OAI

namespace Yau.Target
open scoped ContDiff RealInnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def stereoReciprocal (x : E) : ℝ := (‖x‖^2+4)⁻¹

def stereoNumerator (v x : E) : E := (4:ℝ) • x + (‖x‖^2-4) • v

lemma stereoReciprocal_hasFDerivAt (x : E) :
    HasFDerivAt stereoReciprocal
      (-(stereoReciprocal x)^2 • ((2:ℝ) • innerSL ℝ x)) x := by
  have hd := (hasFDerivAt_inv (by positivity : ‖x‖^2+4 ≠ 0)).comp x
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (4:ℝ))
  convert! hd using 1
  ext w
  simp [stereoReciprocal,inv_pow,smul_eq_mul,nsmul_eq_mul]
  ring

lemma stereoNumerator_hasFDerivAt (v x : E) :
    HasFDerivAt (stereoNumerator v)
      ((4:ℝ) • ContinuousLinearMap.id ℝ E + ((2:ℝ) • innerSL ℝ x).smulRight v) x := by
  convert! ((hasFDerivAt_id x).const_smul (4:ℝ)).add
    (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const (4:ℝ)).smul_const v) using 1
  ext w
  simp [nsmul_eq_mul]

lemma stereoInvFunAux_fderiv (v x w : E) :
    fderiv ℝ (stereoInvFunAux v) x w =
      (-2 * stereoReciprocal x^2 * ⟪x,w⟫) • stereoNumerator v x +
      stereoReciprocal x • ((4:ℝ) • w + (2*⟪x,w⟫) • v) := by
  have hd := (stereoReciprocal_hasFDerivAt x).smul (stereoNumerator_hasFDerivAt v x)
  change HasFDerivAt (stereoInvFunAux v) _ x at hd
  rw [hd.fderiv]
  simp only [smul_apply,add_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_eq_mul]
  rw [add_comm]
  congr 1
  congr 1
  ring

lemma stereoReciprocal_zero_hasFDerivAt :
    HasFDerivAt (stereoReciprocal : E → ℝ) (0 : E →L[ℝ] ℝ) (0:E) := by
  simpa [stereoReciprocal] using (stereoReciprocal_hasFDerivAt (0:E))

lemma stereoInvFunAux_second (v w u : E) :
    fderiv ℝ (fun x ↦ fderiv ℝ (stereoInvFunAux v) x w) 0 u = ⟪u,w⟫ • v := by
  simp_rw [stereoInvFunAux_fderiv]
  have hb : HasFDerivAt (fun x : E ↦ ⟪x,w⟫) (innerSL ℝ w) 0 := by
    convert! (innerSL ℝ w).hasFDerivAt (x := (0:E)) using 1
    funext y
    exact (real_inner_comm y w).symm
  have hA := (((stereoReciprocal_zero_hasFDerivAt (E := E)).pow 2).const_mul (-2:ℝ)).mul hb
  have hB := (hasFDerivAt_const ((4:ℝ) • w) (0:E)).add ((hb.const_mul (2:ℝ)).smul_const v)
  have hd := (hA.smul (stereoNumerator_hasFDerivAt v (0:E))).add
    (stereoReciprocal_zero_hasFDerivAt.smul hB)
  change HasFDerivAt (fun x : E ↦
    (-2 * stereoReciprocal x^2 * ⟪x,w⟫) • stereoNumerator v x +
      stereoReciprocal x • ((4:ℝ) • w + (2*⟪x,w⟫) • v)) _ 0 at hd
  rw [hd.fderiv]
  simp [stereoReciprocal,stereoNumerator,smul_smul,real_inner_comm]
  module

lemma stereoInvFunAux_second_fderiv (v w u : E) :
    fderiv ℝ (fderiv ℝ (stereoInvFunAux v)) 0 u w = ⟪u,w⟫ • v := by
  have hd := (contDiff_stereoInvFunAux (v := v) (m := ∞)).fderiv_right
    (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)
  have he := (hd.differentiable (by simp) (0:E)).hasFDerivAt.clm_apply
    (hasFDerivAt_const w (0:E))
  have h := congrArg (fun L : E →L[ℝ] E ↦ L u) he.fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at h
  rw [← h]
  exact stereoInvFunAux_second v w u

end
end Yau.Target

end OAI
