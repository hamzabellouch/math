import Mathlib
import OAI.Analysis.AffineBernstein.PositiveDerivative

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Orthogonal tangential projection when `e` is a unit vector. -/
def tangentProjection (e v : E) : E := v - inner ℝ e v • e

/- The ambient extension of the spherical gradient of a degree-one support function. -/
def sphereGradient (H : E → ℝ) (e : E) : E := gradient H e - H e • e

/- The round covariant derivative, using tangential projection of the ambient derivative. -/
def roundDerivative (V : E → E) (e v : E) : E :=
  tangentProjection e (fderiv ℝ V e v)

/- The spherical Hessian evaluated on tangent vectors. -/
def sphereHessian (H : E → ℝ) (e v w : E) : ℝ :=
  inner ℝ (roundDerivative (sphereGradient H) e v) w

def sphereRadius (H : E → ℝ) (e v w : E) : ℝ :=
  sphereHessian H e v w + H e * inner ℝ v w

omit [CompleteSpace E] in
theorem inner_tangentProjection {e w : E} (hw : inner ℝ e w = 0) (v : E) :
    inner ℝ (tangentProjection e v) w = inner ℝ v w := by
  simp [tangentProjection, inner_sub_left, real_inner_smul_left, hw]

omit [CompleteSpace E] in
theorem tangentProjection_eq {e v : E} (hv : inner ℝ e v = 0) :
    tangentProjection e v = v := by simp [tangentProjection, hv]

theorem gauss_reconstruction (H : E → ℝ) (e : E) :
    gradient H e = H e • e + sphereGradient H e := by
  simp [sphereGradient]

/- `∇²_S h + h Id` is the restriction of the ambient Hessian of the
one-homogeneous support function. -/
theorem sphereRadius_eq_hessian {H : E → ℝ} {e : E}
    (hh : ContDiffAt ℝ ∞ H e) (v w : E) (hw : inner ℝ e w = 0) :
    sphereRadius H e v w = fderiv ℝ (fderiv ℝ H) e v w := by
  have hG := (contDiffAt_gradient hh).differentiableAt (by simp)
  have hH := hh.differentiableAt (by simp)
  have hd := hG.hasFDerivAt.sub (hH.hasFDerivAt.smul (hasFDerivAt_id e))
  change HasFDerivAt (fun x => gradient H x - H x • x) _ e at hd
  unfold sphereRadius sphereHessian roundDerivative sphereGradient
  rw [inner_tangentProjection hw, hd.fderiv]
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, inner_add_left, real_inner_smul_left, id_eq, hw,
    mul_zero]
  rw [inner_fderiv_gradient hh]
  ring

/- The standard projected local extension of a tangent vector. At a unit `e`,
its round covariant derivative vanishes if `v` is tangent at `e`. -/
theorem hasFDerivAt_tangentProjection (e v : E) :
    HasFDerivAt (fun x => tangentProjection x v)
      (-(inner ℝ e v • ContinuousLinearMap.id ℝ E +
        (InnerProductSpace.toDual ℝ E v).smulRight e)) e := by
  have hd := (hasFDerivAt_const v e).sub
    ((InnerProductSpace.toDual ℝ E v).hasFDerivAt.smul (hasFDerivAt_id e))
  convert hd using 1
  · ext x; simp [tangentProjection, real_inner_comm]
  · simp [real_inner_comm]

/- The covariant derivative of an ambient two-tensor restricted to the sphere.
The arguments `u,v,w` are tangent at the unit point of evaluation. The projected
constant extensions of `v,w` have zero covariant derivative there. -/
def roundTensorDerivative (A : E → E →L[ℝ] E →L[ℝ] ℝ) (e u v w : E) : ℝ :=
  fderiv ℝ (fun x => A x (tangentProjection x v) (tangentProjection x w)) e u

theorem roundTensorDerivative_eq {A : E → E →L[ℝ] E →L[ℝ] ℝ} {e : E}
    (hA : DifferentiableAt ℝ A e)
    (hrad : ∀ v, A e e v = 0 ∧ A e v e = 0)
    (u v w : E) (hv : inner ℝ e v = 0) (hw : inner ℝ e w = 0) :
    roundTensorDerivative A e u v w = fderiv ℝ A e u v w := by
  have hd := (hA.hasFDerivAt.clm_apply (hasFDerivAt_tangentProjection e v)).clm_apply
    (hasFDerivAt_tangentProjection e w)
  unfold roundTensorDerivative
  rw [hd.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, neg_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply_apply,
    tangentProjection_eq hv, tangentProjection_eq hw, hv, hw,
    zero_smul, zero_add, map_neg, map_smul,
    (hrad v).2, (hrad w).1, smul_zero, neg_zero]

/- Codazzi for the radius tensor of a smooth one-homogeneous support function.
The radial Hessian identity is precisely the derivative of Euler's identity;
there is no assumed Codazzi equation. -/
theorem supportRadius_codazzi {H : E → ℝ} {e : E}
    (hh : ContDiffAt ℝ ∞ H e)
    (hrad : ∀ v, fderiv ℝ (fderiv ℝ H) e v e = 0)
    (u v w : E) (hu : inner ℝ e u = 0) (hv : inner ℝ e v = 0)
    (hw : inner ℝ e w = 0) :
    roundTensorDerivative (fderiv ℝ (fderiv ℝ H)) e u v w =
      roundTensorDerivative (fderiv ℝ (fderiv ℝ H)) e v u w := by
  have hrad' (q : E) : fderiv ℝ (fderiv ℝ H) e e q = 0 ∧
      fderiv ℝ (fderiv ℝ H) e q e = 0 := by
    refine ⟨?_, hrad q⟩
    rw [(hh.isSymmSndFDerivAt (by simp)).eq e q]
    exact hrad q
  have hd := ((hh.fderiv_right (m := ∞) (by simp)).fderiv_right
    (m := ∞) (by simp)).differentiableAt (by simp)
  rw [roundTensorDerivative_eq hd hrad' u v w hv hw,
    roundTensorDerivative_eq hd hrad' v u w hu hw]
  exact congrArg (fun L : E →L[ℝ] ℝ => L w)
    (((hh.fderiv_right (m := ∞) (by simp)).isSymmSndFDerivAt (by simp)).eq u v)

end AffineBernstein
end

end OAI
