import Mathlib

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function

theorem spatialJacobian_time_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : ℝ × E → E} (hX : ContDiff ℝ (⊤:ℕ∞) X) (V : E → E) (t : ℝ)
    (hODE : ∀y,HasDerivAt (fun u => X (u,y)) (V (X (t,y))) t) (y : E) :
    HasDerivAt (fun u => fderiv ℝ (fun z => X (u,z)) y)
      (fderiv ℝ (fun z => V (X (t,z))) y) t := by
  let D := fderiv ℝ X
  let S := fderiv ℝ D (t,y)
  let R : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E
  have hD : ContDiff ℝ (⊤:ℕ∞) D := hX.fderiv_right (by simp)
  have hc (u : ℝ) : fderiv ℝ (fun z => X (u,z)) y=(D (u,y)).comp R := by
    have hd := ((hX.differentiable (by simp) (u,y)).hasFDerivAt).comp y
      ((hasFDerivAt_const u y).prodMk (hasFDerivAt_id y))
    exact hd.fderiv
  have hd := ((hD.differentiable (by simp) (t,y)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  have hdc : HasDerivAt (fun u => (D (u,y)).comp R) ((S (1,0)).comp R) t := by
    simpa only [S,Function.comp_def,id_eq,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,zero_add,add_zero]
      using hd.clm_comp (hasDerivAt_const t R)
  have he : (fun z => D (t,z) (1,0))=fun z => V (X (t,z)) := by
    funext z
    exact (((hX.differentiable (by simp) (t,z)).hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))).unique (hODE z)
  have hh := (((hD.differentiable (by simp) (t,y)).hasFDerivAt).comp y
    ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))).clm_apply
      (hasFDerivAt_const (1,0) y)
  change HasFDerivAt (fun z => D (t,z) (1,0)) _ y at hh
  rw [he] at hh
  have hSym := (hX.contDiffAt (x:=(t,y))).isSymmSndFDerivAt (by simp)
  have heq : (S (1,0)).comp R=fderiv ℝ (fun z => V (X (t,z))) y := by
    rw [hh.fderiv]
    ext v
    simpa [S,D,R,ContinuousLinearMap.comp_apply] using hSym (1,0) (0,v)
  simp_rw [hc]
  exact heq ▸ hdc
end LogConcaveSampling

end

end

end

end OAI
