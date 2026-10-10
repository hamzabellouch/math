import OAI.Geometry.SurfaceImmersion.Geometry.LowerDimensionalImage

namespace OAI

/-! A chart of the critical-point equation for an affine perturbation of
a quadratic phase along a regular plane curve. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry

abbrev CurvePlane := ℝ × ℝ

def curvePhaseVelocity (u v : ℝ → CurvePlane) (L t : ℝ) (ell : CurvePlane) : ℝ :=
  (ell.1+L*(u t).1)*(v t).1+(ell.2+L*(u t).2)*(v t).2

def curvePhaseAcceleration (u v w : ℝ → CurvePlane) (L t : ℝ) (ell : CurvePlane) : ℝ :=
  L*((v t).1^2+(v t).2^2)+(ell.1+L*(u t).1)*(w t).1+
    (ell.2+L*(u t).2)*(w t).2

def curvePhaseParameterGraph (u v : ℝ → CurvePlane) (L : ℝ)
    (x : CurvePlane) : CurvePlane :=
  ((-x.2*(v x.1).2-L*((u x.1).1*(v x.1).1+(u x.1).2*(v x.1).2))/(v x.1).1,x.2)

lemma curvePhaseParameterGraph_eq {u v : ℝ → CurvePlane} {L t : ℝ} {ell : CurvePlane}
    (hspeed : (v t).1 ≠ 0) (hcrit : curvePhaseVelocity u v L t ell = 0) :
    curvePhaseParameterGraph u v L (t,ell.2) = ell := by
  apply Prod.ext
  · change (-ell.2*(v t).2-L*((u t).1*(v t).1+(u t).2*(v t).2))/(v t).1 = ell.1
    apply (div_eq_iff hspeed).mpr
    dsimp [curvePhaseVelocity] at hcrit
    nlinarith
  · rfl

lemma curvePhaseParameterGraph_deriv_zero {u v w : ℝ → CurvePlane}
    {L t : ℝ} {ell : CurvePlane}
    (hu : HasDerivAt u (v t) t) (hv : HasDerivAt v (w t) t)
    (hspeed : (v t).1 ≠ 0)
    (hcrit : curvePhaseVelocity u v L t ell = 0)
    (hdeg : curvePhaseAcceleration u v w L t ell = 0) :
    HasDerivAt (fun s => curvePhaseParameterGraph u v L (s,ell.2)) 0 t := by
  have hu1 : HasDerivAt (fun s => (u s).1) (v t).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have hu2 : HasDerivAt (fun s => (u s).2) (v t).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have hv1 : HasDerivAt (fun s => (v s).1) (w t).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hv2 : HasDerivAt (fun s => (v s).2) (w t).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hn := (hv2.const_mul (-ell.2)).sub
    (((hu1.mul hv1).add (hu2.mul hv2)).const_mul L)
  have hquot := hn.div hv1 hspeed
  have hnval : -ell.2*(v t).2-L*((u t).1*(v t).1+(u t).2*(v t).2) =
      ell.1*(v t).1 := by
    dsimp [curvePhaseVelocity] at hcrit
    nlinarith
  have hnprime : -ell.2*(w t).2-
      L*(((v t).1*(v t).1+(u t).1*(w t).1)+
        ((v t).2*(v t).2+(u t).2*(w t).2)) = ell.1*(w t).1 := by
    dsimp [curvePhaseAcceleration] at hdeg
    nlinarith
  have hd := hquot.prodMk (hasDerivAt_const t ell.2)
  convert hd using 1
  · rfl
  · change (0 : CurvePlane) =
      (((-ell.2*(w t).2-L*(((v t).1*(v t).1+(u t).1*(w t).1)+
      ((v t).2*(v t).2+(u t).2*(w t).2)))*(v t).1-
      (-ell.2*(v t).2-L*((u t).1*(v t).1+(u t).2*(v t).2))*(w t).1)/
        ((v t).1)^2,0)
    rw [hnval,hnprime]
    ext <;> dsimp
    ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
