import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.PublishedFlowInput

namespace OAI

/-! Interchanging time and a spatial derivative of the local smooth flow
model. This is the first variational equation's calculus step. -/

noncomputable section
open ContinuousLinearMap
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_spatial_deriv_eq_full (H : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (t : ℝ) (x e : Position) :
    fderiv ℝ (fun y => H (t,y)) x e = fderiv ℝ H (t,x) (0,e) := by
  have hp : HasFDerivAt (fun y : Position => (t,y)) (inr ℝ ℝ Position) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hc := ((hH.differentiable (by norm_num)) (t,x)).hasFDerivAt.comp x hp
  change fderiv ℝ (H ∘ (fun y : Position => (t,y))) x e = _
  rw [hc.fderiv]
  rfl

theorem flow_mixed_spatial_derivative (H : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (t : ℝ) (x e : Position) :
    HasDerivAt (fun s => fderiv ℝ (fun y => H (s,y)) x e)
      (fderiv ℝ (fun y => fderiv ℝ H (t,y) (1,0)) x e) t := by
  let p : ℝ × Position := (t,x)
  let v : ℝ × Position := (1,0)
  let w : ℝ × Position := (0,e)
  have hD : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (by norm_num)
  have hd := ((hD.differentiable (by norm_num)) p).hasFDerivAt
  have hp : HasDerivAt (fun s : ℝ => (s,x)) v t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have htime : HasDerivAt (fun s => fderiv ℝ H (s,x) w)
      (fderiv ℝ (fderiv ℝ H) p v w) t := by
    have h := (hd.clm_apply (hasFDerivAt_const w p)).comp_hasDerivAt t hp
    convert h using 1
    · funext s
      rfl
    · simp only [add_apply,ContinuousLinearMap.comp_apply,
        zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  have hspace : fderiv ℝ (fun y => fderiv ℝ H (t,y) v) x e =
      fderiv ℝ (fderiv ℝ H) p w v := by
    have hi : HasFDerivAt (fun y : Position => (t,y)) (inr ℝ ℝ Position) x :=
      (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
    have h := (hd.clm_apply (hasFDerivAt_const v p)).comp x hi
    change fderiv ℝ ((fun z => fderiv ℝ H z v) ∘
      (fun y : Position => (t,y))) x e = _
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply,add_apply,
      zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
    rfl
  have hsym : fderiv ℝ (fderiv ℝ H) p v w = fderiv ℝ (fderiv ℝ H) p w v :=
    hH.contDiffAt.isSymmSndFDerivAt (by norm_num) v w
  change HasDerivAt (fun s => fderiv ℝ (fun y => H (s,y)) x e)
    (fderiv ℝ (fun y => fderiv ℝ H (t,y) v) x e) t
  rw [hspace,←hsym]
  apply htime.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => flow_spatial_deriv_eq_full H hH s x e)

end ContinuumCoulomb

end

end OAI
