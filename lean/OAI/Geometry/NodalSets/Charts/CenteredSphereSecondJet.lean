import Mathlib.Analysis.Calculus.ContDiff.Comp
import OAI.Geometry.NodalSets.Charts.CenteredSphereChart

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma centeredSphereChart_frame_function (p : Base) :
    sphereChartDerivative p = fderiv ℝ
      (stereoInvFunAux (-(p : AmbientBase)) ∘ (centeredSphereIsometry p)) := by
  funext y
  rw [sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial),
    centeredSphereChart_inverse]

lemma centeredSphereChart_second (p : Base) (v w : BaseModel) :
    fderiv ℝ (sphereChartDerivative p) 0 w v = -⟪w,v⟫ • (p : AmbientBase) := by
  rw [centeredSphereChart_frame_function]
  have h := (centeredSphereIsometry p).toContinuousLinearMap.iteratedFDeriv_comp_right
    (contDiff_stereoInvFunAux (v := -(p : AmbientBase)) (m := ∞)) (0:BaseModel)
    (i := 2) (show (2:WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have he := congrArg (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ BaseModel) AmbientBase ↦
    D ![w,v]) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,map_zero] at he
  calc
    _ = fderiv ℝ (fderiv ℝ (stereoInvFunAux (-(p : AmbientBase)))) 0
        (centeredSphereIsometry p w) (centeredSphereIsometry p v) := he
    _ = _ := by
      rw [stereoInvFunAux_second_fderiv,(centeredSphereIsometry p).inner_map_map]
      simp

local instance : ContinuousSMul ℝ AmbientBase := IsBoundedSMul.continuousSMul

lemma centeredSphereChart_direction_hasFDerivAt (p : Base) (v : BaseModel) :
    HasFDerivAt (fun y ↦ sphereChartDerivative p y v)
      ((-(innerSL ℝ v)).smulRight (p : AmbientBase)) 0 := by
  have hd := (sphereChartDerivative_smooth_at p
    (y := 0) (by rw [centeredSphereChart_target]; trivial)).differentiableAt (by simp)
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v (0:BaseModel))
  convert! h using 1
  ext w
  simp [centeredSphereChart_second,real_inner_comm]

end
end Yau.Target

end OAI
