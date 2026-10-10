import OAI.Geometry.NodalSets.Charts.CenteredSphereSecondJet
import OAI.Geometry.NodalSets.Charts.SphereChartConformal
import OAI.Geometry.NodalSets.Elliptic.StereographicArbitrarySecond

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereChart_second_stereo (p : Base) (y u v : BaseModel) :
    fderiv ℝ (sphereChartDerivative p) y u v =
      fderiv ℝ (fun z ↦ fderiv ℝ (stereoInvFunAux (-(p:AmbientBase))) z
        (centeredSphereIsometry p v)) (centeredSphereIsometry p y)
        (centeredSphereIsometry p u) := by
  rw [centeredSphereChart_frame_function]
  have h := (centeredSphereIsometry p).toContinuousLinearMap.iteratedFDeriv_comp_right
    (contDiff_stereoInvFunAux (v := -(p : AmbientBase)) (m := ∞)) y
    (i := 2) (show (2:WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have he := congrArg (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ BaseModel) AmbientBase ↦
    D ![u,v]) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one] at he
  exact he.trans (stereoInvFunAux_second_fderiv_at _ _ _ _)

lemma sphereChart_second_at (p : Base) (y u v : BaseModel) :
    fderiv ℝ (sphereChartDerivative p) y u v =
      (-2/(‖y‖^2+4)) •
        (⟪y,u⟫ • sphereChartDerivative p y v +
         ⟪y,v⟫ • sphereChartDerivative p y u -
         ⟪u,v⟫ • sphereChartDerivative p y y) -
      ((4/(‖y‖^2+4))^2 * ⟪u,v⟫) •
        ((extChartAt (𝓡 4) p).symm y : AmbientBase) := by
  have hF := congrFun (centeredSphereChart_inverse p) y
  simp only [Function.comp_apply] at hF
  rw [sphereChart_second_stereo,stereoInvFunAux_second_at,hF]
  simp only [sphereChartDerivative_stereo,stereoInvFunAux_fderiv,
    stereoReciprocal,stereoNumerator,stereoInvFunAux,
    (centeredSphereIsometry p).norm_map,(centeredSphereIsometry p).inner_map_map,real_inner_self_eq_norm_sq]
  have hd : ‖y‖^2+4 ≠ 0 := by positivity
  ext i
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.neg_apply,smul_eq_mul]
  field_simp
  ring

end
end Yau.Target

end OAI
