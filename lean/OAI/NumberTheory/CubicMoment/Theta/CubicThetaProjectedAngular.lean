import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedPlane
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleInversion

namespace OAI

/-! All nonzero angular orders of the actual primary-projected cusp
transformation. No Voronoi identity is assumed. -/
noncomputable section
open Filter
open scoped Topology MatrixGroups
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

theorem cubicThetaSelected_projected_angular (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {v : ℝ} (hv : 0<v)
    (rev : Bool) {k : ℕ} (hk : 0<k) :
    cubicThetaNonconstant
      (cubicThetaAngularCoefficient (cubicThetaProjectedCoefficient g hc) (cubicThetaCircleOrder rev k))
        (cubicThetaPrimaryDualCenter g,v)=
      (cubicThetaCircleMultiplier (!rev) (-1/((g 1 0:ℂ)^2*(v:ℂ)^2)))^k*
        cubicThetaNonconstant
          (cubicThetaAngularCoefficient cubicThetaSelectedCoefficient (cubicThetaCircleOrder (!rev) k))
            (cubicThetaPrimaryCuspCenter g,(norm (g 1 0)*v)⁻¹) := by
  let z := cubicThetaPrimaryDualCenter g
  let z' := cubicThetaPrimaryCuspCenter g
  let q : ℂ := (g 1 0:ℂ)
  let fl := fun r : ℝ => fourierCoeff
    (fun t => cubicThetaProjectedPlane g hc (z+cubicThetaSignedCircle rev 1 r t,v)) (k:ℤ)/(r:ℂ)^k
  let fr := fun r : ℝ => fourierCoeff
    (fun t => cubicThetaNonconstant cubicThetaSelectedCoefficient
      (z'+cubicThetaSignedCircle (!rev) (cubicThetaCircleDualDirection q v r) r t,
        cubicThetaCircleDualHeight q v r)) (k:ℤ)/(r:ℂ)^k
  have hq : q≠0 := fun he => primary_ne_zero hc (Subtype.ext he)
  have heq (r : ℝ) : fr r=fl r := by
    have he : (fun t => cubicThetaNonconstant cubicThetaSelectedCoefficient
        (z'+cubicThetaSignedCircle (!rev) (cubicThetaCircleDualDirection q v r) r t,
          cubicThetaCircleDualHeight q v r))=
        fun t => cubicThetaProjectedPlane g hc (z+cubicThetaSignedCircle rev 1 r t,v) := by
      funext t
      have H := cubicThetaSelected_projected_plane g hc (cubicThetaSignedCircle rev 1 r t) hv
      rw [cubicThetaInversion_circle] at H
      simpa only [Prod.fst,Prod.snd,add_comm,z,z',q] using H
    dsimp only [fr,fl]
    rw [he]
  let A := (2*Real.pi*Complex.I)^k/(k.factorial:ℂ)
  have hl : Tendsto fl (𝓝[Set.Ioi 0] 0)
      (𝓝 (A*cubicThetaNonconstant
        (cubicThetaAngularCoefficient (cubicThetaProjectedCoefficient g hc) (cubicThetaCircleOrder rev k))
        (z,v))) := by
    have H := cubicThetaProjectedPlane_circle_limit g hc z rev hk
      (d := fun _ : ℝ => (1:ℂ)) (v := fun _ : ℝ => v) tendsto_const_nhds tendsto_const_nhds hv
    have hm : cubicThetaCircleMultiplier rev 1=1 := by cases rev <;> simp [cubicThetaCircleMultiplier]
    simpa only [hm,one_pow,mul_one,A,fl] using H
  have hbound (n : Eisenstein) (hn : n≠0) : ‖cubicThetaSelectedCoefficient n‖≤81*norm n :=
    (cubicThetaSelectedCoefficient_norm n).trans
      (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))
  have hr : Tendsto fr (𝓝[Set.Ioi 0] 0)
      (𝓝 (A*(cubicThetaCircleMultiplier (!rev) (-1/(q^2*(v:ℂ)^2)))^k*
        cubicThetaNonconstant
          (cubicThetaAngularCoefficient cubicThetaSelectedCoefficient (cubicThetaCircleOrder (!rev) k))
            (z',(norm (g 1 0)*v)⁻¹))) := by
    have H := cubicThetaCircleActual_limit (by norm_num : (0:ℝ)≤81) hbound z' (!rev) k
      (cubicThetaCircleDualDirection_limit hq hv) (cubicThetaCircleDualHeight_limit hq hv)
      (inv_pos.mpr (mul_pos (norm_pos_of_ne_zero (primary_ne_zero hc)) hv))
    simpa only [norm,A,fr,q] using H
  have he := tendsto_nhds_unique hr (hl.congr' (Eventually.of_forall (fun r => (heq r).symm)))
  have hA : A≠0 := by
    apply div_ne_zero
    · apply pow_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    · exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hA
  change A*cubicThetaNonconstant
    (cubicThetaAngularCoefficient (cubicThetaProjectedCoefficient g hc) (cubicThetaCircleOrder rev k)) (z,v)=_
  calc
    _ = A*(cubicThetaCircleMultiplier (!rev) (-1/(q^2*(v:ℂ)^2)))^k*
      cubicThetaNonconstant
        (cubicThetaAngularCoefficient cubicThetaSelectedCoefficient (cubicThetaCircleOrder (!rev) k))
          (z',(norm (g 1 0)*v)⁻¹) := he.symm
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
