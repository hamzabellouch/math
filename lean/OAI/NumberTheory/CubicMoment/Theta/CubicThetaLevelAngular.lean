import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCirclePlane
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleInversion
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelPlane

namespace OAI

/-! All nonzero signed angular transformations at primary-level rational cusps,
derived from the actual automorphic theta function by small-circle extraction. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

theorem cubicThetaArithmetic_level_angular {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) {v : ℝ} (hv : 0<v)
    (rev : Bool) {k : ℕ} (hk : 0<k) :
    cubicSymbol q (3*y)*cubicThetaNonconstant
      (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient (cubicThetaCircleOrder rev k))
        (-(3*(x:ℂ)/(q:ℂ)),v)=
      (cubicThetaCircleMultiplier (!rev) (-1/((q:ℂ)^2*(v:ℂ)^2)))^k*
        cubicThetaNonconstant
          (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient (cubicThetaCircleOrder (!rev) k))
            (3*(y:ℂ)/(q:ℂ),(norm q*v)⁻¹) := by
  let z := -(3*(x:ℂ)/(q:ℂ))
  let z' := 3*(y:ℂ)/(q:ℂ)
  let χ := cubicSymbol q (3*y)
  let fl := fun r : ℝ => fourierCoeff
    (fun t => cubicThetaArithmeticPlane (z+cubicThetaSignedCircle rev 1 r t,v)) (k:ℤ)/(r:ℂ)^k
  let fr := fun r : ℝ => fourierCoeff
    (fun t => cubicThetaArithmeticPlane
      (z'+cubicThetaSignedCircle (!rev) (cubicThetaCircleDualDirection (q:ℂ) v r) r t,
        cubicThetaCircleDualHeight (q:ℂ) v r)) (k:ℤ)/(r:ℂ)^k
  have hqC : (q:ℂ)≠0 := fun he => primary_ne_zero hq (Subtype.ext he)
  have hv' : 0<(norm q*v)⁻¹ := inv_pos.mpr (mul_pos (norm_pos_of_ne_zero (primary_ne_zero hq)) hv)
  have heq (r : ℝ) : fr r=χ*fl r := by
    have he : (fun t => cubicThetaArithmeticPlane
        (z'+cubicThetaSignedCircle (!rev) (cubicThetaCircleDualDirection (q:ℂ) v r) r t,
          cubicThetaCircleDualHeight (q:ℂ) v r))=
        fun t => χ*cubicThetaArithmeticPlane (z+cubicThetaSignedCircle rev 1 r t,v) := by
      funext t
      have H := cubicThetaArithmeticPlane_level hq x y hxy (cubicThetaSignedCircle rev 1 r t) hv
      rw [cubicThetaInversion_circle] at H
      simpa only [Prod.fst,Prod.snd,sub_eq_add_neg,add_comm,z,z',χ] using H
    dsimp only [fr,fl]
    rw [he,fourierCoeff.const_mul]
    ring
  let A := (2*Real.pi*Complex.I)^k/(k.factorial:ℂ)
  have hl : Tendsto fl (𝓝[Set.Ioi 0] 0)
      (𝓝 (A*cubicThetaNonconstant
        (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient (cubicThetaCircleOrder rev k)) (z,v))) := by
    have H := cubicThetaArithmeticPlane_circle_limit z rev hk
      (d := fun _ : ℝ => (1:ℂ)) (v := fun _ : ℝ => v) tendsto_const_nhds tendsto_const_nhds hv
    have hm : cubicThetaCircleMultiplier rev 1=1 := by cases rev <;> simp [cubicThetaCircleMultiplier]
    simpa only [hm,one_pow,mul_one,A,fl] using H
  have hr : Tendsto fr (𝓝[Set.Ioi 0] 0)
      (𝓝 (A*(cubicThetaCircleMultiplier (!rev) (-1/((q:ℂ)^2*(v:ℂ)^2)))^k*
        cubicThetaNonconstant
          (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient (cubicThetaCircleOrder (!rev) k))
            (z',(norm q*v)⁻¹))) := by
    have H := cubicThetaArithmeticPlane_circle_limit z' (!rev) hk
      (cubicThetaCircleDualDirection_limit hqC hv) (cubicThetaCircleDualHeight_limit hqC hv)
      (show 0<(Complex.normSq (q:ℂ)*v)⁻¹ by simpa only [norm] using hv')
    simpa only [norm,A,fr] using H
  have H := tendsto_nhds_unique hr ((tendsto_const_nhds.mul hl).congr' (Eventually.of_forall (fun r => (heq r).symm)))
  have hA : A≠0 := by
    apply div_ne_zero
    · apply pow_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    · exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hA
  change A*(χ*cubicThetaNonconstant
      (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient (cubicThetaCircleOrder rev k)) (z,v))=_
  calc
    _ = χ*(A*cubicThetaNonconstant
        (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient (cubicThetaCircleOrder rev k)) (z,v)) := by ring
    _ = _ := H.symm
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
