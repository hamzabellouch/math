import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHorizontalContinuity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSecondBranchMean

namespace OAI

/-! Exact constant horizontal coefficient of the actual cubed-prime
Hecke correspondence, with both character branches proved to vanish. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeDilation_horizontal_point {p : Eisenstein} (hp : primaryPrime p)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • cubicThetaHorizontalPoint v hv z=
      cubicThetaHorizontalPoint (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv)
        ((p^3:Eisenstein)*z) := by
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) (z,v)=_
  rw [cubicThetaMobius_primeDilation]
  simp only [Subalgebra.coe_pow,norm_pow]
  rfl

lemma cubicThetaPrimeCubeDilation_horizontal_mean {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      cubicThetaHorizontalPoint v hv z))=
    ∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal F (‖(p:ℂ)‖^3*v)
      (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv) z := by
  have he : (fun z : ℂ => F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      cubicThetaHorizontalPoint v hv z))=
      (fun z => cubicThetaSectionHorizontal F (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv)
        ((p^3:Eisenstein)*z)) := by
    funext z
    rw [cubicThetaPrimeCubeDilation_horizontal_point hp]
    rfl
  rw [he]
  exact cubicThetaHorizontal_mul_integral (pow_ne_zero _ hp.2.ne_zero) _
    (cubicThetaSectionHorizontal_periodic F _ _) (cubicThetaSectionHorizontal_integrable F _ _)

theorem cubicThetaPrimeCubeHecke_horizontal_mean {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal (cubicThetaPrimeCubeHecke hp F) v hv z)=
      (∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal F (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv) z)+
      (norm (p^3):ℂ)*(∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3)) z) := by
  let D := fun z => F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
    cubicThetaHorizontalPoint v hv z)
  let B := fun z => cubicThetaPrimeCubeBottomFunctionSum hp F.val (cubicThetaHorizontalPoint v hv z)
  let U := fun z => cubicThetaPrimeCubeUnitFunctionSum hp 1 F.val (cubicThetaHorizontalPoint v hv z)
  let V := fun z => cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
    (cubicThetaHorizontalPoint v hv z)
  have hD : IntegrableOn D cubicThetaHorizontalCell := cubicThetaPrimeCubeDilation_horizontal_integrable hp F v hv
  have hB : IntegrableOn B cubicThetaHorizontalCell := cubicThetaPrimeCubeBottom_horizontal_integrable hp F v hv
  have hU : IntegrableOn U cubicThetaHorizontalCell := cubicThetaPrimeCubeUnit_horizontal_integrable hp 1 F v hv
  have hV : IntegrableOn V cubicThetaHorizontalCell := cubicThetaPrimeCubeUnit_horizontal_integrable hp _ F v hv
  have he : (fun z => cubicThetaSectionHorizontal (cubicThetaPrimeCubeHecke hp F) v hv z)=D+B+U+V := by
    funext z
    exact cubicThetaPrimeCubeHecke_functionOperator hp F (cubicThetaHorizontalPoint v hv z)
  have hDB : integral (volume.restrict cubicThetaHorizontalCell) (D+B)=
      integral (volume.restrict cubicThetaHorizontalCell) D+integral (volume.restrict cubicThetaHorizontalCell) B :=
    integral_add hD hB
  have hDBU : integral (volume.restrict cubicThetaHorizontalCell) (D+B+U)=
      integral (volume.restrict cubicThetaHorizontalCell) (D+B)+integral (volume.restrict cubicThetaHorizontalCell) U :=
    integral_add (hD.add hB) hU
  have hDBUV : integral (volume.restrict cubicThetaHorizontalCell) (D+B+U+V)=
      integral (volume.restrict cubicThetaHorizontalCell) (D+B+U)+integral (volume.restrict cubicThetaHorizontalCell) V :=
    integral_add ((hD.add hB).add hU) hV
  rw [he,hDBUV,hDBU,hDB]
  change (∫ z in cubicThetaHorizontalCell,D z)+(∫ z in cubicThetaHorizontalCell,B z)+
    (∫ z in cubicThetaHorizontalCell,U z)+(∫ z in cubicThetaHorizontalCell,V z)=_
  rw [show (∫ z in cubicThetaHorizontalCell,U z)=0 from cubicThetaPrimeCubeFirstBranch_mean hp F v hv,
    show (∫ z in cubicThetaHorizontalCell,V z)=0 from cubicThetaPrimeCubeSecondBranch_mean hp F v hv,
    add_zero,add_zero]
  exact congrArg₂ (·+·) (cubicThetaPrimeCubeDilation_horizontal_mean hp F v hv)
    (cubicThetaPrimeCubeBottom_mean hp F v hv)

end CubicFirstMoment

end

end OAI
