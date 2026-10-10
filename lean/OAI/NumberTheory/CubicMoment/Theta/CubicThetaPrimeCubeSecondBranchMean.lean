import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeUnitMean
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSecondBranchCoordinates

namespace OAI

/-! The actual second character branch of the cubed-prime Hecke trace
has zero constant horizontal coefficient, at every positive height. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeUnitFunctionSum_two {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaPoint → ℂ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F x=
      ∑' u : (Residues p)ˣ,(cubicSymbol p (3*residueRepresentative p (u:Residues p)))^2*
        F (cubicThetaPrimeCubeBranchPoint hp (⟨2,by decide⟩:Fin 3)
          (residueRepresentative p (u:Residues p)) x) := by
  let g : Eisenstein → ℂ := fun q => ∑' u : (Residues q)ˣ,
    (cubicSymbol p (3*residueRepresentative q (u:Residues q)))^2*
      F (cubicThetaPrimeCubeBranchPoint hp (⟨2,by decide⟩:Fin 3)
        (residueRepresentative q (u:Residues q)) x)
  change g (p^(3-(⟨2,by decide⟩:Fin 3).val))=g p
  exact congrArg g (by norm_num)

theorem cubicThetaPrimeCubeSecondBranch_mean {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,
      cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
        (cubicThetaHorizontalPoint v hv z))=0 := by
  simp_rw [cubicThetaPrimeCubeUnitFunctionSum_two,cubicThetaPrimeCubeSecondBranch_section]
  exact cubicThetaPrimeCubeSquareCharacter_mean hp
    (cubicThetaSectionHorizontal F (‖(p:ℂ)‖*v)
      (mul_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) hv))
    (cubicThetaSectionHorizontal_periodic F _ _)
    (fun u => 3*(residueRepresentative p (u:Residues p):ℂ)/(p:ℂ))

end CubicFirstMoment

end

end OAI
