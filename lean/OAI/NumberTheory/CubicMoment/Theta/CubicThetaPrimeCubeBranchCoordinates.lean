import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeTriangularCoordinates
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeReductionResidue

namespace OAI

/-! The normalized prime-power coordinates of each nonzero valuation
branch in the actual cubed-prime trace. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeReducedScale_normSq_inv {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) :
    (Complex.normSq (cubicThetaPrimeCubeReducedScale hp k))⁻¹=
      ‖(p:ℂ)‖^k.val/‖(p:ℂ)‖^(3-k.val) := by
  calc
    _ = ‖(cubicThetaPrimeCubeReducedScale hp k)⁻¹^2‖ := by
      rw [norm_pow,norm_inv,Complex.normSq_eq_norm_sq,inv_pow]
    _ = _ := by
      rw [cubicThetaPrimeCubeReducedScale_square,norm_div,norm_pow,norm_pow]

theorem cubicThetaPrimeCubeReducedMatrix_coordinates {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) (z : ℂ × ℝ) :
    cubicThetaMobius (cubicThetaPrimeCubeReducedMatrix hp k n hn) z=
      ((p:ℂ)^k.val/(p:ℂ)^(3-k.val)*z.1+
        (((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)/(p:ℂ)^(3-k.val),
        (‖(p:ℂ)‖^k.val/‖(p:ℂ)‖^(3-k.val))*z.2) := by
  rw [cubicThetaPrimeCubeReducedMatrix_mobius,cubicThetaPrimeCubeReducedScale_square,
    cubicThetaPrimeCubeReducedScale_translation]
  apply Prod.ext
  · rfl
  · change z.2*(Complex.normSq (cubicThetaPrimeCubeReducedScale hp k))⁻¹=_
    rw [cubicThetaPrimeCubeReducedScale_normSq_inv,mul_comm]

def cubicThetaPrimeCubeBranchPoint {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b : Eisenstein) (x : CubicThetaPoint) : CubicThetaPoint :=
  ⟨((p:ℂ)^k.val/(p:ℂ)^(3-k.val)*x.val.1+((3*b:Eisenstein):ℂ)/(p:ℂ)^(3-k.val),
    (‖(p:ℂ)‖^k.val/‖(p:ℂ)‖^(3-k.val))*x.val.2),
    mul_pos (div_pos (pow_pos (norm_pos_iff.mpr (fun hz => hp.2.ne_zero (Subtype.ext hz))) _)
      (pow_pos (norm_pos_iff.mpr (fun hz => hp.2.ne_zero (Subtype.ext hz))) _)) x.property⟩

theorem cubicThetaPrimeCubeBranch_section {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) (F : CubicThetaSection) (x : CubicThetaPoint) :
    F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (cubicThetaPrincipalLower (p^k.val*n) • x))=
      (cubicSymbol p (3*cubicThetaPrimeCubeReductionTranslation hp k n hn))^k.val*
        F.val (cubicThetaPrimeCubeBranchPoint hp k
          (cubicThetaPrimeCubeReductionTranslation hp k n hn) x) := by
  rw [cubicThetaPrimeCubeReduction_section hp]
  have he : cubicThetaPrimeCubeReducedMatrix hp k n hn • x=
      cubicThetaPrimeCubeBranchPoint hp k (cubicThetaPrimeCubeReductionTranslation hp k n hn) x := by
    apply Subtype.ext
    change cubicThetaMobius _ x.val=_
    rw [cubicThetaPrimeCubeReducedMatrix_coordinates,
      ←cubicThetaPrimeCubeReductionTranslation_three hp k n hn]
    rfl
  rw [he,cubicThetaPrimeCubeReductionTranslation_three]

end CubicFirstMoment

end

end OAI
