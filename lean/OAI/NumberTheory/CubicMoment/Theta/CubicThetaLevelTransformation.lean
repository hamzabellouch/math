import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelBruhat

namespace OAI

/-! The actual theta transformation at a primary modulus. The constant
term still has the proved value C/B; the cubic character is fully explicit. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaNormalizedSeries_bruhat {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val
      (cubicThetaTranslationMatrix (3*(y:ℂ)/(q:ℂ)) •
        (cubicThetaInversionMatrix (q:ℂ) (fun he => primary_ne_zero hq (Subtype.ext he)) •
          (cubicThetaTranslationMatrix (3*(x:ℂ)/(q:ℂ)) • p)))=
      cubicSymbol q (3*y)*cubicThetaNormalizedSeriesSection.val p := by
  rw [←mul_smul,←mul_smul,cubicThetaLevelBruhat_identity hq x y hxy,mul_smul]
  change cubicThetaNormalizedSeriesSection.val
    (cubicThetaFullInversion • (cubicThetaLevelBruhat hq x y hxy • p))=_
  rw [cubicThetaNormalizedSeriesSection_inversion,
    cubicThetaNormalizedSeriesSection.property,cubicThetaLevelBruhat_kubota]

theorem cubicThetaNormalizedSeries_rational {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) {v : ℝ} (hv : 0<v) :
    cubicThetaSeriesConstant*((((norm q*v)⁻¹)^(2/3:ℝ):ℝ):ℂ)+
      cubicThetaNonconstant cubicThetaArithmeticCoefficient
        (3*(y:ℂ)/(q:ℂ),(norm q*v)⁻¹)=
      cubicSymbol q (3*y)*(cubicThetaSeriesConstant*((v^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaArithmeticCoefficient (-3*(x:ℂ)/(q:ℂ),v)) := by
  let p : CubicThetaPoint := ⟨(-3*(x:ℂ)/(q:ℂ),v),hv⟩
  have hqC : (q:ℂ)≠0 := fun he => primary_ne_zero hq (Subtype.ext he)
  have he := cubicThetaNormalizedSeries_bruhat hq x y hxy p
  rw [cubicThetaNormalizedSeriesSection_apply,cubicThetaNormalizedSeriesSection_apply] at he
  have hcoords :
      (cubicThetaTranslationMatrix (3*(y:ℂ)/(q:ℂ)) •
        (cubicThetaInversionMatrix (q:ℂ) hqC •
          (cubicThetaTranslationMatrix (3*(x:ℂ)/(q:ℂ)) • p))).val=
        (3*(y:ℂ)/(q:ℂ),(norm q*v)⁻¹) := by
    change cubicThetaMobius (cubicThetaTranslationMatrix (3*(y:ℂ)/(q:ℂ)))
      (cubicThetaMobius (cubicThetaInversionMatrix (q:ℂ) hqC)
        (cubicThetaMobius (cubicThetaTranslationMatrix (3*(x:ℂ)/(q:ℂ)))
          (-3*(x:ℂ)/(q:ℂ),v)))=_
    rw [cubicThetaMobius_translation (3*(x:ℂ)/(q:ℂ)) (-3*(x:ℂ)/(q:ℂ),v)]
    dsimp only [Prod.fst,Prod.snd]
    have hx : -3*(x:ℂ)/(q:ℂ)+3*(x:ℂ)/(q:ℂ)=0 := by ring
    rw [hx,cubicThetaMobius_inversion hqC hv,cubicThetaInversion_center (q:ℂ) hv,
      cubicThetaMobius_translation,zero_add]
    rfl
  rw [hcoords] at he
  exact he

theorem cubicThetaArithmetic_rational_inversion {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) {v : ℝ} (hv : 0<v) :
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (3*(y:ℂ)/(q:ℂ),(norm q*v)⁻¹)=
      cubicSymbol q (3*y)*
        cubicThetaNonconstant cubicThetaArithmeticCoefficient (-3*(x:ℂ)/(q:ℂ),v)+
      cubicThetaSeriesConstant*(cubicSymbol q (3*y)*((v^(2/3:ℝ):ℝ):ℂ)-
        ((((norm q*v)⁻¹)^(2/3:ℝ):ℝ):ℂ)) := by
  have he := cubicThetaNormalizedSeries_rational hq x y hxy hv
  linear_combination he

end CubicFirstMoment

end

end OAI
