import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticPlane
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelTransformation

namespace OAI

/-! The primary-level transformation on an open horizontal neighborhood,
so that its actual derivatives can be transported to rational cusps. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticPlane_level {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaArithmeticPlane
      ((cubicThetaInversion (q:ℂ) (z,v)).1+3*(y:ℂ)/(q:ℂ),
        (cubicThetaInversion (q:ℂ) (z,v)).2)=
      cubicSymbol q (3*y)*cubicThetaArithmeticPlane (z-3*(x:ℂ)/(q:ℂ),v) := by
  let p : CubicThetaPoint := ⟨(z-3*(x:ℂ)/(q:ℂ),v),hv⟩
  have hqC : (q:ℂ)≠0 := fun he => primary_ne_zero hq (Subtype.ext he)
  have he := cubicThetaNormalizedSeries_bruhat hq x y hxy p
  rw [←cubicThetaArithmeticPlane_section,←cubicThetaArithmeticPlane_section] at he
  have hc :
      (cubicThetaTranslationMatrix (3*(y:ℂ)/(q:ℂ)) •
        (cubicThetaInversionMatrix (q:ℂ) hqC •
          (cubicThetaTranslationMatrix (3*(x:ℂ)/(q:ℂ)) • p))).val=
      ((cubicThetaInversion (q:ℂ) (z,v)).1+3*(y:ℂ)/(q:ℂ),
        (cubicThetaInversion (q:ℂ) (z,v)).2) := by
    change cubicThetaMobius (cubicThetaTranslationMatrix (3*(y:ℂ)/(q:ℂ)))
      (cubicThetaMobius (cubicThetaInversionMatrix (q:ℂ) hqC)
        (cubicThetaMobius (cubicThetaTranslationMatrix (3*(x:ℂ)/(q:ℂ)))
          (z-3*(x:ℂ)/(q:ℂ),v)))=_
    rw [cubicThetaMobius_translation (3*(x:ℂ)/(q:ℂ)) (z-3*(x:ℂ)/(q:ℂ),v)]
    dsimp only [Prod.fst,Prod.snd]
    rw [sub_add_cancel,cubicThetaMobius_inversion hqC hv,cubicThetaMobius_translation]
  rw [hc] at he
  exact he

end CubicFirstMoment

end

end OAI
