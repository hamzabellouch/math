import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeBranchFourier

namespace OAI

/-! The Fourier action of the actual Hecke section, including the
frequency support in its dilation and character branches. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeHecke_fourier_split {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (h : Eisenstein) :
    cubicThetaSectionFourier (cubicThetaPrimeCubeHecke hp F) v hv h=
      cubicThetaHorizontalFourierCoefficient h (fun z =>
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
          cubicThetaHorizontalPoint v hv z))+
      (norm (p^3):ℂ)*cubicThetaSectionFourier F (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3)) (p^3*h)+
      cubicThetaPrimeCubeUnitFourier hp 1 (p*h)*
        cubicThetaSectionFourier F (v/‖(p:ℂ)‖)
          (div_pos hv (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he)))) (p*h)+
      cubicThetaHorizontalFourierCoefficient h (fun z =>
        cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
          (cubicThetaHorizontalPoint v hv z)) := by
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
  have he : (cubicThetaSectionHorizontal (cubicThetaPrimeCubeHecke hp F) v hv : ℂ → ℂ)=D+B+U+V := by
    funext z
    exact cubicThetaPrimeCubeHecke_functionOperator hp F (cubicThetaHorizontalPoint v hv z)
  unfold cubicThetaSectionFourier
  rw [he,cubicThetaHorizontalFourier_add h (D+B+U) V ((hD.add hB).add hU) hV,
    cubicThetaHorizontalFourier_add h (D+B) U (hD.add hB) hU,
    cubicThetaHorizontalFourier_add h D B hD hB]
  change cubicThetaHorizontalFourierCoefficient h D+cubicThetaHorizontalFourierCoefficient h B+
    cubicThetaHorizontalFourierCoefficient h U+cubicThetaHorizontalFourierCoefficient h V=_
  rw [show cubicThetaHorizontalFourierCoefficient h B=_ from cubicThetaPrimeCubeBottom_fourier hp F v hv h,
    show cubicThetaHorizontalFourierCoefficient h U=_ from cubicThetaPrimeCubeFirstBranch_fourier hp F v hv h]
  rfl

theorem cubicThetaPrimeCubeHecke_fourier_primefree {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaSectionFourier (cubicThetaPrimeCubeHecke hp F) v hv h=
      (norm (p^3):ℂ)*cubicThetaSectionFourier F (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3)) (p^3*h)+
      cubicThetaPrimeCubeUnitFourier hp 1 (p*h)*
        cubicThetaSectionFourier F (v/‖(p:ℂ)‖)
          (div_pos hv (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he)))) (p*h) := by
  rw [cubicThetaPrimeCubeHecke_fourier_split hp F v hv h,
    cubicThetaPrimeCubeDilation_fourier_zero hp F v hv h
      (fun hd => hh ((dvd_pow_self p (by decide : (3:ℕ)≠0)).trans hd)),
    cubicThetaPrimeCubeSecondBranch_fourier_zero hp F v hv h hh,zero_add,add_zero]

end CubicFirstMoment

end

end OAI
