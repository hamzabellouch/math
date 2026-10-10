import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFirstFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSecondFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHorizontalMean
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalPeriodFourier

namespace OAI

/-! Nonzero horizontal observations of the actual four Hecke branches. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSectionFourier (F : CubicThetaSection) (v : ℝ) (hv : 0<v)
    (h : Eisenstein) : ℂ :=
  cubicThetaHorizontalFourierCoefficient h (cubicThetaSectionHorizontal F v hv)

theorem cubicThetaPrimeCubeFirstBranch_fourier {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient h (fun z =>
      cubicThetaPrimeCubeUnitFunctionSum hp 1 F.val (cubicThetaHorizontalPoint v hv z))=
      cubicThetaPrimeCubeUnitFourier hp 1 (p*h)*
        cubicThetaSectionFourier F (v/‖(p:ℂ)‖)
          (div_pos hv (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he)))) (p*h) := by
  have he : (fun z => cubicThetaPrimeCubeUnitFunctionSum hp 1 F.val
      (cubicThetaHorizontalPoint v hv z))=
      cubicThetaPrimeCubeFirstPeriodization p (cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖)
        (div_pos hv (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))))) := by
    funext z
    exact cubicThetaPrimeCubeFirstBranch_periodization hp F v hv z
  rw [he]
  exact cubicThetaPrimeCubeFirstPeriodization_fourier hp _
    (cubicThetaSectionHorizontal_periodic F _ _) h

lemma cubicThetaPrimeCubeSecondBranch_periodization {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
      (cubicThetaHorizontalPoint v hv z)=
      cubicThetaPrimeCubeSecondPeriodization p (cubicThetaSectionHorizontal F (‖(p:ℂ)‖*v)
        (mul_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) hv)) z := by
  rw [cubicThetaPrimeCubeUnitFunctionSum_two]
  unfold cubicThetaPrimeCubeSecondPeriodization
  apply tsum_congr
  intro u
  rw [cubicThetaPrimeCubeSecondBranch_section]

theorem cubicThetaPrimeCubeSecondBranch_fourier {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient (p*h) (fun z =>
      cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
        (cubicThetaHorizontalPoint v hv z))=
      cubicThetaPrimeCubeUnitFourier hp (⟨2,by decide⟩:Fin 3) h*
        cubicThetaSectionFourier F (‖(p:ℂ)‖*v)
          (mul_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) hv) h := by
  have he : (fun z => cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
      (cubicThetaHorizontalPoint v hv z))=
      cubicThetaPrimeCubeSecondPeriodization p (cubicThetaSectionHorizontal F (‖(p:ℂ)‖*v)
        (mul_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) hv)) := by
    funext z
    exact cubicThetaPrimeCubeSecondBranch_periodization hp F v hv z
  rw [he]
  exact cubicThetaPrimeCubeSecondPeriodization_fourier hp _
    (cubicThetaSectionHorizontal_periodic F _ _) h

theorem cubicThetaPrimeCubeSecondBranch_fourier_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaHorizontalFourierCoefficient h (fun z =>
      cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
        (cubicThetaHorizontalPoint v hv z))=0 := by
  have he : (fun z => cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
      (cubicThetaHorizontalPoint v hv z))=
      cubicThetaPrimeCubeSecondPeriodization p (cubicThetaSectionHorizontal F (‖(p:ℂ)‖*v)
        (mul_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) hv)) := by
    funext z
    exact cubicThetaPrimeCubeSecondBranch_periodization hp F v hv z
  rw [he]
  exact cubicThetaPrimeCubeSecondPeriodization_fourier_zero hp _
    (cubicThetaSectionHorizontal_periodic F _ _) h hh

theorem cubicThetaPrimeCubeBottom_fourier {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient h (fun z =>
      cubicThetaPrimeCubeBottomFunctionSum hp F.val (cubicThetaHorizontalPoint v hv z))=
      (norm (p^3):ℂ)*cubicThetaSectionFourier F (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3)) (p^3*h) := by
  have he : (fun z => cubicThetaPrimeCubeBottomFunctionSum hp F.val
      (cubicThetaHorizontalPoint v hv z))=
      cubicThetaHorizontalPeriodization (p^3) (cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3))) := by
    funext z
    exact cubicThetaPrimeCubeBottom_periodization hp F v hv z
  rw [he]
  exact cubicThetaHorizontalPeriodization_fourier (pow_ne_zero _ hp.2.ne_zero) _
    (cubicThetaSectionHorizontal_periodic F _ _) h

theorem cubicThetaPrimeCubeDilation_fourier {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient (p^3*h) (fun z =>
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        cubicThetaHorizontalPoint v hv z))=
      cubicThetaSectionFourier F (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv) h := by
  have he : (fun z => F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      cubicThetaHorizontalPoint v hv z))=
      (fun z => cubicThetaSectionHorizontal F (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv)
        ((p^3:Eisenstein)*z)) := by
    funext z
    rw [cubicThetaPrimeCubeDilation_horizontal_point hp]
    rfl
  rw [he]
  exact cubicThetaHorizontalFourier_dilate _ (cubicThetaSectionHorizontal_periodic F _ _)
    (pow_ne_zero _ hp.2.ne_zero) h (cubicThetaHorizontalFourier_integrable h _
      (cubicThetaSectionHorizontal F _ _).continuous)

theorem cubicThetaPrimeCubeDilation_fourier_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (h : Eisenstein) (hh : ¬p^3∣h) :
    cubicThetaHorizontalFourierCoefficient h (fun z =>
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        cubicThetaHorizontalPoint v hv z))=0 := by
  have he : (fun z => F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      cubicThetaHorizontalPoint v hv z))=
      (fun z => cubicThetaSectionHorizontal F (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv)
        ((p^3:Eisenstein)*z)) := by
    funext z
    rw [cubicThetaPrimeCubeDilation_horizontal_point hp]
    rfl
  rw [he]
  exact cubicThetaHorizontalFourier_dilate_zero _ (cubicThetaSectionHorizontal_periodic F _ _)
    (pow_ne_zero _ hp.2.ne_zero) h hh

end CubicFirstMoment

end

end OAI
