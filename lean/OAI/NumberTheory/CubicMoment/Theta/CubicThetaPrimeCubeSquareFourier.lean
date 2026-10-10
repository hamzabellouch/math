import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckeFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeLocalCases

namespace OAI

/-! At a frequency with prime valuation exactly two, both cubic-character
branches cancel and the dilation branch is absent. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFirstKernel_multiple {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : cubicThetaPrimeCubeUnitFourier hp 1 (p*(p*h))=0 := by
  have he := cubicThetaPrimeCubeUnitFourier_reduction hp 1 (by decide) (p*h)
  simp only [Fin.val_one,Nat.reduceSub,pow_one] at he
  rw [he,cubicThetaPrimeFourier_one_multiple hp h,mul_zero]

lemma cubicThetaPrimeCubeSecondKernel_multiple {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) :
    cubicThetaPrimeCubeUnitFourier hp (⟨2,by decide⟩:Fin 3) (p*h)=0 := by
  have he := cubicThetaPrimeCubeUnitFourier_reduction hp (⟨2,by decide⟩:Fin 3)
    (by decide) (p*h)
  norm_num only [Nat.reduceSub,pow_zero,one_mul,norm_one_eq] at he
  rw [he,cubicThetaPrimeFourier_two_multiple hp h,mul_zero]

lemma cubicThetaPrime_cube_not_dvd_square {p : Eisenstein} (hp : primaryPrime p)
    {h : Eisenstein} (hh : ¬p∣h) : ¬p^3∣p^2*h := by
  intro hd
  apply hh
  have he : p^2*p∣p^2*h := by simpa only [←pow_succ] using hd
  exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hp.2.ne_zero)).mp he

theorem cubicThetaPrimeCubeHecke_fourier_square {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaSectionFourier (cubicThetaPrimeCubeHecke hp F) v hv (p^2*h)=
      (norm (p^3):ℂ)*cubicThetaSectionFourier F (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3))
        (p^3*(p^2*h)) := by
  have hfirst : cubicThetaPrimeCubeUnitFourier hp 1 (p*(p^2*h))=0 := by
    have he := cubicThetaPrimeCubeFirstKernel_multiple hp (p*h)
    convert he using 1; ring_nf
  have hsecond : cubicThetaHorizontalFourierCoefficient (p^2*h) (fun z =>
      cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
        (cubicThetaHorizontalPoint v hv z))=0 := by
    have he := cubicThetaPrimeCubeSecondBranch_fourier hp F v hv (p*h)
    rw [cubicThetaPrimeCubeSecondKernel_multiple hp h,zero_mul] at he
    convert he using 1; ring_nf
  rw [cubicThetaPrimeCubeHecke_fourier_split,
    cubicThetaPrimeCubeDilation_fourier_zero hp F v hv _
      (cubicThetaPrime_cube_not_dvd_square hp hh),hfirst,hsecond,zero_mul,zero_add,add_zero,add_zero]

end CubicFirstMoment

end

end OAI
