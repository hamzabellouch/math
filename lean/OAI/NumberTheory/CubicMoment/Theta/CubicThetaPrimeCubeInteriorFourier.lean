import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSquareFourier

namespace OAI

/-! Away from the initial two valuation classes, the cubic Hecke action
is the exact inward/outward recurrence on actual section Fourier modes. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeHecke_fourier_interior {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (h : Eisenstein) :
    cubicThetaSectionFourier (cubicThetaPrimeCubeHecke hp F) v hv (p^3*h)=
      cubicThetaSectionFourier F (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv) h+
      (norm (p^3):ℂ)*cubicThetaSectionFourier F (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3))
        (p^3*(p^3*h)) := by
  have hfirst : cubicThetaPrimeCubeUnitFourier hp 1 (p*(p^3*h))=0 := by
    have he := cubicThetaPrimeCubeFirstKernel_multiple hp (p^2*h)
    convert he using 1; ring_nf
  have hsecond : cubicThetaHorizontalFourierCoefficient (p^3*h) (fun z =>
      cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
        (cubicThetaHorizontalPoint v hv z))=0 := by
    have he := cubicThetaPrimeCubeSecondBranch_fourier hp F v hv (p^2*h)
    have hz : cubicThetaPrimeCubeUnitFourier hp (⟨2,by decide⟩:Fin 3) (p^2*h)=0 := by
      have he := cubicThetaPrimeCubeSecondKernel_multiple hp (p*h)
      convert he using 1; ring_nf
    rw [hz,zero_mul] at he
    convert he using 1; ring_nf
  rw [cubicThetaPrimeCubeHecke_fourier_split hp F v hv (p^3*h),
    cubicThetaPrimeCubeDilation_fourier hp F v hv h,
    hfirst,hsecond,zero_mul,add_zero,add_zero]

end CubicFirstMoment

end

end OAI
