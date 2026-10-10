import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylGauss

namespace OAI

/-! The zero Fourier row of the actual Weyl action. Subtracting the
zero column removes the dilation term exactly, without assuming it vanishes. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeRootWeyl_average {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) :
    cubicThetaPrimeRootAverage hp (cubicThetaPrimeRootWeylSection hp
      (cubicThetaPrimeRootAverage hp (cubicThetaPrimeRootSectionRestrict F)))=
      (norm p:ℂ)⁻¹ • cubicThetaPrimeRootAverage hp
        (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)) := by
  simpa only [cubicThetaPrimeRootWeylKernel_zero_zero,cubicThetaPrimeRootFourierProjection_zero,
    mul_zero,zero_smul,add_zero] using cubicThetaPrimeRootWeyl_fourier_formula hp 0 0 F

theorem cubicThetaPrimeRootWeyl_zero_row {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) (F : CubicThetaSection) :
    cubicThetaPrimeRootAverage hp (cubicThetaPrimeRootWeylSection hp
      (cubicThetaPrimeRootFourierProjection hp (Ideal.Quotient.mk (modulus p) h)
        (cubicThetaPrimeRootSectionRestrict F)))=
      (norm p:ℂ)⁻¹ •
        (cubicThetaPrimeRootAverage hp
          (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F))+
          cubicThetaPrimeAdditiveGauss p hp 1 (-h) • cubicThetaPrimeRootAverage hp
            (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F))) := by
  simpa only [cubicThetaPrimeRootFourierProjection_zero,
    cubicThetaPrimeRootWeylKernel_zero_left_additive hp h hh] using
    cubicThetaPrimeRootWeyl_fourier_formula hp 0 (Ideal.Quotient.mk (modulus p) h) F

theorem cubicThetaPrimeRootWeyl_zero_row_difference {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : IsCoprime p h) (F : CubicThetaSection) :
    cubicThetaPrimeRootAverage hp (cubicThetaPrimeRootWeylSection hp
      (cubicThetaPrimeRootFourierProjection hp (Ideal.Quotient.mk (modulus p) h)
        (cubicThetaPrimeRootSectionRestrict F)+
       (-1:ℂ) • cubicThetaPrimeRootAverage hp (cubicThetaPrimeRootSectionRestrict F)))=
      ((norm p:ℂ)⁻¹*cubicThetaPrimeAdditiveGauss p hp 1 (-h)) •
        cubicThetaPrimeRootAverage hp
          (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F)) := by
  have hw (X Y : cubicThetaPrimeRootSections p) :
      cubicThetaPrimeRootWeylSection hp (X+(-1:ℂ) • Y)=
        cubicThetaPrimeRootWeylSection hp X+(-1:ℂ) • cubicThetaPrimeRootWeylSection hp Y := rfl
  rw [hw,map_add,map_smul,cubicThetaPrimeRootWeyl_zero_row hp h hh,
    cubicThetaPrimeRootWeyl_average hp F,smul_add]
  simp only [smul_smul]
  rw [add_right_comm,←add_smul,neg_one_mul,add_neg_cancel,zero_smul,zero_add]

end CubicFirstMoment

end

end OAI
