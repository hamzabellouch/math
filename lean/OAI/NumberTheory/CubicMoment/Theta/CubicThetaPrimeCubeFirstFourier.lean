import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierAlgebra
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierVanishing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFirstPeriodMean

namespace OAI

/-! The first character branch at every horizontal frequency, with the
actual finite Gauss kernel and its zero extension on nonunits. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFirstFourier_kernel {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) :
    (∑' r : Residues (p^2),
      cubicSymbol p (3*residueRepresentative (p^2) r)*
        cubicThetaHorizontalCharacter (p*h) (3*(residueRepresentative (p^2) r:ℂ)/(p:ℂ)^2))=
      cubicThetaPrimeCubeUnitFourier hp 1 (p*h) := by
  have he (b : Eisenstein) :
      cubicThetaHorizontalCharacter (p*h) (3*(b:ℂ)/(p:ℂ)^2)=
        residueFourierChar (p^2) (pow_ne_zero _ hp.2.ne_zero)
          (Ideal.Quotient.mk (modulus (p^2)) ((p*h)*b)) := by
    simpa only [Subalgebra.coe_pow] using cubicThetaHorizontalCharacter_fraction (p*h) (p^2) b
      (pow_ne_zero _ hp.2.ne_zero)
  rw [cubicThetaPrimeCubeResidueSum_two hp]
  have hz (r : Residues p) :
      cubicSymbol p (3*residueRepresentative (p^2)
        (Ideal.Quotient.mk (modulus (p^2)) (p*residueRepresentative p r)))*
        cubicThetaHorizontalCharacter (p*h)
          (3*(residueRepresentative (p^2)
            (Ideal.Quotient.mk (modulus (p^2)) (p*residueRepresentative p r)):ℂ)/(p:ℂ)^2)=0 := by
    rw [cubicThetaPrimeCubeFirstCoefficient_nonunit hp,zero_mul]
  simp_rw [hz]
  rw [tsum_zero,add_zero]
  unfold cubicThetaPrimeCubeUnitFourier
  simp only [Fin.val_one,Nat.reduceSub,pow_one]
  apply tsum_congr
  intro u
  rw [he,map_mul,residueRepresentative_spec]

theorem cubicThetaPrimeCubeFirstPeriodization_fourier {p : Eisenstein} (hp : primaryPrime p)
    (f : C(ℂ,ℂ)) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient h (cubicThetaPrimeCubeFirstPeriodization p f)=
      cubicThetaPrimeCubeUnitFourier hp 1 (p*h)*
        cubicThetaHorizontalFourierCoefficient (p*h) f := by
  let : Finite (Residues (p^2)) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^2)) := Fintype.ofFinite _
  calc
    _ = cubicThetaHorizontalFourierCoefficient (p*h)
        (fun z => cubicThetaPrimeCubeFirstPeriodization p f ((p:ℂ)*z)) :=
      (cubicThetaHorizontalFourier_dilate _
        (cubicThetaPrimeCubeFirstPeriodization_periodic hp f hf) hp.2.ne_zero h
        (cubicThetaHorizontalFourier_integrable h _
          (cubicThetaPrimeCubeFirstPeriodization_continuous hp f))).symm
    _ = ∑ r : Residues (p^2),cubicSymbol p (3*residueRepresentative (p^2) r)*
        (cubicThetaHorizontalCharacter (p*h) (3*(residueRepresentative (p^2) r:ℂ)/(p:ℂ)^2)*
          cubicThetaHorizontalFourierCoefficient (p*h) f) := by
      unfold cubicThetaPrimeCubeFirstPeriodization
      simp_rw [cubicThetaPrimeCubeFirstPeriodization_dilate hp,tsum_fintype]
      rw [cubicThetaHorizontalFourier_sum]
      · apply Finset.sum_congr rfl
        intro r _
        rw [cubicThetaHorizontalFourier_const_mul,cubicThetaHorizontalFourier_translate (p*h) f hf]
      · intro r _
        exact continuous_const.mul (f.continuous.comp (continuous_id.add continuous_const))
    _ = _ := by
      simp_rw [←mul_assoc]
      rw [←Finset.sum_mul]
      have hs := cubicThetaPrimeCubeFirstFourier_kernel hp h
      simp only [tsum_fintype] at hs
      rw [hs]

theorem cubicThetaPrimeCubeFirstPeriodization_fourier_reduced {p : Eisenstein}
    (hp : primaryPrime p) (f : C(ℂ,ℂ))
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient h (cubicThetaPrimeCubeFirstPeriodization p f)=
      (cubicSymbol p 3*(norm p:ℂ)*cubicThetaPrimeFourier p hp 1 h)*
        cubicThetaHorizontalFourierCoefficient (p*h) f := by
  rw [cubicThetaPrimeCubeFirstPeriodization_fourier hp f hf h]
  have he := cubicThetaPrimeCubeUnitFourier_reduction hp 1 (by decide) h
  simpa only [Fin.val_one,Nat.reduceSub,pow_one] using
    congrArg (fun c => c*cubicThetaHorizontalFourierCoefficient (p*h) f) he

end CubicFirstMoment

end

end OAI
