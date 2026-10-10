import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierAffine
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeUnitMean

namespace OAI

/-! Fourier coefficients of the second character branch. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeSecondPeriodization (p : Eisenstein) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' u : (Residues p)ˣ,(cubicSymbol p (3*residueRepresentative p (u:Residues p)))^2*
    f ((p:ℂ)*z+3*(residueRepresentative p (u:Residues p):ℂ)/(p:ℂ))

lemma cubicThetaPrimeCubeSecondFourier_kernel {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) :
    (∑' u : (Residues p)ˣ,(cubicSymbol p (3*residueRepresentative p (u:Residues p)))^2*
      cubicThetaHorizontalCharacter h (3*(residueRepresentative p (u:Residues p):ℂ)/(p:ℂ)))=
        cubicThetaPrimeCubeUnitFourier hp (⟨2,by decide⟩:Fin 3) h := by
  have he := fun b => cubicThetaHorizontalCharacter_fraction h p b hp.2.ne_zero
  let g (q : Eisenstein) (hq : q≠0) : ℂ := ∑' u : (Residues q)ˣ,
    (cubicSymbol p (3*residueRepresentative q (u:Residues q)))^2*
      residueFourierChar q hq (Ideal.Quotient.mk (modulus q) h*u)
  calc
    _ = g p hp.2.ne_zero := by
      apply tsum_congr
      intro u
      rw [he,map_mul,residueRepresentative_spec]
    _ = g (p^(3-(⟨2,by decide⟩:Fin 3).val)) (pow_ne_zero _ hp.2.ne_zero) := by
      congr 1
      norm_num
    _ = _ := rfl

theorem cubicThetaPrimeCubeSecondPeriodization_fourier {p : Eisenstein} (hp : primaryPrime p)
    (f : C(ℂ,ℂ)) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient (p*h) (cubicThetaPrimeCubeSecondPeriodization p f)=
      cubicThetaPrimeCubeUnitFourier hp (⟨2,by decide⟩:Fin 3) h*
        cubicThetaHorizontalFourierCoefficient h f := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p)ˣ := Fintype.ofFinite _
  unfold cubicThetaPrimeCubeSecondPeriodization
  simp_rw [tsum_fintype]
  rw [cubicThetaHorizontalFourier_sum]
  · simp_rw [cubicThetaHorizontalFourier_const_mul,cubicThetaHorizontalFourier_affine f hf hp.2.ne_zero,
      ←mul_assoc]
    rw [←Finset.sum_mul]
    have hs := cubicThetaPrimeCubeSecondFourier_kernel hp h
    simp only [tsum_fintype] at hs
    rw [hs]
  · intro u _
    exact continuous_const.mul (f.continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const))

theorem cubicThetaPrimeCubeSecondPeriodization_fourier_zero {p : Eisenstein} (hp : primaryPrime p)
    (f : C(ℂ,ℂ)) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaHorizontalFourierCoefficient h (cubicThetaPrimeCubeSecondPeriodization p f)=0 := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p)ˣ := Fintype.ofFinite _
  unfold cubicThetaPrimeCubeSecondPeriodization
  simp_rw [tsum_fintype]
  rw [cubicThetaHorizontalFourier_sum]
  · simp_rw [cubicThetaHorizontalFourier_const_mul,
      cubicThetaHorizontalFourier_affine_zero f hf hp.2.ne_zero h hh,mul_zero,Finset.sum_const_zero]
  · intro u _
    exact continuous_const.mul (f.continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const))

end CubicFirstMoment

end

end OAI
