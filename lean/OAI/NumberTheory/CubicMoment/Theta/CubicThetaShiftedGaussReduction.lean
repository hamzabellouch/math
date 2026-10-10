import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCharacter
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedWeightFactor
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedFourierSupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedGaussian
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteInflation

namespace OAI

/-! Exact reduction of the translated-cusp Fourier coefficients to
ordinary primary cubic Gauss coefficients, with the ramified shift retained. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCuspStepValue_star_mul (b m : Eisenstein) :
    star (cubicThetaCuspStepValue b m)*cubicThetaCuspStepValue b m=1 := by
  rw [mul_comm,Complex.star_def,Complex.mul_conj']
  change (‖cubicThetaKubotaValue (cubicThetaCuspStep b m)‖:ℂ)^2=1
  rw [cubicThetaKubotaValue_norm]
  norm_num

lemma cubicThetaShiftedGauss_phase {c : Eisenstein} (hc : c≠0)
    (a b : ℤ) (x : Residues (3*c)) :
    residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc)
        (Ideal.Quotient.mk (modulus (3*c)) (c*lambdaE*(b:Eisenstein))*x)=
      cubicThetaCuspStepValue ((a:Eisenstein)+b*omegaE) (residueRepresentative (3*c) x) := by
  rw [cubicThetaCuspStepValue_fourier]
  have hx := residueRepresentative_spec (3*c) x
  conv_lhs => rw [←hx,←map_mul]
  rw [show c*lambdaE*(b:Eisenstein)*residueRepresentative (3*c) x=
    c*(lambdaE*(b:Eisenstein))*residueRepresentative (3*c) x by ring,
    residueFourierChar_mul_factor (by norm_num) hc]
  congr 2
  ring

lemma cubicThetaInvertedWeight_reduction {c : Eisenstein} (hc : primary c)
    (x : Residues (3*c)) :
    cubicSymbol c (3*residueRepresentative c
      (residueReduction (show c ∣ 3*c from ⟨3,by ring⟩) x))=
      cubicSymbol c (3*residueRepresentative (3*c) x) := by
  have he : residueReduction (show c ∣ 3*c from ⟨3,by ring⟩) x=
      Ideal.Quotient.mk (modulus c) (residueRepresentative (3*c) x) := by
    rw [←residueReduction_mk (show c ∣ 3*c from ⟨3,by ring⟩),residueRepresentative_spec]
  rw [he,cubicThetaInvertedResidueWeight_mk hc]

theorem cubicThetaShiftedGaussCoefficient_untwist {c : Eisenstein} (hc : primary c)
    (a b : ℤ) (h : Eisenstein) :
    cubicThetaShiftedGaussCoefficient ((a:Eisenstein)+b*omegaE) c h=
      ∑' x : Residues (3*c),
        cubicSymbol c (3*residueRepresentative c
          (residueReduction (show c ∣ 3*c from ⟨3,by ring⟩) x))*
        residueFourierChar (3*c) (mul_ne_zero (by norm_num) (primary_ne_zero hc))
          (Ideal.Quotient.mk (modulus (3*c)) (h-c*lambdaE*(b:Eisenstein))*x) := by
  rw [cubicThetaShiftedGaussCoefficient_fourier (primary_ne_zero hc)]
  apply tsum_congr
  intro x
  let ψ := residueFourierChar (3*c) (mul_ne_zero (by norm_num) (primary_ne_zero hc))
  have he : ψ (Ideal.Quotient.mk (modulus (3*c)) h*x)=
      ψ (Ideal.Quotient.mk (modulus (3*c)) (h-c*lambdaE*(b:Eisenstein))*x)*
      ψ (Ideal.Quotient.mk (modulus (3*c)) (c*lambdaE*(b:Eisenstein))*x) := by
    rw [←ψ.map_add_eq_mul,←add_mul,←map_add,sub_add_cancel]
  have hw : cubicThetaShiftedResidueWeight ((a:Eisenstein)+b*omegaE) c x=
      star (cubicThetaCuspStepValue ((a:Eisenstein)+b*omegaE) (residueRepresentative (3*c) x))*
        cubicSymbol c (3*residueRepresentative (3*c) x) :=
    cubicThetaShiftedRowWeight_factor hc _ _
  rw [hw,he,cubicThetaShiftedGauss_phase (primary_ne_zero hc) a b x,
    cubicThetaInvertedWeight_reduction hc x]
  have hχ := cubicThetaCuspStepValue_star_mul ((a:Eisenstein)+b*omegaE) (residueRepresentative (3*c) x)
  linear_combination cubicSymbol c (3*residueRepresentative (3*c) x)*
    ψ (Ideal.Quotient.mk (modulus (3*c)) (h-c*lambdaE*(b:Eisenstein))*x)*hχ

theorem cubicThetaShiftedGaussCoefficient_reduce {c : Eisenstein} (hc : primary c)
    (a b : ℤ) (h : Eisenstein) :
    cubicThetaShiftedGaussCoefficient ((a:Eisenstein)+b*omegaE) c
      (3*h+c*lambdaE*(b:Eisenstein))=9*cubicThetaInvertedGaussCoefficient c h := by
  have hc0 := primary_ne_zero hc
  have h3 : (3:Eisenstein)≠0 := by norm_num
  rw [cubicThetaShiftedGaussCoefficient_untwist hc,add_sub_cancel_right]
  rw [residueFourier_inflation_of_eq (mul_ne_zero h3 hc0) hc0 h3
    (show 3*c=c*3 by ring) (show c ∣ 3*c from ⟨3,by ring⟩)
    (fun y => cubicSymbol c (3*residueRepresentative c y)) h]
  have hN : (norm (3:Eisenstein):ℂ)=9 := by
    change (Complex.normSq (3:ℂ):ℂ)=9
    norm_num
  rw [hN]
  congr 1
  unfold cubicThetaInvertedGaussCoefficient
  apply tsum_congr
  intro y
  rw [residueFourierChar_mk_mul]

theorem cubicThetaShiftedGaussCoefficient_congruence {c : Eisenstein} (hc : primary c)
    (a b : ℤ) (h : Eisenstein)
    (hF : cubicThetaShiftedGaussCoefficient ((a:Eisenstein)+b*omegaE) c h≠0) :
    (3:Eisenstein) ∣ h-c*lambdaE*(b:Eisenstein) := by
  have hc0 := primary_ne_zero hc
  have hq : (3*c:Eisenstein)≠0 := mul_ne_zero (by norm_num) hc0
  let : Finite (Residues (3*c)) := finite_residues hq
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  rw [cubicThetaShiftedGaussCoefficient_untwist hc,tsum_fintype] at hF
  have he := residueFourier_inflation_support hq (show c ∣ 3*c from ⟨3,by ring⟩)
    (fun y => cubicSymbol c (3*residueRepresentative c y)) (h-c*lambdaE*(b:Eisenstein)) hF
  rwa [mul_comm (3:Eisenstein) c,mul_dvd_mul_iff_left hc0] at he

end CubicFirstMoment

end

end OAI
