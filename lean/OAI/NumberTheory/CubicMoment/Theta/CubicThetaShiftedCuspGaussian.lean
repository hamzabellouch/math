import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedFourierSupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowGaussian

namespace OAI

/-! Poisson summation at each translated inverted cusp. The true period
is 3c in the row variable and the dual frequency is h/(9 lambda). -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaShiftedCuspGaussianRow (b c : Eisenstein) (z : ℂ) (t : ℝ) : ℂ :=
  ∑' a : Eisenstein, cubicThetaShiftedRowWeight b c a*
    (Real.exp (-t*‖z+3*(a:ℂ)/(c:ℂ)‖^2):ℂ)

theorem cubicThetaShiftedCuspGaussianRow_poisson {c : Eisenstein} (hc : primary c)
    (b : Eisenstein) (z : ℂ) {t : ℝ} (ht : 0<t) :
    cubicThetaShiftedCuspGaussianRow b c z t=
      (2/(81*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaShiftedGaussCoefficient b c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(9*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(9*traceLambda))):ℝ)) := by
  have hc0 := primary_ne_zero hc
  have hcC : (c:ℂ)≠0 := fun h => hc0 (Subtype.ext h)
  have hc3 : (c:ℂ)/3≠0 := div_ne_zero hcC (by norm_num)
  have h3c : (3*c:Eisenstein)≠0 := mul_ne_zero (by norm_num) hc0
  have hp := poisson_eisenstein_periodic (3*c) h3c
    (cubicThetaShiftedResidueWeight b c)
    (cubicThetaShiftedGaussian ((c:ℂ)/3) z hc3 t ht)
  have hleft : (∑' a : Eisenstein,
      cubicThetaShiftedResidueWeight b c (Ideal.Quotient.mk (modulus (3*c)) a)*
        cubicThetaShiftedGaussian ((c:ℂ)/3) z hc3 t ht (a:ℂ))=
      cubicThetaShiftedCuspGaussianRow b c z t := by
    apply tsum_congr
    intro a
    rw [cubicThetaShiftedResidueWeight_mk hc,cubicThetaShiftedGaussian_apply]
    congr 4
    field_simp
  rw [hleft] at hp
  have hfreq (h : Eisenstein) : ((h:ℂ)/(((3*c:Eisenstein):ℂ)*traceLambda))*((c:ℂ)/3)=
      (h:ℂ)/(9*traceLambda) := by
    push_cast
    simp only [show ((3:Eisenstein):ℂ)=3 from rfl]
    field_simp
    ring
  simp_rw [cubicThetaShiftedGaussian_fourier,hfreq] at hp
  change cubicThetaShiftedCuspGaussianRow b c z t=
    (2/(Real.sqrt 3*norm (3*c)):ℝ) •
      ∑' h : Eisenstein, cubicThetaShiftedGaussCoefficient b c h*
        ((Complex.normSq ((c:ℂ)/3):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(9*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(9*traceLambda))):ℝ))) at hp
  rw [hp]
  change ((2/(Real.sqrt 3*norm (3*c)):ℝ):ℂ)*_=_
  have hf : (∑' h : Eisenstein, cubicThetaShiftedGaussCoefficient b c h*
        ((Complex.normSq ((c:ℂ)/3):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(9*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(9*traceLambda))):ℝ))))=
      (Complex.normSq ((c:ℂ)/3):ℂ)*∑' h : Eisenstein,
        cubicThetaShiftedGaussCoefficient b c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(9*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(9*traceLambda))):ℝ)) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro h
    ring
  rw [hf,←mul_assoc]
  congr 1
  have hN : norm c≠0 := (norm_pos_of_ne_zero hc0).ne'
  have hN3 : norm (3*c)=9*norm c := by
    rw [norm_mul_eq]
    congr 1
    norm_num [norm,Complex.normSq_ofReal,show ((3:Eisenstein):ℂ)=3 from rfl]
  rw [Complex.normSq_div,hN3]
  norm_num [Complex.normSq_ofReal]
  change (2/(((Real.sqrt 3:ℝ):ℂ)*(9*(norm c:ℂ))))*((norm c:ℂ)/9)=_
  have hNC : (norm c:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hN
  field_simp
  norm_num

end CubicFirstMoment

end

end OAI
