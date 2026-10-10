import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedFiniteFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowGaussian

namespace OAI

/-! Poisson summation for the actual inverted rows d=3a, with their
finite cubic character and the unchanged frequency lattice. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaInvertedGaussianRow (c : Eisenstein) (z : ℂ) (t : ℝ) : ℂ :=
  ∑' a : Eisenstein, cubicSymbol c (3*a)*
    (Real.exp (-t*‖z+3*(a:ℂ)/(c:ℂ)‖^2):ℂ)

lemma cubicThetaInvertedResidueWeight_mk {c : Eisenstein} (hc : primary c) (a : Eisenstein) :
    cubicSymbol c (3*residueRepresentative c (Ideal.Quotient.mk (modulus c) a))=
      cubicSymbol c (3*a) := by
  rw [cubicSymbol_mul_upper hc,cubicSymbol_mul_upper hc]
  congr 1
  exact cubicSymbol_congr (residueRepresentative_spec c _)

theorem cubicThetaInvertedGaussianRow_poisson {c : Eisenstein} (hc : primary c)
    (z : ℂ) {t : ℝ} (ht : 0<t) :
    cubicThetaInvertedGaussianRow c z t=
      (2/(9*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaInvertedGaussCoefficient c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ)) := by
  have hc0 := primary_ne_zero hc
  have hcC : (c:ℂ)≠0 := fun h => hc0 (Subtype.ext h)
  have hc3 : (c:ℂ)/3≠0 := div_ne_zero hcC (by norm_num)
  have hp := poisson_eisenstein_periodic c hc0
    (fun x => cubicSymbol c (3*residueRepresentative c x))
    (cubicThetaShiftedGaussian ((c:ℂ)/3) z hc3 t ht)
  have hleft : (∑' a : Eisenstein,
      cubicSymbol c (3*residueRepresentative c (Ideal.Quotient.mk (modulus c) a))*
        cubicThetaShiftedGaussian ((c:ℂ)/3) z hc3 t ht (a:ℂ))=
      cubicThetaInvertedGaussianRow c z t := by
    apply tsum_congr
    intro a
    rw [cubicThetaInvertedResidueWeight_mk hc,cubicThetaShiftedGaussian_apply]
    congr 4
    field_simp
  rw [hleft] at hp
  have hfreq (h : Eisenstein) : ((h:ℂ)/((c:ℂ)*traceLambda))*((c:ℂ)/3)=
      (h:ℂ)/(3*traceLambda) := by field_simp
  simp_rw [cubicThetaShiftedGaussian_fourier,hfreq] at hp
  change cubicThetaInvertedGaussianRow c z t=
    (2/(Real.sqrt 3*norm c):ℝ) •
      ∑' h : Eisenstein, cubicThetaInvertedGaussCoefficient c h*
        ((Complex.normSq ((c:ℂ)/3):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ))) at hp
  rw [hp]
  change ((2/(Real.sqrt 3*norm c):ℝ):ℂ)*_=_
  have hf : (∑' h : Eisenstein, cubicThetaInvertedGaussCoefficient c h*
        ((Complex.normSq ((c:ℂ)/3):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ))))=
      (Complex.normSq ((c:ℂ)/3):ℂ)*∑' h : Eisenstein,
        cubicThetaInvertedGaussCoefficient c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ)) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro h
    ring
  rw [hf,←mul_assoc]
  congr 1
  have hN : norm c≠0 := (norm_pos_of_ne_zero hc0).ne'
  rw [Complex.normSq_div]
  norm_num [Complex.normSq_ofReal]
  change (2/(((Real.sqrt 3:ℝ):ℂ)*(norm c:ℂ)))*((norm c:ℂ)/9)=_
  have hNC : (norm c:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hN
  field_simp

end CubicFirstMoment

end

end OAI
