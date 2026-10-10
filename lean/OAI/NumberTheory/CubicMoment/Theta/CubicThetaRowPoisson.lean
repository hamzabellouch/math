import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowGaussian

namespace OAI

/-! The actual finite Gauss coefficient and Poisson expansion of a
nonzero cubic Eisenstein row. The dual lattice is independent of the row. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaEisensteinGaussCoefficient (c h : Eisenstein) : ℂ :=
  ∑' x : Residues (3*c), cubicThetaEisensteinResidueWeight c x*
    (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
      ((h:ℂ)/((3*c: Eisenstein)*traceLambda))):ℂ)

def cubicThetaEisensteinGaussianRow (c : Eisenstein) (z : ℂ) (t : ℝ) : ℂ :=
  ∑' d : Eisenstein, cubicThetaEisensteinWeight c d*
    (Real.exp (-t*‖z+(d:ℂ)/(c:ℂ)‖^2):ℂ)

theorem cubicThetaEisensteinGaussianRow_poisson {c : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hc0 : c ≠ 0) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    cubicThetaEisensteinGaussianRow c z t =
      (2/(9*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaEisensteinGaussCoefficient c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ)) := by
  have hcC : (c:ℂ) ≠ 0 := fun h => hc0 (Subtype.ext h)
  have hq : (3*c:Eisenstein) ≠ 0 := mul_ne_zero (by norm_num) hc0
  have hp := poisson_eisenstein_periodic (3*c) hq (cubicThetaEisensteinResidueWeight c)
    (cubicThetaShiftedGaussian c z hcC t ht)
  have hleft : (∑' d : Eisenstein,
      cubicThetaEisensteinResidueWeight c (Ideal.Quotient.mk (modulus (3*c)) d)*
        cubicThetaShiftedGaussian c z hcC t ht (d:ℂ)) =
      cubicThetaEisensteinGaussianRow c z t := by
    apply tsum_congr
    intro d
    rw [cubicThetaEisensteinResidueWeight_mk hc, cubicThetaShiftedGaussian_apply]
  rw [hleft] at hp
  have hfreq (h : Eisenstein) : ((h:ℂ)/((3*c:Eisenstein)*traceLambda))*(c:ℂ) =
      (h:ℂ)/(3*traceLambda) := by
    change ((h:ℂ)/(((3:ℂ)*(c:ℂ))*traceLambda))*(c:ℂ) = _
    field_simp
  simp_rw [cubicThetaShiftedGaussian_fourier, hfreq] at hp
  change cubicThetaEisensteinGaussianRow c z t =
    (2/(Real.sqrt 3*norm (3*c)):ℝ) •
      ∑' h : Eisenstein, cubicThetaEisensteinGaussCoefficient c h*
        ((Complex.normSq (c:ℂ):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ))) at hp
  rw [hp]
  change ((2/(Real.sqrt 3*norm (3*c)):ℝ):ℂ)*_ = _
  have hf : (∑' h : Eisenstein, cubicThetaEisensteinGaussCoefficient c h*
        ((Complex.normSq (c:ℂ):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ)))) =
      (norm c:ℂ)*∑' h : Eisenstein,
        cubicThetaEisensteinGaussCoefficient c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    change _ = (Complex.normSq (c:ℂ):ℂ)*_
    ring
  rw [hf, ← mul_assoc]
  congr 1
  have hn : norm c ≠ 0 := ne_of_gt (norm_pos_of_ne_zero hc0)
  have hNc : norm (3*c) = 9*norm c := by
    change Complex.normSq (((3:Eisenstein)*c):ℂ) = _
    change Complex.normSq ((3:ℂ)*(c:ℂ)) = _
    rw [map_mul]
    norm_num
    rfl
  rw [hNc]
  push_cast
  have hnC : (norm c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  field_simp

end CubicFirstMoment

end

end OAI
