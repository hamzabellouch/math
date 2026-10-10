import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoefficientScaling
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteNonlinearSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialLogarithmicSymbol

namespace OAI

/-! The physical odd-power coefficients have a fixed decaying radial factor;
the only residual phase frequency is twice the profile exponent's imaginary part. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

private theorem exponential_powers (nu : ℂ) (t : ℝ) (r s : ℕ) :
    Complex.exp (nu*(t : ℂ))^r * star (Complex.exp (nu*(t : ℂ)))^s =
      Complex.exp (((r : ℂ)*nu+(s : ℂ)*star nu)*(t : ℂ)) := by
  simp only [Complex.star_def,← Complex.exp_conj,map_mul,Complex.conj_ofReal,
    ← Complex.exp_nat_mul,← Complex.exp_add]
  congr 1
  ring

theorem spectralRemote_physical_coefficient_factors (m : ℕ) (hm : 1 ≤ m)
    (nu q : ℂ) (t : ℝ) (hscale : 2*(m : ℝ)*nu.re = -2) :
    spectralDiagonalCoefficient m (Complex.exp (nu*(t : ℂ))*q) =
      Complex.exp ((-2 : ℂ)*(t : ℂ))*spectralDiagonalCoefficient m q ∧
    spectralCrossCoefficient m (Complex.exp (nu*(t : ℂ))*q) =
      Complex.exp (((-2 : ℂ)+2*Complex.I*(nu.im : ℂ))*(t : ℂ))*spectralCrossCoefficient m q := by
  have hd : (m : ℂ)*nu+(m : ℂ)*star nu = -2 := by
    apply Complex.ext
    · norm_num [Complex.mul_re]
      nlinarith [hscale]
    · simp [Complex.mul_im]
  have hc : ((m+1 : ℕ) : ℂ)*nu+((m-1 : ℕ) : ℂ)*star nu =
      (-2 : ℂ)+2*Complex.I*(nu.im : ℂ) := by
    rw [Nat.cast_add,Nat.cast_sub hm]
    push_cast
    apply Complex.ext
    · norm_num [Complex.mul_re,Complex.mul_im]
      nlinarith [hscale]
    · norm_num [Complex.mul_re,Complex.mul_im]
      ring
  constructor
  · calc
      _ = (Complex.exp (nu*(t : ℂ))^m*star (Complex.exp (nu*(t : ℂ)))^m)*
          spectralDiagonalCoefficient m q := by
        simp only [spectralDiagonalCoefficient,star_mul,mul_pow]
        ring
      _ = _ := by rw [exponential_powers,hd]
  · calc
      _ = (Complex.exp (nu*(t : ℂ))^(m+1)*star (Complex.exp (nu*(t : ℂ)))^(m-1))*
          spectralCrossCoefficient m q := by
        simp only [spectralCrossCoefficient,star_mul,mul_pow]
        ring
      _ = _ := by rw [exponential_powers,hc]

theorem spectralRemote_complex_exponential_symbol
    {L : ℕ → ℝ} (nu : ℕ → ℂ) (B sigma : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, ‖nu n‖ ≤ B) (hre : ∀ n, (nu n).re = sigma) :
    HasUniformLogJetBound L sigma (fun n t => Complex.exp (nu n*(t : ℂ))) := by
  refine ⟨Eventually.of_forall (fun n => (radial_complexExp_contDiff (nu n)).contDiffOn),?_⟩
  intro k
  refine ⟨B^k,pow_nonneg hB _,?_⟩
  filter_upwards [hb] with n hn
  intro t ht
  rw [radial_complexExp_iteratedDeriv,norm_mul,norm_pow,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,hre]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn _) (Real.exp_nonneg _)

end DefocusingNLS

end OAI
