import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularExistence

namespace OAI

/-! The actual bounded part of the rescaled two-channel spectral system. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def circularBoundedField (νp νm η : ℂ) (m : ℕ) (q : ℂ) (z : E₄) : E₄ :=
  ((z.1.2,-(2*νp+10)*z.1.2-(νp*(νp+10)-η)*z.1.1+
      spectralDiagonalCoefficient m q*z.1.1+spectralCrossCoefficient m q*z.2.1),
   (z.2.2,-(2*νm+10)*z.2.2-(νm*(νm+10)-η)*z.2.1+
      star (spectralDiagonalCoefficient m q)*z.2.1+star (spectralCrossCoefficient m q)*z.1.1))

noncomputable def circularFieldBound (νp νm η : ℂ) (m : ℕ) (M : ℝ) : ℝ :=
  1+‖2*νp+10‖+‖2*νm+10‖+‖νp*(νp+10)-η‖+‖νm*(νm+10)-η‖+
    (2*(m : ℝ)+1)*M^(2*m)

theorem spectralDiagonalCoefficient_norm (m : ℕ) (q : ℂ) :
    ‖spectralDiagonalCoefficient m q‖=((m : ℝ)+1)*‖q‖^(2*m) := by
  have hpow : ‖q‖^m*‖q‖^m=‖q‖^(2*m) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = ‖((m+1 : ℕ) : ℂ)‖*(‖q‖^m*‖q‖^m) := by
      simp only [spectralDiagonalCoefficient,norm_mul,norm_pow,norm_star]
      ring
    _ = _ := by rw [hpow,Complex.norm_natCast]; push_cast; rfl

theorem spectralCrossCoefficient_norm (m : ℕ) (hm : 1 ≤ m) (q : ℂ) :
    ‖spectralCrossCoefficient m q‖=(m : ℝ)*‖q‖^(2*m) := by
  have hpow : ‖q‖^(m+1)*‖q‖^(m-1)=‖q‖^(2*m) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = ‖(m : ℂ)‖*(‖q‖^(m+1)*‖q‖^(m-1)) := by
      simp only [spectralCrossCoefficient,norm_mul,norm_pow,norm_star]
      ring
    _ = _ := by rw [hpow,Complex.norm_natCast]

theorem circularBoundedField_zero (νp νm η : ℂ) (m : ℕ) (q : ℂ) :
    circularBoundedField νp νm η m q 0=0 := by
  simp [circularBoundedField]

theorem circularBoundedField_sub (νp νm η : ℂ) (m : ℕ) (q : ℂ) (z w : E₄) :
    circularBoundedField νp νm η m q (z-w)=
      circularBoundedField νp νm η m q z-circularBoundedField νp νm η m q w := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [circularBoundedField,Prod.fst_sub,Prod.snd_sub]
  all_goals ring

theorem circularBoundedField_continuous (νp νm η : ℂ) (m : ℕ) :
    Continuous (fun p : ℂ × E₄ => circularBoundedField νp νm η m p.1 p.2) := by
  unfold circularBoundedField spectralDiagonalCoefficient spectralCrossCoefficient
  fun_prop

end DefocusingNLS

end OAI
