import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedBisection

namespace OAI

/-! A fixed unary guard bounds the actual residual modulus by a polynomial
in the displacement/weight bound and the amplification. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation

def targetModulusBase (rho : ℕ) : ℝ :=
  localizedCoulombLipschitzConstant (GaussianFrequency.frequency rho) /
    (2 * Real.sqrt (localizedGramConstant (GaussianFrequency.frequency rho)))

def lipschitzGuard (rho : ℕ) : ℕ :=
  ⌈(planarHoppingLipschitzConstant : ℝ) + targetModulusBase rho⌉₊ + 1

theorem targetModulusBase_nonnegative (rho : ℕ) : 0 ≤ targetModulusBase rho :=
  div_nonneg (localizedCoulombLipschitzConstant_nonnegative _)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

theorem lipschitzGuard_bound (rho : ℕ) :
    (planarHoppingLipschitzConstant : ℝ) + targetModulusBase rho ≤ lipschitzGuard rho := by
  have h := Nat.le_ceil ((planarHoppingLipschitzConstant : ℝ) + targetModulusBase rho)
  simp only [lipschitzGuard, Nat.cast_add, Nat.cast_one]
  linarith

theorem lipschitzGuard_positive (rho : ℕ) : 0 < lipschitzGuard rho := by
  unfold lipschitzGuard
  omega

theorem residualLipschitz_bound (rho : ℕ) (e : Environment)
    (hK : (0 : ℝ) ≤ e.2.2.2) (hKN : (e.2.2.2 : ℝ) ≤ e.1.1)
    (hτ1 : (e.2.2.1 : ℝ) ≤ 1) :
    residualLipschitz rho e ≤
      (lipschitzGuard rho : ℝ) * ((e.2.1 : ℝ) + e.1.1 + 1) := by
  have hH : 0 ≤ (planarHoppingLipschitzConstant : ℝ) := NNReal.coe_nonneg _
  have hA := targetModulusBase_nonnegative rho
  have hN : (0 : ℝ) ≤ e.1.1 := Nat.cast_nonneg _
  have hS : (0 : ℝ) ≤ e.2.1 := Nat.cast_nonneg _
  have hroot : Real.sqrt (e.2.2.2 : ℝ) ≤ (e.1.1 : ℝ) + 1 := by
    have hs := Real.sqrt_nonneg (e.2.2.2 : ℝ)
    have he := Real.sq_sqrt hK
    nlinarith [sq_nonneg (Real.sqrt (e.2.2.2 : ℝ) - 1)]
  have hprod : (e.2.2.1 : ℝ) * Real.sqrt (e.2.2.2 : ℝ) ≤ (e.1.1 : ℝ) + 1 :=
    (mul_le_mul_of_nonneg_right hτ1 (Real.sqrt_nonneg _)).trans
      (by simpa only [one_mul] using hroot)
  have htarget : coulombTargetLipschitzConstant (GaussianFrequency.frequency rho)
      e.2.2.1 e.2.2.2 =
      ((e.2.2.1 : ℝ) * Real.sqrt (e.2.2.2 : ℝ)) * targetModulusBase rho := by
    unfold coulombTargetLipschitzConstant targetModulusBase
    ring
  have htargetBound := mul_le_mul_of_nonneg_right hprod hA
  have hguard := mul_le_mul_of_nonneg_right (lipschitzGuard_bound rho)
    (show (0 : ℝ) ≤ (e.2.1 : ℝ) + e.1.1 + 1 by positivity)
  unfold residualLipschitz
  rw [htarget]
  have hcross : 0 ≤ (planarHoppingLipschitzConstant : ℝ) * ((e.1.1 : ℝ) + 1) +
      targetModulusBase rho * (e.2.1 : ℝ) := by positivity
  nlinarith

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
