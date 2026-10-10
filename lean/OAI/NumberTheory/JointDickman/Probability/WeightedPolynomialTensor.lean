import OAI.NumberTheory.JointDickman.Probability.UniformTensorApproximation

namespace OAI

/-! # A bounded scalar weight in the compact tensor approximation -/
namespace JointDickman
open Finset
open scoped Topology

theorem geometricSmoothArithmeticSum_weighted_tensor (P : MvPolynomial (Fin 4) ℝ)
    (s r : ℤ → ℝ) (B j : ℕ) (a b l u T t : ℝ) (S : Finset ℤ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    geometricSmoothArithmeticSum B j a b l u T t S
      (fun k x y z => r k*(MvPolynomial.eval ![x,y,z,s k] P*
        tensorBoxBump x*tensorBoxBump y*tensorBoxBump z)) g h =
      ∑ d ∈ P.support, weightedGeometricArithmeticSum B j a b l u T t S
        (fun k => r k*(P.coeff d*(s k)^(d 3))) g h
        (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2)) := by
  simp_rw [tensor_polynomial_expansion,mul_sum]
  rw [geometricSmoothArithmeticSum_sum]
  apply sum_congr rfl
  intro d _
  have he (k : ℤ) (x y z : ℝ) :
      r k*(P.coeff d*(s k)^(d 3)*tensorPowerFactor (d 0) x*
        tensorPowerFactor (d 1) y*tensorPowerFactor (d 2) z) =
      (r k*(P.coeff d*(s k)^(d 3)))*tensorPowerFactor (d 0) x*
        tensorPowerFactor (d 1) y*tensorPowerFactor (d 2) z := by ring
  simp_rw [he]
  exact geometricSmoothArithmeticSum_separated _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem weighted_smooth_tensor_approximation (F : (Fin 4 → ℝ) → ℝ)
    (hF : ContinuousOn F tensorParameterBox) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 4) ℝ, ∀ (B j : ℕ) (a b l u T t : ℝ) (S : Finset ℤ)
      (s : ℤ → ℝ), (∀ k ∈ S, |s k| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ 1) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      |geometricSmoothArithmeticSum B j a b l u T t S
          (fun k x y z => r k*(F ![x,y,z,s k]*tensorCutoff x y z)) g h-
        geometricSmoothArithmeticSum B j a b l u T t S
          (fun k x y z => r k*(MvPolynomial.eval ![x,y,z,s k] P*tensorCutoff x y z)) g h| ≤
        ε*geometricSmoothArithmeticSum B j a b l u T t S
          (fun _ x y z => tensorCutoff x y z) (fun _ => 1) (fun _ => 1) := by
  obtain ⟨P,hP⟩ := uniform_tensor_approximation F hF hε
  refine ⟨P,?_⟩
  intro B j a b l u T t S s hs r hr g h hg hh
  rw [← geometricSmoothArithmeticSum_sub,← geometricSmoothArithmeticSum_smul]
  apply geometricSmoothArithmeticSum_abs_le B j a b l u T t S _ _ g h hg hh
  intro k hk x y z
  rw [← mul_sub,abs_mul]
  exact (mul_le_mul (hr k hk) (hP (s k) (hs k hk) x y z) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
end JointDickman

end OAI
