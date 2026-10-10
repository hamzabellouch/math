import OAI.NumberTheory.JointDickman.Amplification.WeightedArithmeticFeatures
import OAI.NumberTheory.JointDickman.Probability.TensorCutoff

namespace OAI

/-! # Finite tensor expansion of the full smooth arithmetic weight -/

namespace JointDickman
open Finset

noncomputable def geometricSmoothArithmeticSum (B j : ℕ) (a b l u T t : ℝ)
    (S : Finset ℤ) (W : ℤ → ℝ → ℝ → ℝ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) : ℝ :=
  B*∑ k ∈ S,
    ∑ c ∈ Ioc ⌊l*(Real.exp ((k : ℝ)*t)/T)⌋₊ ⌊u*(Real.exp ((k : ℝ)*t)/T)⌋₊,
    ∑ n₂ ∈ Ioc ⌊a*Real.exp ((k : ℝ)*t)⌋₊ ⌊b*Real.exp ((k : ℝ)*t)⌋₊,
    ∑ n₁ ∈ Ioc ⌊a*Real.exp ((k : ℝ)*t)⌋₊ ⌊b*Real.exp ((k : ℝ)*t)⌋₊,
      if n₁ = n₂+j*c then
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) n₁*
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) n₂*
        coefficientWeight B c*
        W k (n₁/Real.exp ((k : ℝ)*t)) (n₂/Real.exp ((k : ℝ)*t))
          (c/(Real.exp ((k : ℝ)*t)/T))
      else 0

theorem geometricSmoothArithmeticSum_separated (B j : ℕ) (a b l u T t : ℝ)
    (S : Finset ℤ) (r : ℤ → ℝ) (w₁ w₂ w₃ : ℝ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    geometricSmoothArithmeticSum B j a b l u T t S
      (fun k x y z => r k*w₁ x*w₂ y*w₃ z) g h =
      weightedGeometricArithmeticSum B j a b l u T t S r g h w₁ w₂ w₃ := by
  unfold geometricSmoothArithmeticSum weightedGeometricArithmeticSum
  simp only [mul_sum]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro n₂ _
  apply sum_congr rfl
  intro n₁ _
  split_ifs <;> ring

theorem geometricSmoothArithmeticSum_sum {ι : Type*} (I : Finset ι)
    (B j : ℕ) (a b l u T t : ℝ) (S : Finset ℤ)
    (W : ι → ℤ → ℝ → ℝ → ℝ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    geometricSmoothArithmeticSum B j a b l u T t S
      (fun k x y z => ∑ d ∈ I, W d k x y z) g h =
      ∑ d ∈ I, geometricSmoothArithmeticSum B j a b l u T t S (W d) g h := by
  classical
  unfold geometricSmoothArithmeticSum
  simp only [mul_sum]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro k _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro c _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro n₂ _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro n₁ _
  split_ifs <;> simp [mul_sum]

theorem geometricSmoothArithmeticSum_tensor (P : MvPolynomial (Fin 4) ℝ)
    (s : ℤ → ℝ) (B j : ℕ) (a b l u T t : ℝ) (S : Finset ℤ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    geometricSmoothArithmeticSum B j a b l u T t S
      (fun k x y z => MvPolynomial.eval ![x,y,z,s k] P*
        tensorBoxBump x*tensorBoxBump y*tensorBoxBump z) g h =
      ∑ d ∈ P.support, weightedGeometricArithmeticSum B j a b l u T t S
        (fun k => P.coeff d*(s k)^(d 3)) g h
        (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2)) := by
  simp_rw [tensor_polynomial_expansion]
  rw [geometricSmoothArithmeticSum_sum]
  apply sum_congr rfl
  intro d _
  exact geometricSmoothArithmeticSum_separated _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end JointDickman

end OAI
