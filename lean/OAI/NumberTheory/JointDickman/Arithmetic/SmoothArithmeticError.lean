import OAI.NumberTheory.JointDickman.Arithmetic.SmoothArithmeticTensor

namespace OAI

/-! # Positive domination of smooth-weight approximation errors -/

namespace JointDickman
open Finset

theorem geometricSmoothArithmeticSum_sub (B j : ℕ) (a b l u T t : ℝ)
    (S : Finset ℤ) (W V : ℤ → ℝ → ℝ → ℝ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    geometricSmoothArithmeticSum B j a b l u T t S (fun k x y z => W k x y z-V k x y z) g h =
      geometricSmoothArithmeticSum B j a b l u T t S W g h-
        geometricSmoothArithmeticSum B j a b l u T t S V g h := by
  unfold geometricSmoothArithmeticSum
  rw [← mul_sub,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro k _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro c _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro n₂ _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro n₁ _
  split_ifs <;> ring

theorem geometricSmoothArithmeticSum_smul (B j : ℕ) (a b l u T t : ℝ)
    (S : Finset ℤ) (W : ℤ → ℝ → ℝ → ℝ → ℝ) (r : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    geometricSmoothArithmeticSum B j a b l u T t S (fun k x y z => r*W k x y z) g h =
      r*geometricSmoothArithmeticSum B j a b l u T t S W g h := by
  unfold geometricSmoothArithmeticSum
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

theorem geometricSmoothArithmeticSum_abs_le (B j : ℕ) (a b l u T t : ℝ)
    (S : Finset ℤ) (W V : ℤ → ℝ → ℝ → ℝ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (hWV : ∀ k ∈ S, ∀ x y z, |W k x y z| ≤ V k x y z) :
    |geometricSmoothArithmeticSum B j a b l u T t S W g h| ≤
      geometricSmoothArithmeticSum B j a b l u T t S V (fun _ => 1) (fun _ => 1) := by
  have hmass (f : (auxiliaryPrimes B → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) (n : ℕ) :
      |signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) f) n| ≤
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) (fun _ => 1)) n := by
    have hunit : subsetSiteTest (auxiliaryPrimes B) (fun _ => 1) = (fun _ => 1) := rfl
    rw [hunit,signedSplitProductMass_one]
    exact signedSplitProductMass_abs_le (auxiliaryPrimes_prime B) (fun _ _ => hf _) n
  have hmass0 (n : ℕ) :
      0 ≤ signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) (fun _ => 1)) n :=
    (abs_nonneg _).trans (hmass (fun _ => 1) (by simp) n)
  unfold geometricSmoothArithmeticSum
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg B)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro k hk
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro c _
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro n₂ _
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro n₁ _
  split_ifs
  · simp only [abs_mul,abs_of_nonneg (coefficientWeight_nonneg B c)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul (hmass g hg n₁) (hmass h hh n₂)
        (abs_nonneg _) (hmass0 _)) (coefficientWeight_nonneg B c))
      (hWV k hk _ _ _) (abs_nonneg _)
      (mul_nonneg (mul_nonneg (hmass0 n₁) (hmass0 n₂)) (coefficientWeight_nonneg B c))
  · simp

end JointDickman

end OAI
