import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveQuadraticUniformBound
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootNormalizedCoefficient

namespace OAI

/-! # A uniform absolute-mass bound for the original coefficient arrays -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem primeDivisorPositive_uniform_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (U : Finset ℕ) (hU : U ∈ P.powerset) :
    ‖primeDivisorPositive P hP D a θ Φ R v U s‖ ≤
      Real.sqrt P.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H := by
  classical
  have hUP := Finset.mem_powerset.mp hU
  have hp : ∀ p ∈ U, p.Prime := fun p hp => hP p (hUP hp)
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hp)).ne'⟩
  rw [primeDivisorPositive, dite_eq_left hUP]
  apply (positiveQuadraticSum_energy_uniform_bound _ (densityCRTList_energy _ _ _ _)
    (a U) (θ U) Φ R v H s hR hv hH hs hΦ).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.sqrt_le_sqrt
  exact_mod_cast primeSet_prod_le_of_subset P U hP hUP

theorem primeDivisorPositive_combination_uniform_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (c : Finset ℕ → ℂ)
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) :
    ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ≤
      (Real.sqrt P.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
        (1 + 1 / 16 : ℝ) ^ P.card := by
  let B := Real.sqrt P.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ U ∈ P.powerset, ‖c U * primeDivisorPositive P hP D a θ Φ R v U s‖ := norm_sum_le _ _
    _ ≤ ∑ U ∈ P.powerset, (1 / 16 : ℝ) ^ U.card * B := by
      apply Finset.sum_le_sum
      intro U hU
      rw [norm_mul]
      exact mul_le_mul (hc U hU)
        (primeDivisorPositive_uniform_bound P hP D a θ Φ R v H s hR hv hH hs hΦ U hU)
        (norm_nonneg _) (by positivity)
    _ = B * (1 + 1 / 16 : ℝ) ^ P.card := by
      rw [← Finset.sum_mul, sum_powerset_power_card, mul_comm]

theorem rootNormalizedCoefficient_norm_le (F : ℕ → ℂ) (s : ℕ) (hs : 0 < s) :
    ‖rootNormalizedCoefficient F s‖ ≤ ‖F s‖ := by
  have hsq : (1 : ℝ) ≤ Real.sqrt s := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hs
  have hi : (Real.sqrt (s : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsq
  rw [rootNormalizedCoefficient, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) hi

theorem rootNormalizedCoefficient_mass_le (S : Finset ℕ) (F : ℕ → ℂ) (B : ℝ)
    (hS : ∀ s ∈ S, 0 < s) (hF : ∀ s ∈ S, ‖F s‖ ≤ B) :
    (∑ s : S, ‖rootNormalizedCoefficient F s‖) ≤ (S.card : ℝ) * B := by
  calc
    _ = ∑ s ∈ S, ‖rootNormalizedCoefficient F s‖ :=
      Finset.sum_coe_sort S (fun s : ℕ => ‖rootNormalizedCoefficient F s‖)
    _ ≤ ∑ _s ∈ S, B := Finset.sum_le_sum (fun s hs =>
      (rootNormalizedCoefficient_norm_le F s (hS s hs)).trans (hF s hs))
    _ = _ := by simp

end Ostmann

end OAI
