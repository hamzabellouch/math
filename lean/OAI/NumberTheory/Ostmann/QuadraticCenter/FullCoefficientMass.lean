import OAI.NumberTheory.Ostmann.QuadraticCenter.FixedQuadraticFamily

namespace OAI

/-! # Polynomial absolute mass for the full coefficient family -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem fullQuadraticCoefficient_norm_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R H : ℝ) (P : ℕ) (c ξ : Finset ℕ → ℂ) (s : ℕ)
    (hR : 0 < R) (hH : 0 ≤ H) (hP : 0 < P) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0)
    (hc : ∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) :
    ‖fullQuadraticCoefficient Q hQ D a θ Φ R P c ξ s‖ ≤
      ((Real.sqrt Q.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
        (1 + 1 / 16 : ℝ) ^ Q.card / P) *
          ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  apply divisorWeightedCoefficient_norm_le Q ξ _ s _ (by positivity) hξ
  intro V hV
  have hv : 0 < V.toList.prod := prime_list_prod_pos _
    (primeSet_list_prime V (fun p hp => hQ p (Finset.mem_powerset.mp hV hp)))
  exact primeDivisorMultiples_combination_bound Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod H s P
    hP hs hR (by exact_mod_cast hv) hH hΦ c hc

theorem eventual_full_coefficient_point_bound (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (R : ℝ) (P M h₀ s : ℕ) (θ : ℝ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      0 < R → 0 < P → 0 < s →
      ‖arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s‖ ≤ Real.exp (2 * T) := by
  let C := SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H
  filter_upwards [eventually_ge_atTop C, eventually_ge_atTop (0 : ℝ)] with T hTC hT
  intro Q hQ D R P M h₀ s θ hcard hlarge hL hR hP hs
  have hC : C ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hLs : Real.sqrt Q.toList.prod ≤ Real.exp (T / 50) := by
    apply (Real.sqrt_le_sqrt hL).trans_eq
    rw [← Real.exp_half]
    congr 1
    ring
  have he : (1 + 1 / 16 : ℝ) ^ Q.card ≤ Real.exp (T / 16) :=
    (sixteenth_divisor_weight_bound Q.card).trans (Real.exp_le_exp.mpr (by linarith))
  have hm : (∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹) ≤ Real.exp (T / 1000) :=
    (reciprocal_sqrt_divisor_mass_le Q hlarge).trans (Real.exp_le_exp.mpr (by linarith))
  have hb := fullQuadraticCoefficient_norm_le Q hQ D (quadraticInverseResidue M)
    (fun _ => (h₀ : ℝ) + θ) Φ R H P (quadraticSymbolCoefficient M)
    (quadraticDivisorSymbol M) s hR hH hP hs hΦ
    (fun U _ => quadraticSymbolCoefficient_norm_le M U)
    (fun V _ => quadraticDivisorSymbol_norm_le M V)
  apply hb.trans
  change ((Real.sqrt Q.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
    (1 + 1 / 16 : ℝ) ^ Q.card / P) * _ ≤ _
  rw [mul_assoc (Real.sqrt (Q.toList.prod : ℝ))]
  calc
    _ ≤ (Real.exp (T / 50) * Real.exp T * Real.exp (T / 16) / 1) * Real.exp (T / 1000) := by
      gcongr
      exact_mod_cast hP
    _ = Real.exp (T / 50 + T + T / 16 + T / 1000) := by
      rw [div_one, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventual_arithmetic_coefficient_mass (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (R : ℝ) (P M h₀ : ℕ) (θ : ℝ) (S : Finset ℕ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      0 < R → 0 < P → (∀ s ∈ S, 0 < s) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      (∑ s : S, ‖rootNormalizedCoefficient
        (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ) s‖) ≤ Real.exp (16 * T) := by
  filter_upwards [eventual_full_coefficient_point_bound H Φ hH hΦ] with T hp
  intro Q hQ D R P M h₀ θ S hcard hlarge hL hR hP hS hScard
  apply (rootNormalizedCoefficient_mass_le S _ (Real.exp (2 * T)) hS
    (fun s hs => hp Q hQ D R P M h₀ s θ hcard hlarge hL hR hP (hS s hs))).trans
  calc
    _ ≤ Real.exp (14 * T) * Real.exp (2 * T) :=
      mul_le_mul_of_nonneg_right hScard (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem eventual_fixed_quadratic_family_mass (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (S : Finset ℕ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, 0 < s) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      ∀ i ∈ quadraticFamilyParameters T Q.toList.prod,
      (∑ s : S, ‖rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s‖) ≤
        Real.exp (16 * T) := by
  filter_upwards [eventual_arithmetic_coefficient_mass H Φ hH hΦ] with T hm
  intro Q hQ D S hcard hlarge hL hS hScard i hi
  have hmem := (mem_quadraticFamilyParameters T Q.toList.prod i).mp hi
  have hR : 0 < quadraticGridScale (Real.exp (-200 * T)) i.2.2.2 := by
    unfold quadraticGridScale
    positivity
  exact hm Q hQ D _ _ _ _ _ S hcard hlarge hL hR hmem.2.2.1.1 hS hScard

end Ostmann

end OAI
