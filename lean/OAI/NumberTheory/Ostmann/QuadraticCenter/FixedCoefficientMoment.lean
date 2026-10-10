import OAI.NumberTheory.Ostmann.QuadraticCenter.OffWitnessFamily
import OAI.NumberTheory.Ostmann.QuadraticCenter.UniformPrimeProductMoment

namespace OAI

/-! # Applying the published Bonami input to the actual fixed coefficient family -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_fixed_coefficient_moment (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H η : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H) (hη : 0 < η)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (J : Finset QuadraticFamilyIndex)
      (P S R : Finset ℕ) (U Z k l : ℕ) (α : ℝ),
      J ⊆ quadraticFamilyParameters T Q.toList.prod →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (U : ℝ) ≤ Real.exp (500 * T) →
      (∀ i ∈ J, Real.sqrt (∑ s ∈ S, (((2 * l : ℕ) : ℝ) ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤ Real.exp (α * Q.card)) →
      ∀ pick : ℕ → J,
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ (pick m)) s *
            (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
        (Real.exp ((α + η) * Q.card) + Real.exp (-10 * T)) ^ (2 * l) := by
  filter_upwards [eventual_uniform_prime_product_moment hB Cpop (η / 1000)
      (by linarith) (by positivity),
    eventual_quadraticFamilyParameters_card,
    eventual_fixed_quadratic_family_mass H Φ hH hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hm hcard hmass hT
  intro Q hQ D J P S R U Z k l α hJ hK hQT hlarge hL hS hSR hP hodd hSU hPZ hScard
    hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU hnorm pick
  have hJcard : (Fintype.card J : ℝ) ≤ Real.exp (Cpop * T) := by
    have hc : (J.card : ℝ) ≤ ((quadraticFamilyParameters T Q.toList.prod).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hJ)
    rw [Fintype.card_coe]
    exact (hc.trans (hcard Q.toList.prod hL)).trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hCpop) hT]))
  have hSpos : ∀ s ∈ S, 0 < s := fun s hs => Nat.pos_of_ne_zero (hS s hs).ne_zero
  have hmass' (i : J) : (∑ s : S,
      ‖rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s‖) ≤ Real.exp (16 * T) :=
    hmass Q hQ D S hQT hlarge hL hSpos hScard i (hJ i.property)
  have he (i : J) :
      (∑ s : S, ((2 * l : ℕ) : ℝ) ^ s.val.primeFactors.card *
        ‖rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s‖ ^ 2) ≤
        Real.exp (2 * (α * Q.card)) := by
    rw [rootNormalizedCoefficient_energy]
    have hh := (Real.sqrt_le_iff.mp (hnorm i i.property)).2
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hh
  have hh := hm P S R U Z k l hS hSR hP hodd hSU hPZ hZ hpop hZU hk hsize hkL hkU hl
    hlL hlU hJcard (hU.trans (Real.exp_le_exp.mpr (by nlinarith))) (fun i s => rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s)
    pick (Real.exp (2 * (α * Q.card))) (Real.exp (16 * T)) (Real.exp_nonneg _) (Real.exp_nonneg _)
    (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hCpop) hT])) he hmass'
  apply hh.trans
  apply pow_le_pow_left₀ (by positivity)
  apply add_le_add_left
  rw [← Real.exp_half, show 2 * (α * Q.card) / 2 = α * Q.card by ring, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hkη := mul_le_mul_of_nonneg_left hK hη.le
  nlinarith

end Ostmann

end OAI
