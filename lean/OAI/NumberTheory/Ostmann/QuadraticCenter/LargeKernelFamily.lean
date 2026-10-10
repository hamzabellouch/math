import OAI.NumberTheory.Ostmann.QuadraticCenter.FixedCoefficientMoment

namespace OAI

/-! # The fixed principal family on the large squarefree kernels -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def principalQuadraticParameters (T : ℝ) (L : ℕ) : Finset QuadraticFamilyIndex :=
  (quadraticFamilyParameters T L).filter (fun i => i.2.2.1 = 1)

theorem principalQuadraticParameters_subset (T : ℝ) (L : ℕ) :
    principalQuadraticParameters T L ⊆ quadraticFamilyParameters T L := Finset.filter_subset _ _

theorem eventual_large_kernel_family_norm (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hε : 0 < ε)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s) →
      (∀ s ∈ S, 4 * Q.toList.prod ^ 2 ≤ s ∧ s ≤ M) →
      (∀ s ∈ S, Q.toList.prod.Coprime s) →
      2 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (i : QuadraticFamilyIndex),
      i ∈ principalQuadraticParameters T Q.toList.prod →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤
        Real.exp ((7 / 1000 + ε) * Q.card) := by
  filter_upwards [eventual_full_large_kernel_norm C₀ H ε Φ hC₀ hH hε hΦ] with T hn
  intro Q hQ M S u hK hlarge hM hS hrange hcop hu huU D i hi
  have hp := (Finset.mem_filter.mp hi).2
  have hgrid : 0 < quadraticGridScale (Real.exp (-200 * T)) i.2.2.2 := by
    unfold quadraticGridScale
    positivity
  simp only [fixedQuadraticCoefficient, arithmeticQuadraticCoefficient, hp]
  exact hn Q hQ M S u hK hlarge hM hS hrange hcop hu huU D _ _ _ _ _
    hgrid
    (fun U _ => quadraticSymbolCoefficient_norm_le _ U)
    (fun V _ => quadraticDivisorSymbol_norm_le _ V)

theorem eventual_large_kernel_prime_moment (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P S R : Finset ℕ) (U Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ s ∈ S, 4 * Q.toList.prod ^ 2 ≤ s ∧ Q.toList.prod.Coprime s) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (U : ℝ) ≤ Real.exp (14 * T) →
      ∀ pick : ℕ → principalQuadraticParameters T Q.toList.prod,
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ (pick m)) s *
            (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
        (Real.exp ((9 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T)) ^ (2 * l) := by
  filter_upwards [eventual_fixed_coefficient_moment hB Cpop hCpop H (1 / 1000) Φ hH (by norm_num) hΦ,
    eventual_large_kernel_family_norm 14 H (1 / 1000) Φ (by norm_num) hH (by norm_num) hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hm hn hT
  intro Q hQ D P S R U Z k l hK hQT hlarge hL hS hSR hrange hP hodd hSU hPZ hScard
    hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU pick
  have hU500 : (U : ℝ) ≤ Real.exp (500 * T) :=
    hU.trans (Real.exp_le_exp.mpr (by linarith))
  have huU : ((2 * l : ℕ) : ℝ) ≤ 2 * T ^ (1 / 1000000 : ℝ) := by push_cast; linarith
  have he (i : QuadraticFamilyIndex) (hi : i ∈ principalQuadraticParameters T Q.toList.prod) :
      Real.sqrt (∑ s ∈ S, (((2 * l : ℕ) : ℝ) ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤ Real.exp ((8 / 1000 : ℝ) * Q.card) := by
    have hh := hn Q hQ U S ((2 * l : ℕ) : ℝ) hK hlarge hU hS
      (fun s hs => ⟨(hrange s hs).1, hSU s hs⟩) (fun s hs => (hrange s hs).2)
      (by exact_mod_cast (show 2 ≤ 2 * l by omega)) huU D i hi
    norm_num only at hh ⊢
    exact hh
  have hh := hm Q hQ D (principalQuadraticParameters T Q.toList.prod) P S R U Z k l (8 / 1000)
    (principalQuadraticParameters_subset _ _) hK hQT hlarge hL hS hSR hP hodd hSU hPZ
    hScard hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU500 he pick
  norm_num only at hh ⊢
  exact hh

end Ostmann

end OAI
