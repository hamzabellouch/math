import OAI.NumberTheory.Ostmann.Construction.OriginalSmallMoment
import OAI.NumberTheory.Ostmann.Construction.OriginalLargeMoment
import OAI.NumberTheory.Ostmann.Construction.OriginalOffWitnessMoment
import OAI.NumberTheory.Ostmann.Construction.OriginalOuterMoment
import OAI.NumberTheory.Ostmann.Construction.OriginalMomentBudget

namespace OAI

/-! # Positive probability for the original quadratic witness -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap Classical

theorem eventual_original_witness_probability (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (N Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      2 ≤ Q.toList.prod →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
      ∀ (h₀ : ℕ → ℕ) (θ R : ℕ → ℝ),
      (∀ m ∈ primeSubsetProducts P k,
        h₀ m < Q.toList.prod ∧ 0 ≤ θ m ∧ θ m ≤ 1 ∧ 1 ≤ R m ∧
        R m ≤ Real.exp (14 * T) ∧
        (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R m) →
      (∀ m ∈ primeSubsetProducts P k, H * R m * Q.toList.prod ≤ N) →
      Real.exp ((3 / 200 : ℝ) * Q.card) ≤ (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖originalPositiveFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖) →
      Real.exp (-(Q.card : ℝ) / 5) ≤ (P.card.choose k : ℝ)⁻¹ *
        ((primeSubsetProducts P k).filter (fun m =>
          principalSmallWitness Q hQ D m N (h₀ m) (θ m) (R m) Φ)).card := by
  classical
  filter_upwards [eventual_original_small_second_moment hB Cpop hCpop H Φ hH hΦ,
    eventual_original_large_first_moment hB Cpop hCpop H Φ hH hΦ,
    eventual_original_off_witness_mean hB Cpop hCpop H Φ hH hΦ,
    eventual_original_outer_first_moment hB Cpop hCpop H Φ hH hΦ,
    eventual_two_pow_moment_budget, eventually_ge_atTop (1 : ℝ)] with T hs hl ho hr hp hT
  intro Q hQ D P N Z k l hK hK3 hKU hlarge hL hL2 hP hodd hPZ hmin hZ hpop hZU hk hsize
    hkL hkU hll hlL hlU hN1 hN h₀ θ R hrange hcut hfirst
  have hQT : (Q.card : ℝ) ≤ T := hKU.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
      (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num))
  have hK3' : (3000 : ℝ) ≤ Q.card := by exact_mod_cast hK3
  have hK1 : 1 ≤ Q.card := by omega
  have hsecond := hs Q hQ D P N Z k l hK hQT hlarge hL hP hodd hPZ hZ hpop hZU
    hk hsize hkL hkU hll hlL hlU hN h₀ θ R hrange
  have hlargeMean := hl Q hQ D P N Z k l hK hQT hlarge hL hL2 hP hodd hPZ hZ hpop hZU
    hk hsize hkL hkU hll hlL hlU hN h₀ θ R hrange
  have hfail := ho Q hQ D P N Z k l hK hK1 hQT hlarge hL hP hodd hPZ hZ hpop hZU
    hk hsize hkL hkU hll hlL hlU hN h₀ θ R hrange
  have houter := hr Q hQ D P N Z k l hK hKU hlarge hL hP hodd hPZ hmin hZ hpop hZU
    hk hsize hkL hkU hll hlL hlU hN h₀ θ R (fun m hm =>
      ⟨(hrange m hm).1, (hrange m hm).2.1, (hrange m hm).2.2.1,
        (hrange m hm).2.2.2.1, (hrange m hm).2.2.2.2.1, hcut m hm⟩)
  have houterOne := houter.trans (original_outer_moment_budget T Q.card k hK3' hQT
    (hp k Q.card hk hkU hK))
  rw [← primeSubsetProducts_card P k hP] at hfirst hsecond hlargeMean hfail houterOne ⊢
  apply original_moment_witness_probability (primeSubsetProducts P k)
    (fun m => principalSmallWitness Q hQ D m N (h₀ m) (θ m) (R m) Φ)
    (fun m => ‖originalPositiveFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖)
    (fun m => ‖principalSmallFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖)
    (fun m => ‖principalLargeFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖)
    (fun m => ∑ d ∈ m.divisors.erase 1, ‖quadraticArrayStatistic
      (squarefreeKernelSupport Q.toList.prod N) m
      (arithmeticQuadraticCoefficient Q hQ D Φ (R m) d m (h₀ m) (θ m))‖)
    T Q.card hK3' hQT _ hfirst hsecond hlargeMean houterOne hfail
  intro m hm
  have hmpos : 0 < m := by
    have hh := primeSubsetProducts_mem_range P k Z hP hodd hPZ hm
    have hh' := Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1
    omega
  let : NeZero m := ⟨hmpos.ne'⟩
  exact originalPositiveFourier_norm_le_kernels Q hQ D m N (h₀ m) (θ m) (R m) H Φ
    (by have hh := (hrange m hm).2.2.2.1; linarith) hH hN1 (hcut m hm) hΦ

end Ostmann

end OAI
