import OAI.NumberTheory.Ostmann.QuadraticCenter.OuterDivisorParameters
import OAI.NumberTheory.Ostmann.QuadraticCenter.OuterKernelFamily
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalFourierGrid
import OAI.NumberTheory.Ostmann.Preliminaries.FiniteMaximumTransfer

namespace OAI

/-! # The first moment of the genuine nontrivial outer-divisor terms -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_original_outer_first_moment (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (N Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (N : ℝ) ≤ Real.exp (14 * T) →
      ∀ (h₀ : ℕ → ℕ) (θ R : ℕ → ℝ),
      (∀ m ∈ primeSubsetProducts P k,
        h₀ m < Q.toList.prod ∧ 0 ≤ θ m ∧ θ m ≤ 1 ∧ 1 ≤ R m ∧
        R m ≤ Real.exp (14 * T) ∧ H * R m * Q.toList.prod ≤ N) →
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k, ∑ d ∈ m.divisors.erase 1,
          ‖quadraticArrayStatistic (squarefreeKernelSupport Q.toList.prod N) m
            (arithmeticQuadraticCoefficient Q hQ D Φ (R m) d m (h₀ m) (θ m))‖) ≤
        (2 : ℝ) ^ k * (Real.exp ((-799 / 1000 : ℝ) * Q.card) +
          Real.exp (-10 * T) + Real.exp (-113 * T)) := by
  classical
  filter_upwards [eventual_fixed_quadratic_family_covers H Φ hH hΦ,
    eventual_outer_kernel_prime_moment hB Cpop hCpop H Φ hH hΦ,
    eventually_ge_atTop (1 : ℝ)] with T hgrid hm hT
  intro Q hQ D P N Z k l hK hKU hlarge hL hP hodd hPZ hmin hZ hpop hZU hk hsize
    hkL hkU hl hlL hlU hN h₀ θ R hrange
  let A := primeSubsetProducts P k
  let S := squarefreeKernelSupport Q.toList.prod N
  let active (m : ℕ) := (m.divisors.erase 1).filter (fun d => d ^ 2 ≤ N)
  let f (m d : ℕ) := ‖quadraticArrayStatistic S m
    (arithmeticQuadraticCoefficient Q hQ D Φ (R m) d m (h₀ m) (θ m))‖
  let g (m : ℕ) (i : outerQuadraticParameters T Q.toList.prod) :=
    ‖quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i)‖
  let B := Real.exp ((-799 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T)
  have hQT : (Q.card : ℝ) ≤ T := hKU.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
      (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num))
  have hLe : (Q.toList.prod : ℝ) ≤ Real.exp T :=
    hL.trans (Real.exp_le_exp.mpr (by linarith))
  have hspec (s : ℕ) (hs : s ∈ S) := (mem_squarefreeKernelSupport Q.toList.prod N s).mp hs
  have hcard : (S.card : ℝ) ≤ Real.exp (14 * T) :=
    (Nat.cast_le.mpr (squarefreeKernelSupport_card_le Q.toList.prod N)).trans hN
  have hcover (m : ℕ) (hmem : m ∈ A) (d : ℕ) (hd : d ∈ active m) :
      ∃ i : outerQuadraticParameters T Q.toList.prod, f m d ≤ g m i + Real.exp (-113 * T) := by
    obtain ⟨hdM, hdN⟩ := Finset.mem_filter.mp hd
    obtain ⟨hh, hθ0, hθ1, hR, hRU, _⟩ := hrange m hmem
    have hd0 : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hdM)
    have hdU := outerDivisor_upper T N d hN hdN
    have hmOdd : Odd m :=
      (Finset.mem_filter.mp (primeSubsetProducts_mem_range P k Z hP hodd hPZ hmem)).2.1
    obtain ⟨i, hi, hid, _, he⟩ := hgrid Q hQ D m (h₀ m) d (θ m) (R m)
      hQT hlarge hLe hmOdd hh hd0 hdU hθ0 hθ1 hR hRU
    have hiO : i ∈ outerQuadraticParameters T Q.toList.prod :=
      Finset.mem_filter.mpr ⟨hi, hid ▸ primeProduct_divisor_lower P hP k m d
        (Real.exp T) hmin hmem hdM⟩
    have herr : ‖quadraticArrayStatistic S m
        (arithmeticQuadraticCoefficient Q hQ D Φ (R m) d m (h₀ m) (θ m)) -
        quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤
        Real.exp (-113 * T) := by
      apply quadraticArrayStatistic_grid_error
      · exact fun s hs => (hspec s hs).1
      · exact hcard
      · exact fun s hs => he s (hspec s hs).1 ((Nat.cast_le.mpr (hspec s hs).2.1).trans hN)
    refine ⟨⟨i, hiO⟩, ?_⟩
    have hh := norm_add_le
      (quadraticArrayStatistic S m (arithmeticQuadraticCoefficient Q hQ D Φ (R m) d m (h₀ m) (θ m)) -
        quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i))
      (quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i))
    simp only [sub_add_cancel] at hh
    change _ ≤ _ + _
    exact hh.trans (by linarith)
  have hmean (pick : ℕ → outerQuadraticParameters T Q.toList.prod) :
      (A.card : ℝ)⁻¹ * (∑ m ∈ A, g m (pick m)) ≤ B := by
    let SR := S.biUnion Nat.primeFactors
    have hmoment := hm Q hQ D P S SR N Z k l hK hKU hlarge hL
      (fun s hs => (hspec s hs).2.2.1)
      (fun s hs => Finset.subset_biUnion_of_mem Nat.primeFactors hs) hP hodd
      (fun s hs => (hspec s hs).2.1) hPZ hcard hZ hpop hZU hk hsize hkL hkU hl hlL hlU hN pick
    have hh := quadraticArrayStatistic_mean_of_moment P S k l
      (fun i : outerQuadraticParameters T Q.toList.prod => fixedQuadraticCoefficient T Q hQ D Φ i)
      pick B hP hl (by positivity) (by simpa only [quadraticArrayStatistic] using hmoment)
    simpa only [A, g, primeSubsetProducts_card P k hP] using hh
  have htrim (m : ℕ) (hmem : m ∈ A) :
      (∑ d ∈ m.divisors.erase 1, f m d) = ∑ d ∈ active m, f m d := by
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hn : d ^ 2 ≤ N
    · simp only [hn, ite_true]
    · simp only [hn, ite_false]
      symm
      change ‖quadraticArrayStatistic S m _‖ = 0
      rw [quadraticArrayStatistic_zero_outer Q hQ D m N d (h₀ m) (θ m) (R m) H Φ S
        (by have hh := (hrange m hmem).2.2.2.1; linarith) hH
        (fun s hs => (hspec s hs).1) (hrange m hmem).2.2.2.2.2 (Nat.lt_of_not_ge hn) hΦ,
        norm_zero]
  rw [← primeSubsetProducts_card P k hP]
  change (A.card : ℝ)⁻¹ * (∑ m ∈ A, ∑ d ∈ m.divisors.erase 1, f m d) ≤ _
  rw [Finset.sum_congr rfl htrim]
  apply finite_inner_sum_mean_le A active f g ((2 : ℝ) ^ k) (Real.exp (-113 * T)) B
    (by positivity) (by positivity) (by positivity)
    (fun _ _ _ _ => norm_nonneg _) (fun _ _ _ => norm_nonneg _) _ hcover hmean
  intro m hm
  have hc : (active m).card ≤ m.divisors.card :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans
      (Finset.card_le_card (Finset.erase_subset _ _))
  have he := primeProduct_divisors_card P hP k m hm
  exact_mod_cast hc.trans_eq he

end Ostmann

end OAI
