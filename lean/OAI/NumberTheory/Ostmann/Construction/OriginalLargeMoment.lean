import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalFourierGrid
import OAI.NumberTheory.Ostmann.QuadraticCenter.LargeKernelFamily
import OAI.NumberTheory.Ostmann.Preliminaries.FiniteMomentPerturbation

namespace OAI

/-! # The first moment of the original large-kernel Fourier term -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_original_large_first_moment (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (N Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) → 2 ≤ Q.toList.prod →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (N : ℝ) ≤ Real.exp (14 * T) →
      ∀ (h₀ : ℕ → ℕ) (θ R : ℕ → ℝ),
      (∀ m ∈ primeSubsetProducts P k,
        h₀ m < Q.toList.prod ∧ 0 ≤ θ m ∧ θ m ≤ 1 ∧ 1 ≤ R m ∧
        R m ≤ Real.exp (14 * T) ∧
        (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R m) →
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖principalLargeFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖) ≤
        Real.exp ((9 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T) + Real.exp (-113 * T) := by
  filter_upwards [eventual_principalFourier_grid H Φ hH hΦ,
    eventual_large_kernel_prime_moment hB Cpop hCpop H Φ hH hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hgrid hm hT
  intro Q hQ D P N Z k l hK hQT hlarge hL hL2 hP hodd hPZ hZ hpop hZU hk hsize
    hkL hkU hl hlL hlU hN h₀ θ R hrange
  let S := largeSquarefreeKernels Q.toList.prod N
  let B := Real.exp ((9 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T)
  have hLe : (Q.toList.prod : ℝ) ≤ Real.exp T :=
    hL.trans (Real.exp_le_exp.mpr (by linarith))
  have hcard : (S.card : ℝ) ≤ Real.exp (14 * T) :=
    (Nat.cast_le.mpr (filteredKernel_card_le Q.toList.prod N _)).trans hN
  have hspec (s : ℕ) (hs : s ∈ S) := largeSquarefreeKernels_spec Q.toList.prod N s hL2 hs
  have hprodOdd (m : ℕ) (hm : m ∈ primeSubsetProducts P k) : Odd m :=
    (Finset.mem_filter.mp (primeSubsetProducts_mem_range P k Z hP hodd hPZ hm)).2.1
  have hcover (m : ℕ) (hmem : m ∈ primeSubsetProducts P k) :
      ∃ i : smallKernelParameters T Q.toList.prod,
        ‖principalLargeFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
          quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤
            Real.exp (-113 * T) := by
    obtain ⟨hh, hθ0, hθ1, hR, hRU, hmargin⟩ := hrange m hmem
    obtain ⟨i, hi, _, he⟩ := hgrid Q hQ D m N (h₀ m) (θ m) (R m) hQT hlarge hLe
      (hprodOdd m hmem) hh hθ0 hθ1 hR hRU hmargin hN
    exact ⟨⟨i, hi⟩, he⟩
  have hkP : k ≤ P.card := by nlinarith
  have hne : (primeSubsetProducts P k).Nonempty := by
    apply Finset.card_pos.mp
    rw [primeSubsetProducts_card P k hP]
    exact Nat.choose_pos hkP
  obtain ⟨m₀, hm₀⟩ := hne
  obtain ⟨i₀, _⟩ := hcover m₀ hm₀
  have hex (m : ℕ) : ∃ i : smallKernelParameters T Q.toList.prod,
      m ∈ primeSubsetProducts P k →
        ‖principalLargeFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
          quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤
            Real.exp (-113 * T) := by
    by_cases hh : m ∈ primeSubsetProducts P k
    · obtain ⟨i, hi⟩ := hcover m hh
      exact ⟨i, fun _ => hi⟩
    · exact ⟨i₀, fun h => (hh h).elim⟩
  choose pick hpick using hex
  let SR := S.biUnion Nat.primeFactors
  have hmoment := hm Q hQ D P S SR N Z k l hK hQT hlarge hL
    (fun s hs => (hspec s hs).2.2.1)
    (fun s hs => Finset.subset_biUnion_of_mem Nat.primeFactors hs)
    (fun s hs => ⟨(hspec s hs).2.2.2.2, (hspec s hs).2.2.2.1.symm⟩) hP hodd
    (fun s hs => (hspec s hs).2.1) hPZ hcard hZ hpop hZU hk hsize hkL hkU hl hlL hlU hN
    (fun m => ⟨(pick m).val, smallKernelParameters_principal T Q.toList.prod (pick m).property⟩)
  have hmean := quadraticArrayStatistic_mean_of_moment P S k l
    (fun i : smallKernelParameters T Q.toList.prod => fixedQuadraticCoefficient T Q hQ D Φ i)
    pick B hP hl (by positivity) (by simpa only [quadraticArrayStatistic] using hmoment)
  rw [← primeSubsetProducts_card P k hP]
  rw [← primeSubsetProducts_card P k hP] at hmean
  apply finite_mean_pointwise_le_add _ _ _ (Real.exp (-113 * T)) B (Real.exp_nonneg _) _ hmean
  intro m hmem
  have hp := hpick m hmem
  have hh := norm_add_le
    (principalLargeFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
      quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ (pick m)))
    (quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ (pick m)))
  simp only [sub_add_cancel] at hh
  linarith

end Ostmann

end OAI
