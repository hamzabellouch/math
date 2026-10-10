import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalFourierGrid
import OAI.NumberTheory.Ostmann.QuadraticCenter.OffWitnessStatistic
import OAI.NumberTheory.Ostmann.Preliminaries.FiniteMomentPerturbation

namespace OAI

/-! # The original small-kernel statistic on the event with no witness -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap Classical

noncomputable def principalSmallWitness (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : Prop :=
  ∃ s ∈ smallSquarefreeKernels Q.toList.prod N, ∃ V ∈ Q.powerset, ∃ U ∈ Q.powerset,
    Real.exp (-(Q.card : ℝ)) * (Real.sqrt 2) ^ U.card <
      ‖primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
        (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod U s‖

theorem eventual_original_off_witness_mean (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (N Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      1 ≤ Q.card → (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
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
        (∑ m ∈ (primeSubsetProducts P k).filter
          (fun m => ¬principalSmallWitness Q hQ D m N (h₀ m) (θ m) (R m) Φ),
          ‖principalSmallFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖) ≤
        Real.exp ((-797 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T) + Real.exp (-113 * T) := by
  filter_upwards [eventual_off_witness_family_covers H Φ hH hΦ,
    eventual_off_witness_prime_mean hB Cpop hCpop H Φ hH hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hgrid hm hT
  intro Q hQ D P N Z k l hK hK1 hQT hlarge hL hP hodd hPZ hZ hpop hZU hk hsize
    hkL hkU hl hlL hlU hN h₀ θ R hrange
  let S := smallSquarefreeKernels Q.toList.prod N
  let E := (primeSubsetProducts P k).filter
    (fun m => ¬principalSmallWitness Q hQ D m N (h₀ m) (θ m) (R m) Φ)
  have hES : E ⊆ primeSubsetProducts P k := Finset.filter_subset _ _
  by_cases hE : E.Nonempty
  · have hLe : (Q.toList.prod : ℝ) ≤ Real.exp T :=
      hL.trans (Real.exp_le_exp.mpr (by linarith))
    have hcard : (S.card : ℝ) ≤ Real.exp (14 * T) :=
      (Nat.cast_le.mpr (filteredKernel_card_le Q.toList.prod N _)).trans hN
    have hspec (s : ℕ) (hs : s ∈ S) := smallSquarefreeKernels_spec Q.toList.prod N s hs
    have hprodOdd (m : ℕ) (hm : m ∈ primeSubsetProducts P k) : Odd m :=
      (Finset.mem_filter.mp (primeSubsetProducts_mem_range P k Z hP hodd hPZ hm)).2.1
    have hcover (m : ℕ) (hmem : m ∈ E) :
        ∃ i : offWitnessParameters T Q hQ D Φ S,
          ‖principalSmallFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
            quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤
              Real.exp (-113 * T) := by
      have hmemP := hES hmem
      obtain ⟨hh, hθ0, hθ1, hR, hRU, hmargin⟩ := hrange m hmemP
      have hfail (s : ℕ) (hs : s ∈ S) (V : Finset ℕ) (hV : V ∈ Q.powerset)
          (U : Finset ℕ) (hU : U ∈ Q.powerset) :
          ‖primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue m) V)
            (fun _ => (h₀ m : ℝ) + θ m) Φ (R m) V.toList.prod U s‖ ≤
              Real.exp (-(Q.card : ℝ)) * (Real.sqrt 2) ^ U.card := by
        apply le_of_not_gt
        intro hbad
        exact (Finset.mem_filter.mp hmem).2 ⟨s, hs, V, hV, U, hU, hbad⟩
      obtain ⟨i, hi, he⟩ := hgrid Q hQ D m (h₀ m) (θ m) (R m) S hK1 hQT hlarge hLe
        (hprodOdd m hmemP) hh (fun s hs => ⟨(hspec s hs).1,
          (Nat.cast_le.mpr (hspec s hs).2.1).trans hN⟩)
        hθ0 hθ1 hR hRU hmargin hfail
      refine ⟨⟨i, hi⟩, ?_⟩
      exact quadraticArrayStatistic_grid_error T S m _ _
        (fun s hs => (hspec s hs).1) hcard he
    obtain ⟨m₀, hm₀⟩ := hE
    obtain ⟨i₀, _⟩ := hcover m₀ hm₀
    have hex (m : ℕ) : ∃ i : offWitnessParameters T Q hQ D Φ S, m ∈ E →
        ‖principalSmallFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
          quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤
            Real.exp (-113 * T) := by
      by_cases hh : m ∈ E
      · obtain ⟨i, hi⟩ := hcover m hh
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun h => (hh h).elim⟩
    choose pick hpick using hex
    let SR := S.biUnion Nat.primeFactors
    have hmean := hm Q hQ D P S SR N Z k l hK hQT hlarge hL
      (fun s hs => (hspec s hs).2.2.1)
      (fun s hs => Finset.subset_biUnion_of_mem Nat.primeFactors hs)
      hP hodd (fun s hs => (hspec s hs).2.1) hPZ hcard hZ hpop hZU hk hsize hkL hkU hl hlL hlU hN pick
    change (P.card.choose k : ℝ)⁻¹ * (∑ m ∈ primeSubsetProducts P k,
      ‖quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ (pick m))‖) ≤
      Real.exp ((-797 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T) at hmean
    rw [← primeSubsetProducts_card P k hP] at hmean ⊢
    apply finite_restricted_mean_pointwise_le_add _ E hES _ _ (Real.exp (-113 * T)) _
      (Real.exp_nonneg _) (fun _ _ => norm_nonneg _) _ hmean
    intro m hmem
    have hp := hpick m hmem
    have hh := norm_add_le
      (principalSmallFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
        quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ (pick m)))
      (quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ (pick m)))
    simp only [sub_add_cancel] at hh
    linarith
  · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    change _ * (∑ m ∈ E, _) ≤ _
    rw [he, Finset.sum_empty, mul_zero]
    positivity

end Ostmann

end OAI
