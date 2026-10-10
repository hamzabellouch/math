import OAI.NumberTheory.Ostmann.Construction.OriginalPositiveFirstMoment
import OAI.NumberTheory.Ostmann.Construction.OriginalWitnessProbability
import OAI.NumberTheory.Ostmann.Characters.FourierGridMargin

namespace OAI

/-! # A positive family of simultaneous lifts from the original tail data -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

/-- This combines the physical amplification, Poisson, fixed-family moments,
and inverse phase argument. No Fourier moment or witness event is assumed. -/
theorem eventual_original_lift_probability (hBonami : PublishedBonamiBound)
    (cψ a c C B : ℝ) (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c)
    (hC : 500 ≤ C) (hB : 3 ≤ B) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, B ^ 2 < |x| → 𝓕 ψ x = 0) (hCψ : (𝓕 ψ 0).re ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (X : ℝ),
      0 < X → B ^ 2 < X / Q.toList.prod →
      ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k l N Z : ℕ, 1 ≤ k → Even k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      2 ≤ Q.toList.prod →
      Real.exp T ≤ C * T * P.card → X ≤ Real.exp ((k : ℝ) * T) →
      (∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M) →
      (∀ p ∈ P, p ≤ Z) → (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      1 ≤ Z → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
      (∀ M ∈ primeSubsetProducts P k,
        B ^ 2 * ((M : ℝ) / X) * Q.toList.prod ≤ N ∧
        Real.exp (10 * T) ≤ (M : ℝ) / X ∧ (M : ℝ) / X ≤ Real.exp (14 * T)) →
      Real.exp (-(Q.card : ℝ) / 5) ≤ (Fintype.card (Fin k ↪ P) : ℝ)⁻¹ *
        (tupleLiftFamily P k ⌈Real.exp (13 * T / 100)⌉₊
          ⌈X * Real.exp (13 * T / 100)⌉₊ t).card := by
  have hsupport (x : ℝ) (hx : B ^ 2 < x) : 𝓕 ψ x = 0 := hsupp x (hx.trans_le (le_abs_self x))
  filter_upwards [eventual_original_positive_mean cψ a c C hcψ ha hc (by linarith),
    eventual_original_witness_probability hBonami C hC (B ^ 2) (𝓕 ψ) (sq_nonneg _) hsupport,
    eventual_original_tuple_witness_lift B (𝓕 ψ) hB hsupport,
    eventually_ge_atTop (1 : ℝ)] with T hfirst hprob hlift hT
  intro Q P hQ hP hodd D X hX hBX S hS hsize hD hSD ε t hε hbias k l N Z
    hk heven hksize hkL hkU hK hK3 hKU hlarge hL hL2 hpop hXk hcop hPZ hmin
    hZ hZU hl hlL hlU hN1 hN hscale
  have hkP : k ≤ P.card := by nlinarith
  have hpopC : Real.exp T ≤ C * T * P.card := hpop.trans (by
    gcongr)
  obtain ⟨τ, h₀, hphase, hmean⟩ := hfirst Q P hQ hP hodd D ψ X (B ^ 2)
    hX (sq_nonneg _) hreal hψ0 hψ1 hBX hsupp hCψ S hS hsize hD hSD ε t hε hbias
    k N hk heven hkP hkU hK (by exact_mod_cast hK3) hpopC hXk hcop
    (fun m hm => (hscale m hm).1)
  have hphaseRange (m : ℕ) (hm : m ∈ primeSubsetProducts P k) :
      h₀ m < Q.toList.prod ∧ 0 ≤ (τ m : ℝ) / m ∧ (τ m : ℝ) / m ≤ 1 ∧
      1 ≤ (m : ℝ) / X ∧ (m : ℝ) / X ≤ Real.exp (14 * T) ∧
      (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ (m : ℝ) / X := by
    obtain ⟨ht0, htM, hh, _, _⟩ := hphase m hm
    have hm0 : (0 : ℝ) < m := by
      have hm' : (0 : ℤ) < m := ht0.trans_lt htM
      exact_mod_cast hm'
    refine ⟨hh, div_nonneg (by exact_mod_cast ht0) hm0.le,
      (div_le_one hm0).mpr (by exact_mod_cast htM.le), ?_, (hscale m hm).2.2, ?_⟩
    · exact (Real.one_le_exp (by linarith : 0 ≤ 10 * T)).trans (hscale m hm).2.1
    · exact fourier_grid_margin_of_prime_scale T _ _ hT hL (hscale m hm).2.1
  have hp := hprob Q hQ D P N Z k l hK hK3 hKU hlarge
    (hL.trans (Real.exp_le_exp.mpr (by linarith))) hL2 hP hodd hPZ hmin hZ hpop hZU
    hk hksize hkL hkU hl hlL hlU hN1 hN h₀ (fun m => (τ m : ℝ) / m)
    (fun m => (m : ℝ) / X) hphaseRange (fun m hm => (hscale m hm).1) hmean
  apply hp.trans
  apply tupleLiftFamily_probability P hP k _ _ t
    (fun m => principalSmallWitness Q hQ D m N (h₀ m) ((τ m : ℝ) / m) ((m : ℝ) / X) (𝓕 ψ))
  apply hlift Q hQ D P hP k N t τ h₀ X hX hL hKU
  intro m hm
  refine ⟨(hscale m hm).2.1, (hscale m hm).2.2, ?_⟩
  intro p hp
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub (t p) (τ m) p).mp ((hphase m hm).2.2.2.2 p hp).symm

end Ostmann

end OAI
