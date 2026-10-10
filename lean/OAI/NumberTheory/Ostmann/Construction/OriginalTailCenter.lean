import OAI.NumberTheory.Ostmann.Construction.OriginalLiftProbability
import OAI.NumberTheory.Ostmann.Construction.OriginalCommonCenter

namespace OAI

/-! # The original tail assumptions give a common rational center -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem eventual_original_tail_commonCenter (hBonami : PublishedBonamiBound)
    (cψ a c C B : ℝ) (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c)
    (hC : 500 ≤ C) (hB : 3 ≤ B) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, B ^ 2 < |x| → 𝓕 ψ x = 0) (hCψ : (𝓕 ψ 0).re ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime),
      ∀ hP : ∀ p ∈ P, p.Prime, (∀ p ∈ P, Odd p) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (X : ℝ),
      1 ≤ X → B ^ 2 < X / Q.toList.prod →
      ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k l N Z : ℕ, 10 ≤ k → Even k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      2 ≤ Q.toList.prod →
      Real.exp T ≤ C * T * P.card → (P.card : ℝ) ≤ Real.exp (T + 1) →
      X ≤ Real.exp (((k - 10 : ℕ) : ℝ) * T) →
      (∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M) →
      (∀ p ∈ P, p ≤ Z) → (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      1 ≤ Z → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
      (∀ M ∈ primeSubsetProducts P k,
        B ^ 2 * ((M : ℝ) / X) * Q.toList.prod ≤ N ∧
        Real.exp (10 * T) ≤ (M : ℝ) / X ∧ (M : ℝ) / X ≤ Real.exp (14 * T)) →
      ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊,
        ∃ n ∈ Finset.Ico (-(⌈X * Real.exp (13 * T / 100)⌉₊ : ℤ))
          (⌈X * Real.exp (13 * T / 100)⌉₊ + 1), ∃ h : ℤ, ∃ m : ℕ,
          0 < m ∧ m ≤ ⌈Real.exp (13 * T / 100)⌉₊ ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
          Real.exp (3 * T / 5) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
          (P.card : ℝ) * Real.exp (-T / (k - 1 : ℕ)) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
          ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
            let _ : Fact p.Prime := ⟨hP p (Finset.mem_filter.mp hp).1⟩
            (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  filter_upwards [eventual_original_lift_probability hBonami cψ a c C B hcψ ha hc hC hB ψ
    hreal hψ0 hψ1 hsupp hCψ, eventual_original_commonCenter C hC,
    eventually_ge_atTop (1 : ℝ)] with T hlift hcenter hT
  intro Q P hQ hP hodd D X hX hBX S hS hsize hD hSD ε t hε hbias k l N Z
    hk heven hksize hkL hkU hK hK3 hKU hlarge hL hL2 hpop hPU hXU hcop hPZ hmin
    hZ hZU hll hlL hlU hN1 hN hscale
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hXk : X ≤ Real.exp (((j + 1 : ℕ) : ℝ) * T) := hXU.trans (Real.exp_le_exp.mpr (by
    have hh : ((j + 1 - 10 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le (j + 1) 10
    exact mul_le_mul_of_nonneg_right hh (by linarith)))
  have hp := hlift Q P hQ hP hodd D X (by linarith) hBX S hS hsize hD hSD ε t hε hbias
    (j + 1) l N Z (by omega) heven hksize hkL hkU hK hK3 hKU hlarge hL hL2 hpop hXk hcop
    hPZ hmin hZ hZU hll hlL hlU hN1 hN hscale
  have hKT : (Q.card : ℝ) ≤ T := hKU.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
      (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num))
  have hc := hcenter P t j Q.card X hP hmin hpop hPU hk hksize hkU hK hKT hX hXU hp
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hc

end Ostmann

end OAI
