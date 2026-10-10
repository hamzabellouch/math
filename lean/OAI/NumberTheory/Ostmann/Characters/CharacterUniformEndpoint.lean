import OAI.NumberTheory.Ostmann.Characters.CharacterEndpointContradiction

namespace OAI

/-! # Uniformity in the actual selected nonword-cell count -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_uniform_character_endpoint_contradiction (n N Bnb : ℕ)
    (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 < z)
    (hCmass : 0 < Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
    (hs : 0 < s) (hγ : 0 < γ) (hH : 0 ≤ H) (hα : 0 < α)
    (hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (hB : 0 ≤ B)
    (hB₁ : 0 ≤ B₁) (hB₁eq : B₁ = Aend + 2 * Bword + 3)
    (hBstrong : 2 * B₁ + 5 ≤ B) (hBpos : 1 ≤ B) (ha1 : a ≤ 1)
    (hβg : 0 < βg) (hγw : 0 ≤ γw) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hwg : γw ≤ βg)
    (hβw : βw < νw) (hβa : βa < νa) (hε : 0 < ε)
    (hbudgetAll : 4 * Cmass * Bnb ≤ z)
    (hgapFinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ∀ᶠ L : ℝ in atTop, ∀ nc : ℕ, nc ≤ Bnb →
    let m := ⌊z * L⌋₊
    ∀ (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
    (∀ j, r j ≤ N) → f ≤ N →
    1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb →
    Cmass * (∑ j, (r j : ℝ)) ≤ z / 4 →
    ∀ (_cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
      (logX τ bmax : ℝ) (P U T₀ : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ)
      (R : (v : CharacterCell (n + 1)) → Fin (characterCellSize r f v) → Finset ℕ),
    0 < logX → Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) →
    (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
    (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
    Disjoint U T₀ → (∀ v i, Disjoint U (R v i)) →
    (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
      (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
    (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
      Real.exp (Real.exp (νa * L)) ≤ p) →
    (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ),
    (∀ v i p, p ∈ R v i → cellLo ⟨v, i⟩ ≤ p ∧ p ≤ cellHi ⟨v, i⟩) →
    ∀ (anchor : Fin (n + 1) → Bool → ℝ) (bin : Fin (⌊4 * τ⌋₊ + 1)), 0 < bin.val →
    let Δ := characterBaseGap B z m
    let T := characterPivotTarget (n + 1) bin.val (fun j => anchor j false + anchor j true)
      (fun j => characterPivotGap B z m j.val)
    let F := characterFillerTarget logX Δ bin.val T anchor
    (∀ j, T j + c ≤ Real.exp (βg * L)) →
    (∀ v, Real.exp (characterLogCenter bin.val T anchor F (true, some v) - c) ≤
      ∏ i, cellLo ⟨v, i⟩) →
    (∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤
      Real.exp (characterLogCenter bin.val T anchor F (true, some v) + c)) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ρ : ℝ),
    Real.sqrt (Real.exp logX) * Real.exp (-Aend * m) ≤ E.card →
    Real.exp (-Bword * m) ≤ ρ →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re) →
    (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((x : ZMod p) - center p))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
    (∀ x ∈ E, ∀ v i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R v i) p : ℂ) * χ p ((x : ZMod p) - center p)‖) →
    False := by
  have hbudget (i : Fin (Bnb + 1)) : 4 * (i.val : ℝ) * Cmass ≤ z := by
    have hi : (i.val : ℝ) ≤ Bnb := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * Cmass by positivity)
    nlinarith only [hh, hbudgetAll]
  have hall := eventually_all.mpr (fun i : Fin (Bnb + 1) =>
    eventual_character_endpoint_contradiction n N Bnb i.val
      a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε
      ha hb hz hCmass hCtotal hc hs hγ hH hα (hbudget i) hgapInitial hB hB₁ hB₁eq
      hBstrong hBpos ha1 hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll
      hgapFinal hentropy ψ hψ hreal heven hψK hsupp)
  filter_upwards [hall] with L hL nc hnc
  exact hL ⟨nc, Nat.lt_succ_of_le hnc⟩

end Ostmann

end OAI
