import OAI.NumberTheory.Ostmann.Characters.CharacterIterationContradiction

namespace OAI

/-! # The finite character contradiction is uniform over the chosen word lengths -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_uniform_character_iteration_contradiction (n N Bnb : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
    (K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε : ℝ)
    (hB : 1 ≤ B) (hBstrong : 2 * B₁ + 5 ≤ B) (hB₁ : 0 ≤ B₁)
    (hz : 1 < z) (hc : 1 ≤ c) (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b)
    (hCmass : 0 < Cmass) (hα : 0 < α) (hβg : 0 < βg) (hγw : 0 ≤ γw)
    (hαw : α < βw) (hsw : γs < βw) (hαa : α < βa)
    (hwa : γw < βa) (hwg : γw ≤ βg) (hβw : βw < νw) (hβa : βa < νa)
    (hε : 0 < ε) (hbudget : 4 * Cmass * Bnb ≤ z)
    (hgap : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1) :
    ∀ᶠ L : ℝ in atTop, ∀ (r : Fin (n + 1) → ℕ) (f : ℕ),
      (∀ j, r j ≤ N) → f ≤ N → ∀ (hr : ∀ j, 0 < r j),
      1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb →
      Cmass * (∑ j, (r j : ℝ)) ≤ z / 4 →
      let m := ⌊z * L⌋₊
      ∀ (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : Fin (m + 1) → Finset ℕ)
        (R : (v : CharacterCell (n + 1)) → Fin (characterCellSize r f v) → Finset ℕ),
      (∀ i : Fin m, Q i.succ = U) → Disjoint U (Q 0) →
      (∀ v i, Disjoint U (R v i)) →
      (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ → a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ →
      (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
      (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
        (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
        Real.exp (Real.exp (νa * L)) ≤ p) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin (n + 1) → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget (n + 1) J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      (∀ j, T j + c ≤ Real.exp (βg * L)) →
      ∀ cellLo cellHi : (Σ v, Fin (characterSize m r f v)) → ℕ,
      (∀ i p, p ∈ characterFullPrimeCells m r f Q R i →
        cellLo i ≤ p ∧ p ≤ cellHi i) →
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤
        ∏ i, cellLo ⟨(true, some v), i⟩) →
      (∀ v, (∏ i, cellHi ⟨(true, some v), i⟩ : ℕ) ≤
        Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      ∀ center : ∀ p : ℕ, ZMod p,
      let lo := initialWordAtomLower J (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
      let hi := initialWordAtomUpper J (fun v => ∏ i, cellHi ⟨(true, some v), i⟩)
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError (n + 1) c)
      Real.exp (-(B₁ - 1) * m) ≤
        ‖scheduledConstituentAmplitude (characterRole (n + 1)) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP
          (characterFullPrimeCells m r f Q R) lo hi V cap
          (scheduleFourierLeaf (characterRole (n + 1)) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))) center 0‖ → False := by
  let F (r : Fin (n + 1) → ℕ) (f : ℕ) (L : ℝ) : Prop := ∀ (hr : ∀ j, 0 < r j),
      1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb →
      Cmass * (∑ j, (r j : ℝ)) ≤ z / 4 →
      let m := ⌊z * L⌋₊
      ∀ (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : Fin (m + 1) → Finset ℕ)
        (R : (v : CharacterCell (n + 1)) → Fin (characterCellSize r f v) → Finset ℕ),
      (∀ i : Fin m, Q i.succ = U) → Disjoint U (Q 0) →
      (∀ v i, Disjoint U (R v i)) →
      (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ → a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ →
      (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
      (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
        (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
        Real.exp (Real.exp (νa * L)) ≤ p) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin (n + 1) → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget (n + 1) J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      (∀ j, T j + c ≤ Real.exp (βg * L)) →
      ∀ cellLo cellHi : (Σ v, Fin (characterSize m r f v)) → ℕ,
      (∀ i p, p ∈ characterFullPrimeCells m r f Q R i →
        cellLo i ≤ p ∧ p ≤ cellHi i) →
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤
        ∏ i, cellLo ⟨(true, some v), i⟩) →
      (∀ v, (∏ i, cellHi ⟨(true, some v), i⟩ : ℕ) ≤
        Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      ∀ center : ∀ p : ℕ, ZMod p,
      let lo := initialWordAtomLower J (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
      let hi := initialWordAtomUpper J (fun v => ∏ i, cellHi ⟨(true, some v), i⟩)
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError (n + 1) c)
      Real.exp (-(B₁ - 1) * m) ≤
        ‖scheduledConstituentAmplitude (characterRole (n + 1)) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP
          (characterFullPrimeCells m r f Q R) lo hi V cap
          (scheduleFourierLeaf (characterRole (n + 1)) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))) center 0‖ → False
  have hF (r : Fin (n + 1) → ℕ) (f : ℕ) (hrN : ∀ j, r j ≤ N) (hf : f ≤ N) :
      ∀ᶠ L : ℝ in atTop, F r f L := by
    by_cases hr : ∀ j, 0 < r j
    · by_cases hnb : 1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb
      · by_cases hpivot : Cmass * (∑ j, (r j : ℝ)) ≤ z / 4
        · have hh := eventual_character_iteration_contradiction n N Bnb r f hr hrN hf hnb
            ψ hreal K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε hB hBstrong hB₁
            hz hc ha ha1 hb hCmass hα hβg hγw hαw hsw hαa hwa hwg hβw hβa hε
            hbudget hpivot hgap hψ hentropy
          filter_upwards [hh] with L hL
          intro hr' _ _
          exact hL
        · exact Filter.Eventually.of_forall (fun L _ _ hp => (hpivot hp).elim)
      · exact Filter.Eventually.of_forall (fun L _ hn => (hnb hn).elim)
    · exact Filter.Eventually.of_forall (fun L hr' => (hr hr').elim)
  have hall := eventually_all.mpr (fun rr : Fin (n + 1) → Fin (N + 1) =>
    eventually_all.mpr (fun ff : Fin (N + 1) =>
      hF (fun j => (rr j).val) ff.val (fun j => Nat.le_of_lt_succ (rr j).isLt)
        (Nat.le_of_lt_succ ff.isLt)))
  filter_upwards [hall] with L hL r f hrN hf
  exact hL (fun j => ⟨r j, Nat.lt_succ_of_le (hrN j)⟩) ⟨f, Nat.lt_succ_of_le hf⟩

end Ostmann

end OAI
