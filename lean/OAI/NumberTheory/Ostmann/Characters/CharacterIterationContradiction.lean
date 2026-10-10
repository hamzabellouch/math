import OAI.NumberTheory.Ostmann.Characters.CharacterDiagonalDecay
import OAI.NumberTheory.Ostmann.Characters.CharacterFinalContradiction
import OAI.NumberTheory.Ostmann.Characters.CharacterLengthBounds

namespace OAI

/-! # Finite character transfer and the final contradiction

All diagonal and final comparison bounds here are derived from the physical
prime ranges and original harmonic priors. The initial amplitude is supplied
by the separately proved fixed-bin endpoint statistic.
-/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_character_iteration_contradiction (n N Bnb : ℕ)
    (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j)
    (hrN : ∀ j, r j ≤ N) (hf : f ≤ N)
    (hnb : 1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
    (K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε : ℝ)
    (hB : 1 ≤ B) (hBstrong : 2 * B₁ + 5 ≤ B) (hB₁ : 0 ≤ B₁)
    (hz : 1 < z) (hc : 1 ≤ c) (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b)
    (hCmass : 0 < Cmass) (hα : 0 < α) (hβg : 0 < βg) (hγw : 0 ≤ γw)
    (hαw : α < βw) (hsw : γs < βw) (hαa : α < βa)
    (hwa : γw < βa) (hwg : γw ≤ βg) (hβw : βw < νw) (hβa : βa < νa)
    (hε : 0 < ε) (hbudget : 4 * Cmass * Bnb ≤ z)
    (hpivot : Cmass * (∑ j, (r j : ℝ)) ≤ z / 4)
    (hgap : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1) :
    ∀ᶠ L : ℝ in atTop,
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
  have hz0 : 0 < z := by linarith
  have hdiag := fun j : Fin (n + 1) => eventual_character_diagonal_decay (n + 1) j.val Bnb N
    j.isLt ψ hreal K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε hB hBstrong hz.le hc
    ha ha1 hb hCmass hα hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudget hgap hψ
  choose M hM using hdiag
  have hall := eventually_all.mpr hM
  have hthreshold := eventually_all.mpr (fun j => eventual_character_length_ge z (M j) hz0)
  obtain ⟨Mf, hfinal⟩ := eventual_character_final_contradiction n N ψ hreal K B B₁ z c
    Cmass α βg βw γs νw ε hB hB₁ hz.le hc hCmass hα hβg hαw hsw hβw hε hψ hentropy
  filter_upwards [hall, hthreshold, hfinal, eventual_character_length_ge z Mf hz0,
    eventual_character_length_bounds z hz,
    eventual_character_atom_iteration (n + 1) r f hr B (B₁ - 1) z c Cmass (by linarith) hz.le hc
      hCmass.le hpivot,
    eventual_full_character_mass_floor a b Cmass ha hb hCmass,
    (tendsto_id.const_mul_atTop ha).eventually (eventually_ge_atTop (1 : ℝ)),
    eventual_natural_cutoff_below_primes (n + 1) (B + 20 * Real.log z) z α 1
      (by linarith [Real.log_nonneg hz.le]) hz0.le hα (by norm_num)]
    with L hd hth hfina hMf hlength hiter hmass haL hlarge
  intro m P U hP Q R hQU htop hdis hQP hRP htopmass hbulk hRmass hPrange hUrange
    hsmall hbig χ hχ J hJ anchor F logX hlogX Δ T hT cellLo cellHi hcell hlo hhi
    center lo hi χ₀ V cap hinit
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hlength.2.1
  have hLm : L ≤ (m : ℝ) := hlength.2.2.1
  have hmL : (m : ℝ) ≤ z * L := hlength.2.2.2.1
  have hLm₂ : z * L ≤ 2 * m := hlength.2.2.2.2
  have hQall := characterFullPrimeCells_subset m r f P Q R hQP hRP
  have hmassall := hmass (n + 1) m r f Q R htopmass
    (fun i => by rw [hQU]; exact hbulk) hRmass
  have hpos (i) : (∑ p ∈ characterFullPrimeCells m r f Q R i, (p : ℝ)⁻¹) ≠ 0 :=
    ne_of_gt ((Real.exp_pos _).trans_le (hmassall i))
  have hlargeall (p : ℕ) (hp : p ∈ P) : V (n + 1) < p :=
    hlarge m hm hmL p (by simpa only [one_mul] using (hPrange p hp).1) (n + 1) le_rfl
  have hdiagonal (j : ℕ) (hj : j < n + 1) :=
    hd ⟨j, hj⟩ m (hth ⟨j, hj⟩) hLm hmL hLm₂ r f hr hnb hrN hf P U hP Q R
      hQU htop hdis hQP hRP htopmass hbulk hRmass hPrange hUrange hsmall hbig χ hχ
      J hJ anchor F logX hlogX (hT ⟨j, hj⟩)
      (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
      (fun v => ∏ i, cellHi ⟨(true, some v), i⟩) hlo hhi center
  have htransfer := hiter J hJ anchor F cellLo cellHi χ₀
    (fun i => primeGaussMultiplier (χ₀ i)) P hP (characterFullPrimeCells m r f Q R)
    (scheduleFourierLeaf (characterRole (n + 1)) ψ (Real.exp logX)
      (Real.exp (Δ - (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))
      (Real.exp (Δ + (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))) center
    (fun _ _ _ => (primeGaussMultiplier_norm _ _).le) hQall hpos hcell hlo hhi
    (fun j i => harmonic_mass_inv_le_exp _ Cmass L (hRmass (.inl j) i))
    hlargeall hinit (by
      intro j hj
      simpa only [sub_add_cancel, characterPivotRole_eq hj, Nat.cast_pow, Nat.cast_ofNat]
        using hdiagonal j hj)
  have hlast := hfina m hMf hLm hmL r f hr hrN hf P hP
    (characterFullPrimeCells m r f Q R) hQall hmassall hPrange hsmall
    (fun i p hp => by
      rw [characterFullPrimeCells_bulk, hQU] at hp
      exact (hUrange p hp).1)
    (fun i => by
      rw [characterFullPrimeCells_bulk, hQU]
      exact haL.trans hbulk) χ hχ J
    (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
    (fun v => ∏ i, cellHi ⟨(true, some v), i⟩) logX hlogX cap center
  apply hlast
  simpa only [sub_add_cancel] using htransfer

end Ostmann

end OAI
