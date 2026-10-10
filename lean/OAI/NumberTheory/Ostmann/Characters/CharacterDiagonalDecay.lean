import OAI.NumberTheory.Ostmann.Characters.CharacterNonanchorDecay
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroDiagonal

namespace OAI

/-! # The literal character diagonal satisfies the finite iteration budget -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem character_nonanchor_gap_small (n : ℕ) (B B₁ z m C : ℝ)
    (hm : 0 ≤ m) (hz : 1 ≤ z) (hC : 2 * C ≤ m)
    (hB : 2 * B₁ + 5 ≤ B) :
    Real.exp (-(characterPivotGap B z m n - 2 * C)) ≤
      Real.exp (-(2 * B₁ + 4) * (2 ^ n : ℕ) * m) := by
  apply Real.exp_le_exp.mpr
  have hgap := character_diagonal_gap_reserve n B z m C hm hC
  have hlog := Real.log_nonneg hz
  have hscale : 0 ≤ (2 ^ n : ℕ) * m := mul_nonneg (Nat.cast_nonneg _) hm
  have hcoef : 2 * B₁ + 4 ≤ B + 20 * Real.log z - 1 := by linarith
  have hh := mul_le_mul_of_nonneg_right hcoef hscale
  nlinarith only [hgap, hh]

theorem eventual_character_diagonal_decay (k n Bnb N : ℕ) (hn : n < k)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
    (K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε : ℝ)
    (hB : 1 ≤ B) (hBstrong : 2 * B₁ + 5 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hCmass : 0 < Cmass)
    (hα : 0 < α) (hβg : 0 < βg) (hγw : 0 ≤ γw)
    (hαw : α < βw) (hsw : γs < βw) (hαa : α < βa)
    (hwa : γw < βa) (hwg : γw ≤ βg) (hβw : βw < νw) (hβa : βa < νa)
    (hε : 0 < ε) (hbudget : 4 * Cmass * Bnb ≤ z)
    (hgap : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) → L ≤ m →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
      ∀ (r : Fin k → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
      1 + ((∑ j, r j) + 2 * k) ≤ Bnb → (∀ j, r j ≤ N) → f ≤ N →
      ∀ (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : Fin (m + 1) → Finset ℕ)
        (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ),
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
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin k → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget k J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      T ⟨n, hn⟩ + c ≤ Real.exp (βg * L) →
      ∀ lower upper : CharacterCell k → ℕ,
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤ lower v) →
      (∀ v, (upper v : ℝ) ≤ Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      ∀ center : ∀ p : ℕ, ZMod p,
      let lo := initialWordAtomLower J lower
      let hi := initialWordAtomUpper J upper
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError k c)
      scheduledConstituentDiagonal (characterRole k) (characterSize m r f) χ₀
        (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP
        (characterFullPrimeCells m r f Q R) lo hi V cap
        (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
          (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
          (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c))) center
        (characterPivotAtom ⟨n, hn⟩) n ≤
        Real.exp (-(2 * B₁ + 3) * (2 ^ n : ℕ) * m) := by
  obtain ⟨M₀, hA⟩ := eventual_character_anchor_decay k n Bnb hn ψ K B B₁ z c a b
    Cmass α γw ε hB hz hc ha ha1 hb hCmass hα hγw hε hbudget hgap hψ
  have hdec := fun (d : ℕ) (hd : d + 1 < k) =>
    eventual_character_nonanchor_decay k d N hd ψ hreal B z c Cmass α βg βw γs βa γw νw νa
      hB hz hc hCmass hα hβg hαw hsw hαa hwa hwg hβw hβa
  have hdecAll := eventually_all.mpr (fun d : Fin k =>
    eventually_all.mpr (fun hd : d.val + 1 < k => hdec d hd))
  refine ⟨max M₀ (max 1 (max ((Fintype.card (CharacterRole k) : ℝ) * c)
    (2 * characterRangeError k c))), ?_⟩
  filter_upwards [hA, hdecAll, eventual_full_character_mass_floor a b Cmass ha hb hCmass,
    eventual_natural_cutoff_below_primes k (B + 20 * Real.log z) z α 1
      (by linarith [Real.log_nonneg hz]) (by linarith) hα (by norm_num)]
    with L hA hD hmass hlarge
  intro m hM hLm hmL hLm₂ r f hr hnb hrN hf P U hP Q R hQU htop hdis hQP hRP
    htopmass hbulk hRmass hPrange hUrange hsmall hbig χ hχ J hJ anchor F logX hlogX
    Δ T hT lower upper hlo hhi center lo hi χ₀ V cap
  let leaf := scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
    (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
    (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c))
  have hM₀ : M₀ ≤ (m : ℝ) := (le_max_left _ _).trans hM
  have hm : (1 : ℝ) ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hCm : (Fintype.card (CharacterRole k) : ℝ) * c ≤ m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hC : 2 * characterRangeError k c ≤ m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hA' := hA m hM₀ hLm hmL hLm₂ r f hr hnb P U hP Q R hQU hQP hRP
    htopmass hbulk hRmass (fun p hp => (hPrange p hp).1)
    (fun p hp => (hUrange p hp).2) J hJ anchor F logX hlogX lower upper hlo hhi χ
  have hlarge' : ∀ p ∈ P, V n < p := by
    intro p hp
    exact hlarge m hm hmL p (by simpa only [one_mul] using (hPrange p hp).1) n hn.le
  cases n with
  | zero =>
    have he := character_literal_diagonal_zero m r f Q U R hQU htop hdis χ₀
      (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP J hJ
      lower upper V cap leaf center (characterPivotAtom ⟨0, hn⟩) hlarge'
    dsimp only at he hA' ⊢
    rw [he]
    apply hA'.trans
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith only [hm]
  | succ d =>
    have hmass' := hmass k m r f Q R htopmass
      (fun i => by rw [hQU]; exact hbulk) hRmass
    have hD' := hD ⟨d, by omega⟩ hn m hm hLm hmL hCm r f hr hrN hf P hP
      (characterFullPrimeCells m r f Q R)
      (characterFullPrimeCells_subset m r f P Q R hQP hRP) hmass' hPrange
      hsmall (fun i p hp => by
        rw [characterFullPrimeCells_bulk, hQU] at hp
        exact hUrange p hp) hbig χ hχ J hJ anchor F logX hlogX hT lower upper hlo hhi
    have he := character_literal_diagonal_split m r f (d + 1) Q U R hQU htop hdis χ₀
      (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP J hJ
      lower upper V cap leaf center (characterPivotAtom ⟨d + 1, hn⟩) hlarge'
    dsimp only at he hA' hD' ⊢
    rw [he]
    exact character_diagonal_sum_small _ _ B₁ m (d + 1) hm hA'
      (hD'.trans (character_nonanchor_gap_small (d + 1) B B₁ z m
        (characterRangeError k c) (by linarith) hz hC hBstrong))
end Ostmann

end OAI
