import OAI.NumberTheory.Ostmann.Characters.CharacterConstructedTargets
import OAI.NumberTheory.Ostmann.Construction.FixedCharacterPriors

namespace OAI

/-! # Fixed character priors constructed from the tested shells and exact targets -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- All cells below are obtained from the published progression input. No
pivot-word, cell-mean, or normalized-prior hypothesis is supplied here. -/
theorem PublishedProgressionInput.constructed_fixed_character_priors
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : ℕ), 20000 ≤ k →
      C₀ ≤ Real.exp ((k : ℝ) / 10000) → ∀ (B z α β C : ℝ),
      0 ≤ B → 1 ≤ z → 0 < α → 0 ≤ C →
      ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤ z →
      ∀ᶠ L : ℝ in atTop, ∀ (U τ J : ℝ) (m D : ℕ),
      α * L ≤ U → U ≤ β * L → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 → 0 < τ →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m → τ / 2 ≤ J → J ≤ 4 * τ →
      (D + 1 : ℕ) ≤ Real.exp (C * L) → 5 * k ≤ D →
      ∀ (P : Finset ℕ) (G : ℕ → ℕ → ℂ) (ζ : ℂ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, primeLogIndex p ≤ D) → ‖ζ‖ = 1 →
      (∀ x p, p ∈ P → ‖G x p‖ ≤ 1) →
      (∀ u v : ℝ, U ≤ u → v ≤ U + 5 * k → (k : ℝ) / 10000 ≤ v - u →
        ∃ j : ℕ, u ≤ U + j ∧ U + j + 1 ≤ v ∧
          c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) →
      (∀ (x j : ℕ), j ≤ 5 * k → c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (ζ * G x p).re) →
      ∀ u : Fin k × Bool → ℝ,
      (∀ j, α * L ≤ u j ∧ u j ≤ β * L) →
      (∀ j : Fin k, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
      (∀ j, c ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
      (∀ x j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * G x p).re) →
      ∀ E : Finset ℕ, E.Nonempty → ∀ X A : ℝ,
      Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∃ a : ∀ x j, CharacterAnchorCell P (fun p => ζ * G x p) c δ (u j),
      ∃ w : ∀ x j, CharacterTargetWord P (fun p => ζ * G x p) c δ U k
        (characterConstructedTargets k J (1000 * (4 : ℝ) ^ k * τ) B z m
          (fun j => (a x j).index) j),
      (∀ x j, 0 < (w x j).indices.length) ∧
      ∃ x₀ ∈ E, ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 4 * C + 4) * m) ≤ S.card ∧
        let Q := characterPrimeCells (w x₀) (characterAnchorCells (a x₀))
        (∀ v i, Q v i ⊆ P) ∧
        (∀ v i, (∑ p : P, primeSubsetPrior P (Q v i) p) = 1) ∧
        (∀ v i, Real.exp (-(β + 1) * L) ≤ ∑ p ∈ Q v i, (p : ℝ)⁻¹) ∧
        (∀ x ∈ S, ∀ v i, δ / 2 ≤
          ‖∑ p : P, (primeSubsetPrior P (Q v i) p : ℂ) * G x p‖) := by
  obtain ⟨C₀, hC₀, hw⟩ := P0.character_backwards_words c δ hc hδ
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp (P0.character_anchor_cell c δ hc hδ)
  refine ⟨C₀, hC₀, ?_⟩
  intro k hk hC₀k B z α β C hB hz hα hC hsize
  have hanchor : ∀ᶠ L : ℝ in atTop, u₀ ≤ α * L :=
    (tendsto_id.const_mul_atTop hα).eventually (eventually_ge_atTop u₀)
  filter_upwards [hw k hk hC₀k B z α hB hz hα, hanchor,
    eventual_fixed_character_priors c δ β C z k hc hδ hC hz hsize] with L hwords hanchor hfixed
  intro U τ J m D hUL hUβ hUτ hτU hτ hm hmlo hJlo hJhi hD hkD P G ζ
    hP hPD hζ hG hrich htest u hu hus hmass hmean E hE X A hEcard
  have hrot (x p : ℕ) (hp : p ∈ P) : ‖ζ * G x p‖ ≤ 1 := by
    rw [norm_mul, hζ, one_mul]
    exact hG x p hp
  have hac : ∀ x j, Nonempty (CharacterAnchorCell P (fun p => ζ * G x p) c δ (u j)) := by
    intro x j
    exact hu₀ (u j) (hanchor.trans (hu j).1) P (fun p => ζ * G x p) hP
      (hrot x) (hmass j) (hmean x j)
  let a : ∀ x j, CharacterAnchorCell P (fun p => ζ * G x p) c δ (u j) :=
    fun x j => Classical.choice (hac x j)
  have hapair (x : ℕ) (j : Fin k) : (a x (j, false)).index + (a x (j, true)).index ≤ (4 * τ : ℝ) :=
    by linarith [(a x (j, false)).upper, (a x (j, true)).upper, hus j]
  let T := fun x => characterConstructedTargets k J (1000 * (4 : ℝ) ^ k * τ) B z m
    (fun j => (a x j).index)
  have hwords' : ∀ x, ∃ w : ∀ j, CharacterTargetWord P (fun p => ζ * G x p) c δ U k (T x j),
      (∀ j, 0 < (w j).indices.length) ∧
      (∑ j : Option (Fin k), (w j).indices.length) ≤ characterTargetLabelBound c δ k := by
    intro x
    exact hwords U τ J m hUL hUτ hτU hτ hm hJlo hJhi
      (fun j b => (a x (j, b)).index) (hapair x) P (fun p => ζ * G x p) hP
      (hrot x) hrich (htest x)
  choose w hlength hcount using hwords'
  refine ⟨a, w, hlength, ?_⟩
  exact hfixed D m X A U hD hmlo hUβ E hE hEcard P G ζ hζ hkD hPD u
    (fun j => (hu j).2) a
    (fun x _ j => (a x j).index_le hc hδ D hPD) T w

end Ostmann

end OAI
