import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePairPatterns

namespace OAI

/-! # Applying representative-prior domination to the literal sampled pair -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPairCompensatedMass {A : Type*} (μ : ℕ → A → ℝ)
    (prime : A → ℕ) {n : ℕ} (a : MovingSampleSlots A n × MovingSampleSlots A n) : ℝ :=
  ((movingSampleProduct prime a.1 : ℝ) * movingSamplesPrior μ a.1) *
    ((movingSampleProduct prime a.2 : ℝ) * movingSamplesPrior μ a.2)

theorem movingPairCompensatedMass_pattern {A C : Type*} (μ : ℕ → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C) (x : C → A) :
    movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm (x ∘ pattern)) =
      internalPatternWeight pattern (fun i => μ (movingSampleTier i.2)) prime x := by
  rw [movingPairCompensatedMass, movingSamplePair_compensated_prior]
  rfl

/-- The weight bound needed by the proved symbolic-line comparison now
applies to the original two sample trees, including each node's `u` factor. -/
theorem movingPairCompensatedMass_pattern_bound {A C : Type*} [Fintype C]
    (μ : ℕ → A → ℝ) (prime : A → ℕ) (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (C → A) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hG : ∀ x, ‖G x‖ ≤ B) (x : C → A) :
    ‖(movingPairCompensatedMass μ prime
        ((movingSamplePairCoordinates A n).symm (x ∘ pattern)) : ℂ) * G x‖ *
      (∏ c, (prime (x c) : ℝ)⁻¹) ≤
        (B * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
          ∏ c, μ (movingSampleTier (rep c).val.2) (x c) := by
  rw [movingPairCompensatedMass_pattern]
  have h := internalPatternWeight_complex_bound pattern rep
    (fun i => μ (movingSampleTier i.2)) prime E hprime
    (fun i a => hμ _ a) (fun i a => hbound _ a) G B hB hG x
  simpa only [card_movingSamplePairIndex] using h

theorem sampleEqualityPattern_count_le (I : Type*) [Fintype I] :
    let _ := sampleSetoidFintype I
    Fintype.card (Setoid I) ≤ 2 ^ (Fintype.card I) ^ 2 := by
  let _ := sampleSetoidFintype I
  have hi : Function.Injective (fun s : Setoid I => {p : I × I | s p.1 p.2}) := by
    intro s t h
    ext i j
    exact Set.ext_iff.mp h (i, j)
  have h := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_set, Fintype.card_prod, pow_two] using h

/-- A coarse sufficient bound for all patterns at a fixed transfer depth.
In particular no bulk-length variable enters the exponent. -/
theorem movingSamplePair_pattern_count (n : ℕ) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    Fintype.card (Setoid (Bool × MovingSampleIndex n)) ≤ 2 ^ (4 * n * 2 ^ n) ^ 2 := by
  simpa only [card_movingSamplePairIndex] using
    sampleEqualityPattern_count_le (Bool × MovingSampleIndex n)

end Ostmann

end OAI
