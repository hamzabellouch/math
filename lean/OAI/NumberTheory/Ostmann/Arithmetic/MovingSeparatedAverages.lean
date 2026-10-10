import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedPageCRT
import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalProductError
import OAI.NumberTheory.Ostmann.Construction.FiniteEnumeration

namespace OAI

/-! # Explicit three-factor form of the original Page-weighted average -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingFrequencyPageAverage {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) : ℂ :=
  (Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ *
    ∑ z : ZMod r × (ZMod r)ˣ,
      movingFrequencyPairFactor value outside F E T nodes R z.1.val z.2.val.val *
        pageGiantWeight input Q r z.2.val.val y

noncomputable def movingSpectatorHaarAverage {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : Bool → (ZMod q)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) : ℂ :=
  (Fintype.card (ZMod q × (ZMod q)ˣ) : ℂ)⁻¹ *
    ∑ z : ZMod q × (ZMod q)ˣ, movingSpectatorPairFactor value q g D T z.1 z.2

theorem movingArithmeticPageFactor_averages {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) (S : Finset I)
    [∀ p : P, Fact p.val.Prime] [∀ b, NeZero (movingArithmeticModuli r q P S b)]
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    (∏ b, (Fintype.card (ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ *
      ∑ z, movingArithmeticPageFactor r q P S input Q y
        (movingArithmeticLocalFactor q value outside F E g D T nodes R r P S) b z) =
      movingFrequencyPageAverage value outside F E T nodes R r input Q y *
        (∏ p : P, movingInternalHaarAverage value T p.val) *
        ∏ i : S, movingSpectatorHaarAverage value (q i.val) (g i.val)
          (fun side => D side i.val) T := by
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, movingArithmeticPageFactor,
    movingArithmeticLocalFactor, movingArithmeticModuli, movingFrequencyPageAverage,
    movingInternalHaarAverage, movingSpectatorHaarAverage]
  rw [← mul_assoc]
  congr 4

section
variable {σ I : Type*} (q : I → ℕ) [∀ i, Fact (q i).Prime]
  (value : σ → ℕ) (outside : List ℕ)
  (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
  (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
  (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
  {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
  (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) (S : Finset I)
  [∀ p : P, Fact p.val.Prime]
  [∀ b, NeZero (movingArithmeticModuli r q P S b)]
  [NeZero (∏ b, movingArithmeticModuli r q P S b)]
  (hf : ∀ side, (T side).Frequencies (· ≠ 0))
  (hR : ∀ side, (T side).frequencyProduct ∣ R)
  (hfrequency : R ^ (n + 1) ∣ (r : ℤ))
  (hcover : ∀ side, ∀ o ∈ (T side).occurrences,
    ∀ i ∈ o.current.compensationSlots, value i ∈ P)
  (hc : Pairwise (fun b c => (movingArithmeticModuli r q P S b).Coprime
    (movingArithmeticModuli r q P S c)))
  (input : PublishedProgressionInput) (Q : ℕ)
  (hpage : pageAtModulus (∏ b, movingArithmeticModuli r q P S b) (selectedPageZero input Q) =
    pageAtModulus r (selectedPageZero input Q))

include hf hR hfrequency hcover hc hpage

theorem movingSeparatedPairResidueCoefficient_page_factorization (y : ℝ) :
    correctedMixedPairAverage input Q (∏ b, movingArithmeticModuli r q P S b)
      (movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R) y =
      movingFrequencyPageAverage value outside F E T nodes R r input Q y *
        (∏ p : P, movingInternalHaarAverage value T p.val) *
        ∏ i : S, movingSpectatorHaarAverage value (q i.val) (g i.val)
          (fun side => D side i.val) T := by
  rw [movingSeparatedPairResidueCoefficient_page_average q value outside F E g D T nodes
    R r P S hf hR hfrequency hcover hc input Q hpage]
  exact movingArithmeticPageFactor_averages q value outside F E g D T nodes R r P S input Q y

/-- Remove all prime-square exclusions from the literal corrected average.
The frequency/Page factor and each spectator factor are retained exactly. -/
theorem movingSeparatedPairResidueCoefficient_square_error
    (tier : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (hlevels : ∀ side, (T side).Levels tier)
    (hfmod : ∀ p : P, ∀ side, (T side).Frequencies (fun s => (s : ZMod p.val) ≠ 0))
    (y B : ℝ)
    (hweight : ‖movingFrequencyPageAverage value outside F E T nodes R r input Q y *
        (∏ i : S, movingSpectatorHaarAverage value (q i.val) (g i.val)
          (fun side => D side i.val) T)‖ *
      (∏ p : P, movingInternalLineProbability value T p.val) ≤ B) :
    ‖correctedMixedPairAverage input Q (∏ b, movingArithmeticModuli r q P S b)
        (movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R) y -
      movingFrequencyPageAverage value outside F E T nodes R r input Q y *
        (∏ p : P, (movingInternalLineProbability value T p.val : ℂ)) *
        ∏ i : S, movingSpectatorHaarAverage value (q i.val) (g i.val)
          (fun side => D side i.val) T‖ ≤
      B * (2 * (2 ^ n - 1 : ℕ) * ∑ p : P, (p.val : ℝ)⁻¹) := by
  rw [movingSeparatedPairResidueCoefficient_page_factorization q value outside F E g D T nodes
    R r P S hf hR hfrequency hcover hc input Q hpage]
  have h := movingInternalProduct_weighted_error tier value hprime hdisjoint T hlevels P hfmod
    (movingFrequencyPageAverage value outside F E T nodes R r input Q y *
      ∏ i : S, movingSpectatorHaarAverage value (q i.val) (g i.val)
        (fun side => D side i.val) T) B hweight
  convert h using 1
  congr 1
  ring

end
end Ostmann

end OAI
