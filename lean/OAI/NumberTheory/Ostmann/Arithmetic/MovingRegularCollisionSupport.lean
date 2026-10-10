import OAI.NumberTheory.Ostmann.Arithmetic.FrozenFrequencyAverage
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedOuterFactor
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeObservable

namespace OAI

/-! # Invalid regular-prime configurations vanish before either average -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingSupportedWeight_zero_of_not_regular {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hbad : ¬ movingRegularOutsidePairwise value outside T)
    (XL XR : ℕ) (z : ℂ) : movingSupportedWeight value outside T XL XR z = 0 := by
  apply ite_eq_right
  intro h
  exact hbad (movingFullOutsidePairwise_regular value outside T XL XR h.1)

theorem movingOriginalSupportedOuterPair_zero_of_not_regular {σ I : Type*}
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : Bool → ∀ i, (ZMod (p i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (t : Bool → FrequencyTree ℤ n) (hbad : ¬ ∀ b, movingRegularOutsidePairwise value outside (T b))
    (XL XR : ℕ) :
    movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi
      φ G Jleft Jright diagonal T t XL XR = 0 := by
  obtain ⟨b, hb⟩ := not_forall.mp hbad
  have hz := movingSupportedWeight_zero_of_not_regular value outside (T b) hb XL XR
  cases b <;> simp only [movingOriginalSupportedOuterPair, hz, map_zero, zero_mul, mul_zero]

theorem movingFrequencyPageAverage_zero_of_not_regular {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
    (hbad : ¬ ∀ b, movingRegularOutsidePairwise value outside (T b)) :
    movingFrequencyPageAverage value outside F E T nodes R r input Q y = 0 := by
  rw [movingFrequencyPageAverage_core]
  have hn : ¬ ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      (∀ f ∈ nodes b, f.guard.frequencyBounds) := fun h => hbad (fun b => (h b).1)
  rw [ite_eq_right hn, zero_mul]

end Ostmann

end OAI
