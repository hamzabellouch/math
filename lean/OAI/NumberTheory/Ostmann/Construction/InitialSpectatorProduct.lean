import OAI.NumberTheory.Ostmann.Construction.InitialMovingWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingInitialCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitude

namespace OAI

/-! # The fixed spectator product retains both original logarithmic cutoffs -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem initialMovingCutoffWeight_spectator_product {A : Type*}
    (value : A → ℕ) (hvalue : ∀ x, 0 < value x)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → A)
    (y : MovingRegularSlot 0 (r + r) (b + b) → A)
    (hy : initialMovingCutoffWeight value b d r cb cd sl sr y ≠ 0) :
    |Real.log ((∏ i, value (Fin.append sl sr i) : ℕ) : ℝ) - 2 * cd| < 2 := by
  rw [Nat.cast_prod, Real.log_prod (fun i _ => by exact_mod_cast (hvalue (Fin.append sl sr i)).ne')]
  exact (initialMovingCutoffWeight_live_sums value b d r cb cd sl sr y hy).2

theorem initialMovingOriginalLeaf_spectator_product {A I : Type*}
    (value : A → ℕ) (hvalue : ∀ x, 0 < value x)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → A) (fallback : A)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (x : MovingSlotState A) (s : ℤ)
    (hx : movingOriginalLeaf value q
      (initialMovingDataCutoff value b d r cb cd sl sr fallback) g Dq S ψ X lo hi x s ≠ 0) :
    |Real.log ((∏ i, value (Fin.append sl sr i) : ℕ) : ℝ) - 2 * cd| < 2 := by
  have hw := left_ne_zero_of_mul (left_ne_zero_of_mul hx)
  have hd : initialMovingDataCutoff value b d r cb cd sl sr fallback x.data s ≠ 0 := by
    intro hz
    apply hw
    simp only [movingWindowLeaf, movingDataLeaf, hz, ite_self]
  have hc : initialMovingCutoffWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback x.data.regularSlots) ≠ 0 := by
    intro hz
    apply hd
    simp only [initialMovingDataCutoff, hz, ite_self]
  exact initialMovingCutoffWeight_spectator_product value hvalue b d r cb cd sl sr _ hc

/-- A nonzero initial statistic certifies the fixed spectator product, with no
assumption on an individual sampled summand. -/
theorem initialTemplateAmplitude_spectator_product {A I : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ x, 0 < value x)
    (b d r a : ℕ) (cb cd : ℝ) (sl sr : Fin d → A) (fallback : A)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot 0 a (b + b) → A → ℝ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (fav : ℕ → Bool)
    (h : movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q
        (initialMovingDataCutoff value b d r cb cd sl sr fallback) g Dq S ψ X lo hi)
      φ G 0 a (b + b) Pg ρ ν greg ggiant fav ≠ 0) :
    |Real.log ((∏ i, value (Fin.append sl sr i) : ℕ) : ℝ) - 2 * cd| < 2 := by
  obtain ⟨XL, _, hXL⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨XR, _, hXR⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hXL)
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hXR)
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  have hc := left_ne_zero_of_mul (right_ne_zero_of_mul hy)
  unfold movingTemplateCoefficient at hc
  have hf := movingFrequencyCoefficient_levelZero_support A value outside μ childBound
    pivotBound V _ φ G s.val _ _ XL XR hc
  exact initialMovingOriginalLeaf_spectator_product value hvalue b d r cb cd sl sr
    fallback q g Dq S ψ X lo hi _ _ hf

end Ostmann

end OAI
