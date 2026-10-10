import OAI.NumberTheory.Ostmann.Construction.InitialMovingCoefficientFactor
import OAI.NumberTheory.Ostmann.Construction.InitialHalfBulkProduct

namespace OAI

/-! # Factoring the genuine half-list weights in the original Fourier coefficient -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalLeaf_initial_halves {P I : Type}
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (x : MovingSlotState P) (s : ℤ) :
    movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
      g Dq S ψ X lo hi x s =
    (initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) *
      movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi x s := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  dsimp only
  rw [initialMovingDataCutoff_factor]
  split_ifs <;> ring

theorem movingFrequencyCoefficient_original_initial_halves {P I : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List P) n) (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
        φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR := by
  have he : movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
      g Dq S ψ X lo hi = fun x s =>
      (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) *
      movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi x s := by
    funext x s
    exact movingOriginalLeaf_initial_halves value b d r cb cd sl sr fallback q g Dq S ψ X lo hi x s
  rw [he]
  exact movingFrequencyCoefficient_initial_halves value b d r cb cd sl sr fallback outside μ
    childBound pivotBound V _ φ G n a s small slot hsmall hlen XL XR

theorem movingFrequencyCoefficient_original_initial_product_lower {P I : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List P) n) (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) ≤ ((∏ j, value (slot j) : ℕ) : ℝ) := by
  rw [movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s small slot hsmall hlen XL XR] at h
  apply initialHalfBulkProduct_product_lower value hvalue b d cb cd sl sr n slot
  exact Complex.ofReal_ne_zero.mp (left_ne_zero_of_mul h)

end Ostmann

end OAI
