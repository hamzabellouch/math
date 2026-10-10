import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalSampleExpansion

namespace OAI

/-! # The literal level-zero coefficient and its original cutoff -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingFrequencyCoefficient_levelZero_sample (σ : Type) [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (small bulk : List σ) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 s
      small bulk XL XR =
    movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) 0 s small bulk XL XR := by
  unfold movingFrequencyCoefficient
  change (∑ t : Unit, _) = _
  rw [Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem movingFrequencyCoefficient_levelZero (σ : Type) [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (small bulk : List σ) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 s
      small bulk XL XR =
    movingGuardedLeaf value outside F ⟨0, .leaf s (small ++ bulk), XL, XR⟩ s := by
  unfold movingFrequencyCoefficient
  change (∑ t : Unit, _) = _
  rw [Finset.univ_unique, Finset.sum_singleton]
  unfold movingSupportedSampledWeight movingSampledWeight
  rw [← (movingSampleZeroEquiv σ).sum_comp]
  rw [Finset.univ_unique, Finset.sum_singleton]
  simp [movingSampleZeroEquiv, movingSamplesPrior, recursiveTransferWeight,
    buildMovingSlotData, frequencyRoot, flattenMovingSlots, movingRootedFrequencyTree]

theorem movingFrequencyCoefficient_levelZero_support (σ : Type) [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (small bulk : List σ) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 s
      small bulk XL XR ≠ 0) :
    F ⟨0, .leaf s (small ++ bulk), XL, XR⟩ s ≠ 0 := by
  rw [movingFrequencyCoefficient_levelZero] at h
  unfold movingGuardedLeaf at h
  split_ifs at h
  · exact h
  · exact (h rfl).elim

theorem movingOriginalLeaf_window {σ I : Type*}
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) (s : ℤ)
    (h : movingOriginalLeaf value q F g Dq S ψ X lo hi x s ≠ 0) :
    (movingSlotModulus value x : ℝ) / X ∈ Set.Icc lo hi := by
  have hw : movingWindowLeaf value X lo hi (movingDataLeaf F) x s ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul h)
  unfold movingWindowLeaf at hw
  split_ifs at hw with hc
  · exact hc
  · exact (hw rfl).elim

theorem movingFrequencyCoefficient_initial_window {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (small bulk : List σ) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G 0 s small bulk XL XR ≠ 0) :
    X * lo ≤ (XL * XR * MovingSlotReversal.naturalProduct value (small ++ bulk) : ℕ) ∧
      ((XL * XR * MovingSlotReversal.naturalProduct value (small ++ bulk) : ℕ) : ℝ) ≤ X * hi := by
  have hw := movingOriginalLeaf_window value q F g Dq S ψ X lo hi
    ⟨0, .leaf s (small ++ bulk), XL, XR⟩ s
    (movingFrequencyCoefficient_levelZero_support σ value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G s small bulk XL XR h)
  change lo ≤ _ / X ∧ _ / X ≤ hi at hw
  constructor
  · have ht := (le_div_iff₀ hX).mp hw.1
    simpa only [movingSlotModulus, mul_comm] using ht
  · have ht := (div_le_iff₀ hX).mp hw.2
    simpa only [movingSlotModulus, mul_comm] using ht

/-- At the first step the original terminal window bounds the retained
product after the extracted giant and compensation product are removed. -/
theorem movingFrequencyCoefficient_initial_retained_bound {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi lower : ℝ) (hX : 0 < X)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ)
    (comp small bulk : List σ) (p XR H : ℕ)
    (hp : 0 < p) (hcomp : 0 < MovingSlotReversal.naturalProduct value comp)
    (hlower : lower ≤ (p * MovingSlotReversal.naturalProduct value comp : ℕ))
    (hcap : X * hi ≤ lower * H)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G 0 s (comp ++ small) bulk p XR ≠ 0) :
    XR * MovingSlotReversal.naturalProduct value (small ++ bulk) ≤ H := by
  have hu := (movingFrequencyCoefficient_initial_window value outside μ childBound pivotBound V
    q F g Dq S ψ X lo hi hX φ G s (comp ++ small) bulk p XR h).2
  have hproduct : p * XR * MovingSlotReversal.naturalProduct value ((comp ++ small) ++ bulk) =
      (p * MovingSlotReversal.naturalProduct value comp) *
        (XR * MovingSlotReversal.naturalProduct value (small ++ bulk)) := by
    simp only [MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]
    ring
  rw [hproduct, Nat.cast_mul] at hu
  have htot := hu.trans (hcap.trans (mul_le_mul_of_nonneg_right hlower (Nat.cast_nonneg H)))
  have hpositive : (0 : ℝ) < (p * MovingSlotReversal.naturalProduct value comp : ℕ) := by
    exact_mod_cast Nat.mul_pos hp hcomp
  exact_mod_cast (mul_le_mul_iff_right₀ hpositive).mp htot

end Ostmann

end OAI
