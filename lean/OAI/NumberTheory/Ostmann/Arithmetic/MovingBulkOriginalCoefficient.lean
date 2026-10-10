import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkCoefficient

namespace OAI

/-! # The original windowed Fourier coefficient retains its bulk cutoffs -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingBulkLeafProduct_bounds {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (cb cd : ℝ) (n : ℕ) (bulk : TreeLeafTuple (List σ) n) :
    0 ≤ treeLeafProduct n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n bulk) ∧
      treeLeafProduct n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n bulk) ≤ 1 := by
  induction n with
  | zero => exact movingBulkListLogWeight_bounds value outside cb cd bulk
  | succ n ih =>
    obtain ⟨hL, hL'⟩ := ih bulk.1
    obtain ⟨hR, hR'⟩ := ih bulk.2
    exact ⟨mul_nonneg hL hR, (mul_le_mul hL' hR' hR zero_le_one).trans_eq (one_mul 1)⟩

theorem movingOriginalLeaf_bulk_log {σ I : Type*}
    (value tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) (s : ℤ) :
    movingOriginalLeaf value q
        (fun T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F T s)
        g Dq S ψ X lo hi x s =
      (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) *
        movingOriginalLeaf value q F g Dq S ψ X lo hi x s := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  split_ifs <;> ring

/-- All sharp windows, Fourier factors, spectator factors and support tests
remain in the coefficient after the real bulk weight has been extracted. -/
theorem movingFrequencyCoefficient_original_bulk_log {σ I : Type} [Fintype σ]
    (value tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → σ → ℝ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (childBound pivotBound V : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (small bulk : TreeLeafTuple (List σ) n)
    (hn : n ≤ k) (hsmall : ∀ i ∈ flattenMovingSlots n small, tier i ≠ k)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, tier i = k) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q
          (fun T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F T s)
          g Dq S ψ X lo hi) φ G n s small bulk XL XR =
      ((treeLeafProduct n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n bulk) : ℝ) : ℂ) *
        movingFrequencyCoefficient value outside μ childBound pivotBound V
          (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small bulk XL XR := by
  have hF : movingOriginalLeaf value q
      (fun T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F T s)
      g Dq S ψ X lo hi =
      fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) *
        movingOriginalLeaf value q F g Dq S ψ X lo hi x s := by
    funext x s
    exact movingOriginalLeaf_bulk_log value tier k outside cb cd q F g Dq S ψ X lo hi x s
  rw [hF]
  exact movingFrequencyCoefficient_bulk_log value tier k outside cb cd μ hμ childBound pivotBound V
    (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small bulk hn hsmall hbulk XL XR

/-- Pointwise domination applies before any external bulk symmetrization.
It supplies the original same-assignment energy bound with the cutoffs retained. -/
theorem movingFrequencyCoefficient_original_bulk_log_norm_le {σ I : Type} [Fintype σ]
    (value tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → σ → ℝ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (childBound pivotBound V : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (small bulk : TreeLeafTuple (List σ) n)
    (hn : n ≤ k) (hsmall : ∀ i ∈ flattenMovingSlots n small, tier i ≠ k)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, tier i = k) (XL XR : ℕ) :
    ‖movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q
          (fun T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F T s)
          g Dq S ψ X lo hi) φ G n s small bulk XL XR‖ ≤
      ‖movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small bulk XL XR‖ := by
  rw [movingFrequencyCoefficient_original_bulk_log value tier k outside cb cd μ hμ q F
    g Dq S ψ X lo hi childBound pivotBound V φ G n s small bulk hn hsmall hbulk XL XR,
    norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (movingBulkLeafProduct_bounds value outside cb cd n bulk).1]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (movingBulkLeafProduct_bounds value outside cb cd n bulk).2

end Ostmann

end OAI
