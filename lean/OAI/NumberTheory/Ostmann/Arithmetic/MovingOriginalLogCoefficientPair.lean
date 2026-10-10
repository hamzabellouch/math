import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkPairedLogWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkOriginalCoefficient

namespace OAI

/-! # Exact retained-log factors in the original paired Fourier coefficients -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalCoefficientPair_bulk_log {σ I : Type} [Fintype σ]
    (value tier : σ → ℕ) (hvalue : ∀ a, 0 < value a)
    (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → σ → ℝ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {d : ℕ} → MovingSlotData σ d → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (childBound pivotBound V : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (small : TreeLeafTuple (List σ) n)
    (bulk : Bool → TreeLeafTuple (List σ) n)
    (hn : n ≤ k) (hsmall : ∀ i ∈ flattenMovingSlots n small, tier i ≠ k)
    (hbulk : ∀ b i, i ∈ flattenMovingSlots n (bulk b) → tier i = k)
    (XL XR : ℕ) :
    let coeff := fun b => movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small (bulk b) XL XR
    let weighted := fun b => movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q
        (fun T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F T s)
        g Dq S ψ X lo hi) φ G n s small (bulk b) XL XR
    weighted false * star (weighted true) =
      (logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^
        (2 ^ n + 2 ^ n) : ℝ) *
        ((∏ j, bulkLogCutoffWeight (fun a => (value a : ℝ)) cb
          (movingBulkPairedCutoffSlots n bulk j) : ℝ) : ℂ) *
        (coeff false * star (coeff true)) := by
  dsimp only
  rw [movingFrequencyCoefficient_original_bulk_log value tier k outside cb cd μ hμ q F g Dq S
    ψ X lo hi childBound pivotBound V φ G n s small (bulk false) hn hsmall (hbulk false) XL XR,
    movingFrequencyCoefficient_original_bulk_log value tier k outside cb cd μ hμ q F g Dq S
    ψ X lo hi childBound pivotBound V φ G n s small (bulk true) hn hsmall (hbulk true) XL XR,
    star_mul]
  calc
    _ = ((treeLeafProduct (U := ℝ) n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n (bulk false)) : ℂ) *
        star (treeLeafProduct (U := ℝ) n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n (bulk true)) : ℂ)) *
        (movingFrequencyCoefficient value outside μ childBound pivotBound V
          (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small (bulk false) XL XR *
          star (movingFrequencyCoefficient value outside μ childBound pivotBound V
          (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small (bulk true) XL XR)) := by ring
    _ = _ := by rw [movingBulkLeafProduct_pair_eq_cutoffs value hvalue outside cb cd n bulk]

end Ostmann

end OAI
