import OAI.NumberTheory.Ostmann.Construction.InitialMovingOriginalFactor
import OAI.NumberTheory.Ostmann.Construction.InitialHalfLogMap

namespace OAI

/-! # The exact retained half-bulk factors in a pair of Fourier coefficients -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalCoefficientPair_initial_halves {P J : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List P) n) (slot : Bool → TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    let plain := fun side => movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
      φ G n s small (bulkSlotLeaves n (b + b) (slot side)) XL XR
    let weighted := fun side => movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n s small (bulkSlotLeaves n (b + b) (slot side)) XL XR
    weighted false * star (weighted true) =
      ((initialLogSumWeight value cd sl * initialLogSumWeight value cd sr) ^
        (2 ^ n + 2 ^ n) : ℝ) *
      ((∏ j, bulkLogCutoffWeight (fun p => (value p : ℝ)) cb
        (initialPairedHalfLogSlots n b slot j) : ℝ) : ℂ) *
      (plain false * star (plain true)) := by
  dsimp only
  rw [movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s small (slot false) hsmall hlen XL XR,
    movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s small (slot true) hsmall hlen XL XR,
    star_mul]
  have hp := initialHalfBulkProduct_pair_log_slots value hvalue b d cb cd sl sr n slot
  let C := fun side => movingFrequencyCoefficient value outside μ childBound pivotBound V
    (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
    φ G n s small (bulkSlotLeaves n (b + b) (slot side)) XL XR
  calc
    _ = ((initialHalfBulkProduct value b d cb cd sl sr n (slot false) : ℂ) *
        star (initialHalfBulkProduct value b d cb cd sl sr n (slot true) : ℂ)) *
        (C false * star (C true)) := by dsimp only [C]; ring
    _ = _ := by rw [hp]

end Ostmann

end OAI
