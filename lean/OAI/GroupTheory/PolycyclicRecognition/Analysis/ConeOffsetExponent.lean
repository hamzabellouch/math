import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

/-! # Cancellation of the three exponential counts in the offset argument -/

namespace PolycyclicRecognition

open Filter
open scoped Topology BigOperators

/-- Assigning finitely many endpoints to tiles multiplies the tile count by
the uniform per-tile bound; an assignment need not be injective. -/
theorem card_le_real_tile_bound {n m : ℕ} (tile : Fin n → Fin m) {B : ℝ}
    (hB : ∀ j : Fin m, ((Finset.univ.filter fun i => tile i = j).card : ℝ) ≤ B) :
    (n : ℝ) ≤ (m : ℝ) * B := by
  classical
  have hc : n = ∑ j : Fin m, (Finset.univ.filter fun i => tile i = j).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := tile) (by simp))
  calc
    (n : ℝ) = ∑ j : Fin m, ((Finset.univ.filter fun i => tile i = j).card : ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ _j : Fin m, B := Finset.sum_le_sum (fun j _ => hB j)
    _ = (m : ℝ) * B := by simp

/-- Source exponent `P₁`, tiling exponent `P₁-P₂`, and tile-image exponent
`P₂-ℓ` force `ℓ≤0`. Every subexponential loss is retained explicitly. -/
theorem cone_offset_exponent_nonpos
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (points tiles : ℕ → ℕ) (assign : ∀ k, Fin (points k) → Fin (tiles k))
    (lower tileLoss pointLoss : ℕ → ℝ)
    (hlower : HasSubexponentialLowerBoundSeq scale lower)
    (htile : HasSubexponentialUpperBoundSeq scale tileLoss)
    (hpoint : HasSubexponentialUpperBoundSeq scale pointLoss)
    (htile0 : ∀ᶠ k in atTop, 0 ≤ tileLoss k)
    (hpoint0 : ∀ᶠ k in atTop, 0 ≤ pointLoss k)
    {P₁ P₂ ℓ : ℝ}
    (hsource : ∀ᶠ k in atTop, lower k * Real.exp (scale k * P₁) ≤ points k)
    (htiles : ∀ᶠ k in atTop,
      (tiles k : ℝ) ≤ tileLoss k * Real.exp (scale k * (P₁ - P₂)))
    (himages : ∀ᶠ k in atTop, ∀ j : Fin (tiles k),
      ((Finset.univ.filter fun i => assign k i = j).card : ℝ) ≤
        pointLoss k * Real.exp (scale k * (P₂ - ℓ))) : ℓ ≤ 0 := by
  have hu := htile.mul hpoint htile0
  have he : P₁ ≤ P₁ - ℓ := exponent_le_of_sequence_subexponential_bounds
    hs hlower hu (by
      filter_upwards [hsource, htiles, himages, hpoint0] with k hsrc htc him hp
      have hc := card_le_real_tile_bound (assign k) him
      calc
        lower k * Real.exp (scale k * P₁) ≤ (points k : ℝ) := hsrc
        _ ≤ (tiles k : ℝ) * (pointLoss k * Real.exp (scale k * (P₂ - ℓ))) := hc
        _ ≤ (tileLoss k * Real.exp (scale k * (P₁ - P₂))) *
            (pointLoss k * Real.exp (scale k * (P₂ - ℓ))) :=
          mul_le_mul_of_nonneg_right htc (mul_nonneg hp (Real.exp_pos _).le)
        _ = (tileLoss k * pointLoss k) * Real.exp (scale k * (P₁ - ℓ)) := by
          rw [mul_mul_mul_comm, ← Real.exp_add]
          congr 2
          ring)
  linarith

end PolycyclicRecognition

end OAI
