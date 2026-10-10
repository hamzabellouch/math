import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePrior
import OAI.NumberTheory.Ostmann.Construction.InitialSelectedPrior

namespace OAI

/-! # Actual compensation-prior support bounds for the first transfers -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingCompensation_product_lower {σ : Type*} (value : σ → ℕ)
    (μ : σ → ℝ) (c : ℝ)
    (hlower : ∀ x, μ x ≠ 0 → Real.exp (c - 1) ≤ (value x : ℝ))
    (n : ℕ) (a : TreeLeafTuple (Fin 4 → σ) n)
    (ha : movingCompensationPrior μ n a ≠ 0) :
    Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * (c - 1)) ≤
      (MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a)) : ℝ) := by
  induction n with
  | zero =>
    change Real.exp (4 * (c - 1)) ≤
      (MovingSlotReversal.naturalProduct value (List.ofFn a) : ℝ)
    have hprod : (∏ i : Fin 4, Real.exp (c - 1)) ≤ ∏ i : Fin 4, (value (a i) : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => Real.exp_nonneg _)
        (fun i hi => hlower _ (Finset.prod_ne_zero_iff.mp ha i hi))
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_nat_mul, MovingSlotReversal.naturalProduct,
      List.map_ofFn, List.prod_ofFn, Function.comp_def, Nat.cast_prod, Nat.cast_ofNat] using hprod
  | succ n ih =>
    have hL := ih a.1 (left_ne_zero_of_mul ha)
    have hR := ih a.2 (right_ne_zero_of_mul ha)
    change Real.exp (((2 ^ (n + 1) * 4 : ℕ) : ℝ) * (c - 1)) ≤
      (MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a.1) ++
          flattenMovingSlots n (movingCompensationSlots n a.2)) : ℝ)
    rw [movingNaturalProduct_append]
    simp only [Nat.cast_mul] at hL hR ⊢
    calc
      _ = Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * (c - 1)) *
          Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * (c - 1)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        rw [pow_succ]
        ring
      _ ≤ _ := by
        simpa only [Nat.cast_mul] using
          mul_le_mul hL hR (Real.exp_nonneg _) (Nat.cast_nonneg _)

theorem movingInsertedPivot_product_lower {σ : Type*} (value : σ → ℕ)
    (μ : σ → ℝ) (c G : ℝ) (φ : ℝ → ℝ)
    (hlower : ∀ x, μ x ≠ 0 → Real.exp (c - 1) ≤ (value x : ℝ))
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (n : ℕ) (a : TreeLeafTuple (Fin 4 → σ) n)
    (ha : movingCompensationPrior μ n a ≠ 0)
    (p : ℕ) (hp : 0 < p) (hφ : φ (Real.log p - G) ≠ 0) :
    Real.exp (G - 1 + ((2 ^ n * 4 : ℕ) : ℝ) * (c - 1)) ≤
      (p * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a)) : ℕ) := by
  have habs : |Real.log p - G| < 1 := by
    by_contra hn
    exact hφ (hout _ (not_lt.mp hn))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpbound : Real.exp (G - 1) ≤ (p : ℝ) := by
    have hlog : G - 1 ≤ Real.log (p : ℝ) := by linarith [(abs_lt.mp habs).1]
    exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hpR)
  rw [Real.exp_add]
  simpa only [Nat.cast_mul] using
    mul_le_mul hpbound (movingCompensation_product_lower value μ c hlower n a ha)
      (Real.exp_nonneg _) (Nat.cast_nonneg _)

end Ostmann

end OAI
