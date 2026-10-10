import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSpectatorGain
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSupportedArithmetic

namespace OAI

/-! # Pointwise cost of the actual normalized spectator transforms -/

namespace Ostmann
open scoped Classical BigOperators

theorem normalizedResidueTransform_norm_le_sqrt {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    ‖normalizedResidueTransform S x‖ ≤ Real.sqrt (p : ℝ) := by
  have hx : ‖normalizedResidueTransform S x‖ ^ 2 ≤
      ∑ y : ZMod p, ‖normalizedResidueTransform S y‖ ^ 2 :=
    Finset.single_le_sum (f := fun y : ZMod p => ‖normalizedResidueTransform S y‖ ^ 2)
      (fun y _ => sq_nonneg _) (Finset.mem_univ x)
  rw [normalizedResidueTransform_energy S hS hSp] at hx
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p),
    Real.sqrt_nonneg (p : ℝ), norm_nonneg (normalizedResidueTransform S x)]

theorem normalizedResidueTransform_norm_le_prime {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    ‖normalizedResidueTransform S x‖ ≤ p := by
  apply (normalizedResidueTransform_norm_le_sqrt S hS hSp x).trans
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p), Real.sqrt_nonneg (p : ℝ)]

/-- A common prime upper bound controls all actual pointwise spectator
factors. This cost is retained in the cell error, separate from signed gain. -/
theorem moving_spectator_product_cost (n m : ℕ) (p : Fin m → ℕ)
    (V : ℝ) (hp : ∀ i, (p i : ℝ) ≤ Real.exp V) :
    (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp ((2 ^ (n + 1) : ℕ) * (m : ℝ) * V) := by
  calc
    _ ≤ ∏ _i : Fin m, (Real.exp V) ^ (2 ^ (n + 1)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hp i) _
    _ = _ := by
      simp only [← Real.exp_nat_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      ring

theorem moving_spectator_linear_cost (n m : ℕ) (p : Fin m → ℕ)
    (K L A : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (_hA : 0 ≤ A)
    (hm : (m : ℝ) ≤ K * L) (hamp : A ≤ Real.exp (K * L))
    (hp : ∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) :
    A * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp ((((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K * L *
        Real.exp ((1 / 1000 : ℝ) * L)) := by
  have hE : 1 ≤ Real.exp ((1 / 1000 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by positivity)
  calc
    _ ≤ Real.exp (K * L) *
        Real.exp ((2 ^ (n + 1) : ℕ) * (m : ℝ) * Real.exp ((1 / 1000 : ℝ) * L)) :=
      mul_le_mul hamp (moving_spectator_product_cost n m p _ hp)
        (Finset.prod_nonneg fun i _ => by positivity) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (2 ^ (n + 1))))
        (Real.exp_nonneg ((1 / 1000 : ℝ) * L))
      have hKL := mul_le_mul_of_nonneg_left hE (mul_nonneg hK hL)
      nlinarith

theorem moving_frozen_residue_coefficient_norm {σ J : Type*}
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (n m : ℕ) (data : Bool → MovingSlotData σ n) (childBound : ℕ → ℕ)
    (R : ℤ) (r : ℕ) [NeZero r] (P : PublishedProgressionInput) (Q : ℕ)
    (y : ℝ) (hy : 0 ≤ y) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (hSp : ∀ i, (S i).card < p i)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (samples : Bool → MovingSampleSlots σ n)
    (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (a : J → (ZMod r)ˣ) (z : ∀ i, TreeLeafIndex n × Fin m → (ZMod (p i))ˣ) :
    ‖frozenBulkFrequencyFactor base slot outside F E data childBound R r P Q y a *
      ∏ i, frozenBulkSpectatorHaar base n m t small samples (twist i) perm
        (normalizedResidueTransform (S i)) (z i)‖ ≤
      (2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
        ‖movingDataWeight (F true) (E true) (data true)‖)) *
          ∏ i, (p i : ℝ) ^ (2 ^ (n + 1)) := by
  rw [norm_mul, norm_prod]
  apply mul_le_mul
    (frozenBulkFrequencyFactor_norm_le base slot outside F E data childBound R r P Q y hy a)
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ =>
      frozenBulkSpectatorHaar_norm_le base n m t small samples (twist i) perm
        (normalizedResidueTransform (S i)) (p i) (Nat.cast_nonneg _)
        (normalizedResidueTransform_norm_le_prime (S i) (hS i) (hSp i)) (z i)))
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)

end Ostmann

end OAI
