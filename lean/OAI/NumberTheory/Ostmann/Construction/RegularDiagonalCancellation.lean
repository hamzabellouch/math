import OAI.NumberTheory.Ostmann.Construction.RegularResidueNorm
import OAI.NumberTheory.Ostmann.Arithmetic.CRTLineAverage

namespace OAI

/-! # Exact cancellation of the diagonal regular-prime unit loss

The external integer giant is restricted to units. At a regular prime
carrying a squared transform, its energy cancels that restriction exactly.
At an outer compensation prime the factor left over is `1 - 1/p`.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def externalRegularLocal {p : ℕ} [Fact p.Prime]
    (active : Bool) (a : (ZMod p)ˣ) (g : ZMod p → ℂ)
    (z : ZMod p × (ZMod p)ˣ) : ℝ :=
  if z.1 = 0 then 0 else
    if active then ‖g ((a : ZMod p) * (z.1 * (z.2 : ZMod p))⁻¹)‖ ^ 2 else 1

theorem externalRegularLocal_sum_first {p : ℕ} [Fact p.Prime]
    (active : Bool) (a : (ZMod p)ˣ) (g : ZMod p → ℂ)
    (hg : g 0 = 0) (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) = p)
    (v : (ZMod p)ˣ) :
    (∑ x : ZMod p, externalRegularLocal active a g (x, v)) =
      if active then (p : ℝ) else Fintype.card (ZMod p)ˣ := by
  rw [← sum_units_eq_sum_of_zero
    (fun x => externalRegularLocal active a g (x, v)) (by simp [externalRegularLocal])]
  cases active
  · simp [externalRegularLocal, Units.ne_zero]
  · have hs := sum_regular_local_norm (a * v⁻¹) g hg
    rw [henergy] at hs
    simp only [↓reduceIte]
    convert hs using 1
    apply Finset.sum_congr rfl
    intro u _
    simp only [externalRegularLocal, Units.ne_zero, ↓reduceIte]
    simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc]

theorem externalRegularLocal_average {p : ℕ} [Fact p.Prime]
    (active : Bool) (a : (ZMod p)ˣ) (g : ZMod p → ℂ)
    (hg : g 0 = 0) (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) = p) :
    (Fintype.card (ZMod p × (ZMod p)ˣ) : ℝ)⁻¹ *
      (∑ z, externalRegularLocal active a g z) =
        if active then 1 else 1 - (p : ℝ)⁻¹ := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hu : (0 : ℝ) < Fintype.card (ZMod p)ˣ := by exact_mod_cast Fintype.card_pos
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [externalRegularLocal_sum_first active a g hg henergy]
  rw [Fintype.card_prod, ZMod.card, Nat.cast_mul]
  cases active
  · simp only [Bool.false_eq_true, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one] at *
    field_simp
  · simp only [↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-- This is the exact regular-prime integral in the diagonal environment,
including the outer compensation slots which carry no transform. -/
theorem crt_external_regular_cancellation {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (active : I → Bool) (a : ∀ i, (ZMod (p i))ˣ) (g : ∀ i, ZMod (p i) → ℂ)
    (hg : ∀ i, g i 0 = 0) (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i) :
    (Fintype.card (ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) : ℝ)⁻¹ *
      (∑ z, ∏ i, externalRegularLocal (active i) (a i) (g i) (crtExternalPairEquiv p hc z i)) =
    ∏ i, if active i then 1 else 1 - (p i : ℝ)⁻¹ := by
  rw [crt_external_pair_average p hc (fun i => externalRegularLocal (active i) (a i) (g i))]
  apply Finset.prod_congr rfl
  intro i _
  exact externalRegularLocal_average (active i) (a i) (g i) (hg i) (henergy i)

theorem external_regular_cancellation_factor_le_one {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) :
    (∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹) ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i _
    have hp : (1 : ℝ) ≤ p i := by exact_mod_cast (Fact.out : (p i).Prime).one_le
    split
    · norm_num
    · exact sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr hp)
  · intro i _
    split
    · exact le_rfl
    · have hinv : (0 : ℝ) ≤ (p i : ℝ)⁻¹ := by positivity
      linarith

end Ostmann

end OAI
