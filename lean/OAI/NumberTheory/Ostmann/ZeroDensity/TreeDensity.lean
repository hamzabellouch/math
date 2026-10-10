import OAI.NumberTheory.Ostmann.ZeroDensity.PairDensity
import OAI.NumberTheory.Ostmann.Characters.DifferenceMoment

namespace OAI

/-!
# Iterating the elementary tree density estimate

A split plan allows the remaining unit parameters to depend on every
previous split coordinate. The bound is uniform over those choices.
The separate rational-coordinate lemmas identify the manuscript's tree
with this inverse-square split law on valid ancestor data.
-/

namespace Ostmann

open scoped BigOperators

/-- Parameters for an ordered binary tree, with adaptive descendant data. -/
def BinarySplitPlan (U : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => U × (U → BinarySplitPlan U n) × (U → BinarySplitPlan U n)

noncomputable def splitTreeMoment {p : ℕ} [Fact p.Prime] (w : ZMod p → ℝ) :
    (n : ℕ) → BinarySplitPlan (ZMod p)ˣ n → ZMod p → ℝ
  | 0, _, d => if d = 0 then 0 else w d
  | n + 1, plan, d => if d = 0 then 0 else
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ m : (ZMod p)ˣ,
        let t := plan.1 * (m⁻¹) ^ 2
        if t = 1 then 0 else
          splitTreeMoment w n (plan.2.1 m)
            (d * (t : ZMod p) / ((t : ZMod p) - 1)) *
          splitTreeMoment w n (plan.2.2 m)
            (d / ((t : ZMod p) - 1))

/-- Parameter-free density majorant, including the zero convention. -/
noncomputable def treeDensityMajorant {p : ℕ} [Fact p.Prime] (w : ZMod p → ℝ) :
    ℕ → ZMod p → ℝ
  | 0, d => if d = 0 then 0 else w d
  | n + 1, d => if d = 0 then 0 else
      (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
        differenceMoment (treeDensityMajorant w n) (treeDensityMajorant w n) d

/-- The successive bounds are `E`, `2 E²`, `8 E⁴`, and so on. -/
def binaryMomentBound (E : ℝ) : ℕ → ℝ
  | 0 => E
  | n + 1 => 2 * binaryMomentBound E n ^ 2

theorem treeDensityMajorant_zero {p : ℕ} [Fact p.Prime] (w : ZMod p → ℝ) (n : ℕ) :
    treeDensityMajorant w n 0 = 0 := by
  cases n <;> simp [treeDensityMajorant]

theorem treeDensityMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (n : ℕ) (d : ZMod p) :
    0 ≤ treeDensityMajorant w n d := by
  induction n generalizing d with
  | zero => simp only [treeDensityMajorant]; split_ifs; exact le_rfl; exact hw d
  | succ n ih =>
    simp only [treeDensityMajorant]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by positivity) (differenceMoment_nonneg _ _ ih ih d)

theorem splitTreeMoment_nonneg {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (n : ℕ)
    (plan : BinarySplitPlan (ZMod p)ˣ n) (d : ZMod p) :
    0 ≤ splitTreeMoment w n plan d := by
  induction n generalizing d with
  | zero => simp only [splitTreeMoment]; split_ifs; exact le_rfl; exact hw d
  | succ n ih =>
    simp only [splitTreeMoment]
    split_ifs
    · exact le_rfl
    · apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro m _
      dsimp
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (ih _ _) (ih _ _)

/-- Each valid split costs at most the factor two in the square-fiber bound. -/
theorem splitTreeMoment_le_majorant {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (n : ℕ)
    (plan : BinarySplitPlan (ZMod p)ˣ n) (d : ZMod p) :
    splitTreeMoment w n plan d ≤ treeDensityMajorant w n d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    by_cases hd : d = 0
    · simp [hd, splitTreeMoment, treeDensityMajorant]
    · simp only [splitTreeMoment, treeDensityMajorant, hd, ite_false]
      have h := pair_inverse_square_density (Units.mk0 d hd) plan.1
        (treeDensityMajorant w n) (treeDensityMajorant w n)
        (treeDensityMajorant_zero w n) (treeDensityMajorant_zero w n)
        (treeDensityMajorant_nonneg w hw n) (treeDensityMajorant_nonneg w hw n)
      calc
        _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ m : (ZMod p)ˣ,
            let t := plan.1 * (m⁻¹) ^ 2
            if t = 1 then 0 else
              treeDensityMajorant w n (d * (t : ZMod p) / ((t : ZMod p) - 1)) *
                treeDensityMajorant w n (d / ((t : ZMod p) - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro m _
          dsimp
          split_ifs
          · exact le_rfl
          · exact mul_le_mul (ih _ _) (ih _ _)
              (splitTreeMoment_nonneg w hw n _ _) (treeDensityMajorant_nonneg w hw n _)
        _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
            (2 * differenceMoment (treeDensityMajorant w n) (treeDensityMajorant w n) d) :=
          mul_le_mul_of_nonneg_left h (by positivity)
        _ = _ := by ring

theorem treeDensityMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (E : ℝ)
    (hE : (∑ d : (ZMod p)ˣ, w d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ E) (n : ℕ) :
    (∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ binaryMomentBound E n := by
  have hU : 0 < (Fintype.card (ZMod p)ˣ : ℝ) := by exact_mod_cast Fintype.card_pos
  induction n with
  | zero =>
    simpa only [treeDensityMajorant, Units.ne_zero, ite_false, binaryMomentBound] using hE
  | succ n ih =>
    have hzero := treeDensityMajorant_zero w n
    have hsum := sum_units_eq_sum_of_zero (treeDensityMajorant w n) hzero
    have hnn : 0 ≤ (∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
        (Fintype.card (ZMod p)ˣ : ℝ) := by
      apply div_nonneg _ hU.le
      exact Finset.sum_nonneg fun d _ => treeDensityMajorant_nonneg w hw n d
    calc
      _ = (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
          (∑ d : (ZMod p)ˣ,
            differenceMoment (treeDensityMajorant w n) (treeDensityMajorant w n) d) /
            (Fintype.card (ZMod p)ˣ : ℝ) := by
        simp only [treeDensityMajorant, Units.ne_zero, ite_false, ← Finset.mul_sum]
      _ ≤ (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
          ((∑ x : ZMod p, treeDensityMajorant w n x) ^ 2) /
            (Fintype.card (ZMod p)ˣ : ℝ) := by
        apply div_le_div_of_nonneg_right _ hU.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [pow_two] using sum_units_differenceMoment_le
          (treeDensityMajorant w n) (treeDensityMajorant w n)
          (treeDensityMajorant_nonneg w hw n) (treeDensityMajorant_nonneg w hw n)
      _ = 2 * ((∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
          (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by rw [← hsum]; ring
      _ ≤ 2 * binaryMomentBound E n ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn ih 2) (by norm_num)
      _ = _ := rfl

/-- Uniform root averaging permits a different descendant plan at each root value. -/
theorem splitTreeMoment_mean_le {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (E : ℝ)
    (hE : (∑ d : (ZMod p)ˣ, w d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ E)
    (n : ℕ) (plans : (ZMod p)ˣ → BinarySplitPlan (ZMod p)ˣ n) :
    (∑ d : (ZMod p)ˣ, splitTreeMoment w n (plans d) d) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ binaryMomentBound E n := by
  apply le_trans _ (treeDensityMajorant_mean_le w hw E hE n)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun d _ => splitTreeMoment_le_majorant w hw n (plans d) d

/-- The recursive density bound in closed form. -/
theorem binaryMomentBound_eq (E : ℝ) (n : ℕ) :
    binaryMomentBound E n = (2 * E) ^ (2 ^ n) / 2 := by
  induction n with
  | zero => simp [binaryMomentBound]
  | succ n ih =>
    rw [binaryMomentBound, ih, pow_succ (2 : ℕ), pow_mul]
    ring

/-- The `3^r` estimate for an `L²`-normalized test at an odd prime. -/
theorem splitTreeMoment_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (n : ℕ) (plans : (ZMod p)ˣ → BinarySplitPlan (ZMod p)ˣ n) :
    (∑ d : (ZMod p)ˣ, splitTreeMoment (fun x => ‖g x‖ ^ 2) n (plans d) d) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  have hpr : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  have hsum := sum_units_eq_sum_of_zero (fun x => ‖g x‖ ^ 2) (by simp [hg])
  have hE : (∑ d : (ZMod p)ˣ, ‖g d‖ ^ 2) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ 3 / 2 := by
    rw [hU, hsum]
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr
    linarith
  have h := splitTreeMoment_mean_le (fun x => ‖g x‖ ^ 2) (fun _ => sq_nonneg _)
    (3 / 2) hE n plans
  rw [binaryMomentBound_eq] at h
  norm_num only [show (2 : ℝ) * (3 / 2) = 3 by norm_num] at h
  exact h.trans (by have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (2 ^ n); linarith)

end Ostmann

end OAI
