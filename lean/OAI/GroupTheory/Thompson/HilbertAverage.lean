import OAI.GroupTheory.Thompson.UnitBall
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace OAI

/-!
# Finite averages in the unit ball

The norm bounds hold in any real seminormed space. Inner-product expansions are
kept in a separate section and require a real inner-product space.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

universe uE

namespace ThompsonNonamenability

section Normed

variable {E : Type uE} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {D : ℕ}

/-- The equally weighted mean of a finite family. -/
def finMean (x : Fin D → E) : E :=
  (D : ℝ)⁻¹ • ∑ i, x i

theorem finMean_sub (x y : Fin D → E) :
    finMean (fun i => x i - y i) = finMean x - finMean y := by
  simp only [finMean, Finset.sum_sub_distrib, smul_sub]

@[simp] theorem finMean_const (hD : 0 < D) (z : E) :
    finMean (fun _ : Fin D => z) = z := by
  have hD' : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  rw [finMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ D z, smul_smul, inv_mul_cancel₀ hD', one_smul]

/-- The squared norm of a mean is bounded by the mean of the squared norms. -/
theorem norm_finMean_sq_le (hD : 0 < D) (x : Fin D → E) :
    ‖finMean x‖ ^ 2 ≤ (D : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 := by
  have hD' : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hc : 0 ≤ (D : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg D)
  have hcs : (∑ i, ‖x i‖) ^ 2 ≤ (D : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin D => (1 : ℝ)) (fun i => ‖x i‖)
  have hs : ‖∑ i, x i‖ ^ 2 ≤ (D : ℝ) * ∑ i, ‖x i‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ x) 2).trans hcs
  calc
    ‖finMean x‖ ^ 2 = ((D : ℝ)⁻¹) ^ 2 * ‖∑ i, x i‖ ^ 2 := by
      rw [finMean, norm_smul_of_nonneg hc, mul_pow]
    _ ≤ ((D : ℝ)⁻¹) ^ 2 * ((D : ℝ) * ∑ i, ‖x i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = (D : ℝ)⁻¹ * ((D : ℝ)⁻¹ * (D : ℝ)) * ∑ i, ‖x i‖ ^ 2 := by
      ring
    _ = (D : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 := by
      rw [inv_mul_cancel₀ hD', mul_one]

/-- Averaging a finite family in the closed unit ball preserves its norm bound. -/
theorem finMean_mem_unitBall (hD : 0 < D) (x : Fin D → UnitBall E) :
    ‖finMean (fun i => (x i : E))‖ ≤ 1 := by
  have hD' : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hc : 0 ≤ (D : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg D)
  have hs : ‖∑ i, (x i : E)‖ ≤ (D : ℝ) := by
    calc
      ‖∑ i, (x i : E)‖ ≤ ∑ i, ‖(x i : E)‖ := norm_sum_le Finset.univ _
      _ ≤ ∑ _i : Fin D, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (x i).property)
      _ = (D : ℝ) := by simp
  calc
    ‖finMean (fun i => (x i : E))‖ = (D : ℝ)⁻¹ * ‖∑ i, (x i : E)‖ := by
      rw [finMean, norm_smul_of_nonneg hc]
    _ ≤ (D : ℝ)⁻¹ * (D : ℝ) := mul_le_mul_of_nonneg_left hs hc
    _ = 1 := inv_mul_cancel₀ hD'

/-- The equally weighted mean, bundled with its unit-ball bound. -/
def ballMean (hD : 0 < D) (x : Fin D → UnitBall E) : UnitBall E :=
  ⟨finMean (fun i => (x i : E)), finMean_mem_unitBall hD x⟩

@[simp] theorem coe_ballMean (hD : 0 < D) (x : Fin D → UnitBall E) :
    (ballMean hD x : E) = finMean (fun i => (x i : E)) := rfl

end Normed

section InnerProduct

variable {E : Type uE} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D K : ℕ}

/-- The inner product of two finite averages is the average of all pairings. -/
theorem inner_finMean (x : Fin D → E) (y : Fin K → E) :
    ⟪finMean x, finMean y⟫_ℝ =
      ((D : ℝ)⁻¹ * (K : ℝ)⁻¹) * ∑ i, ∑ j, ⟪x i, y j⟫_ℝ := by
  simp_rw [finMean, real_inner_smul_left, real_inner_smul_right,
    sum_inner, inner_sum, mul_assoc]

/-- Expand the squared norm of an average into all pairwise inner products. -/
theorem norm_finMean_sq (x : Fin D → E) :
    ‖finMean x‖ ^ 2 = ((D : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, ⟪x i, x j⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, inner_finMean, pow_two]

end InnerProduct

end ThompsonNonamenability

end

end OAI
