import OAI.Geometry.SurfaceImmersion.Correction.FiniteSmootherWeighted

namespace OAI

/-! The finite-input smoothing-tail estimate at every output order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory WeightedEstimates
open JetPolynomial (Base)

def tailConstant (r : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (r + 1), approximationConstant r j) +
    (1 + ∫ y, ‖kernel 0 y‖) ^ r

lemma approximationConstant_le_tail {r j : ℕ} (hj : j ≤ r) :
    approximationConstant r j ≤ tailConstant r := by
  have h : approximationConstant r j ≤
      ∑ i ∈ Finset.range (r + 1), approximationConstant r i :=
    Finset.single_le_sum (fun i _ => approximationConstant_nonneg r i)
      (Finset.mem_range.mpr (by omega))
  exact h.trans (le_add_of_nonneg_right (pow_nonneg
    (add_nonneg zero_le_one (integral_nonneg fun _ => norm_nonneg _)) r))

lemma residualConstant_le_tail (r : ℕ) :
    (1 + ∫ y, ‖kernel 0 y‖) ^ r ≤ tailConstant r :=
  le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => approximationConstant_nonneg r i)

lemma tailConstant_nonneg (r : ℕ) : 0 ≤ tailConstant r :=
  (approximationConstant_nonneg r 0).trans (approximationConstant_le_tail (Nat.zero_le r))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Only the finite order `r` is used in the approximation term; uncontrolled
higher input derivatives enter linearly, multiplied by `(τ/t)^r`. -/
theorem weighted_smoothing_tail (r m : ℕ) {s t τ B C : ℝ}
    (hτ : 0 < τ) (hτs : τ ≤ s) (hst : s ≤ t)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hBr : WeightedBound Set.univ t r B f)
    (hCm : WeightedBound Set.univ t m C f) :
    WeightedBound Set.univ τ m
      (tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
      (f - finiteSmooth r s f) := by
  have hs : 0 < s := hτ.trans_le hτs
  have ht : 0 < t := hs.trans_le hst
  have hτt : τ ≤ t := hτs.trans hst
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hBr.norm_le (Set.mem_univ 0))
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hCm.norm_le (Set.mem_univ 0))
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hjr : j ≤ r
  · have hbr : ∀ y, ‖iteratedFDeriv ℝ r f y‖ ≤ B / t ^ r := fun y => by
      simpa only [iteratedFDerivWithin_univ] using hBr.deriv_le ht le_rfl (Set.mem_univ y)
    have h := finiteSmooth_approximation r 0 j hjr hs hf hfc
      (fun y => by rw [Nat.zero_add]; exact hbr y) x
    rw [Nat.zero_add] at h
    have hp : τ ^ j * s ^ (r - j) ≤ s ^ r := by
      calc
        _ ≤ s ^ j * s ^ (r - j) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hτ.le hτs j) (pow_nonneg hs.le _)
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjr]
    calc
      _ ≤ τ ^ j * (approximationConstant r j * s ^ (r - j) * (B / t ^ r)) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hτ.le _)
      _ = (approximationConstant r j * B / t ^ r) * (τ ^ j * s ^ (r - j)) := by ring
      _ ≤ (approximationConstant r j * B / t ^ r) * s ^ r :=
        mul_le_mul_of_nonneg_left hp (div_nonneg
          (mul_nonneg (approximationConstant_nonneg _ _) hB) (pow_nonneg ht.le _))
      _ = approximationConstant r j * (B * (s / t) ^ r) := by rw [div_pow]; ring
      _ ≤ tailConstant r * (B * (s / t) ^ r) :=
        mul_le_mul_of_nonneg_right (approximationConstant_le_tail hjr)
          (mul_nonneg hB (pow_nonneg (div_nonneg hs.le ht.le) _))
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg hC (pow_nonneg (div_nonneg hτ.le ht.le) _)))
        (tailConstant_nonneg r)
  · have hrj : r ≤ j := by omega
    have hbc : ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ C / t ^ j := fun y => by
      simpa only [iteratedFDerivWithin_univ] using hCm.deriv_le ht hj (Set.mem_univ y)
    have h := iterated_residual_bounded hs r j hf hfc hbc x
    rw [error_finiteSmooth]
    have hp : (τ / t) ^ j ≤ (τ / t) ^ r :=
      pow_le_pow_of_le_one (div_nonneg hτ.le ht.le) ((div_le_one ht).mpr hτt) hrj
    calc
      _ ≤ τ ^ j * ((1 + ∫ y, ‖kernel 0 y‖) ^ r * (C / t ^ j)) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hτ.le _)
      _ = (1 + ∫ y, ‖kernel 0 y‖) ^ r * C * (τ / t) ^ j := by rw [div_pow]; ring
      _ ≤ (1 + ∫ y, ‖kernel 0 y‖) ^ r * C * (τ / t) ^ r :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg
          (pow_nonneg (add_nonneg zero_le_one (integral_nonneg fun _ => norm_nonneg _)) _) hC)
      _ ≤ tailConstant r * (C * (τ / t) ^ r) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (residualConstant_le_tail r)
          (mul_nonneg hC (pow_nonneg (div_nonneg hτ.le ht.le) _))
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg hB (pow_nonneg (div_nonneg hs.le ht.le) _)))
        (tailConstant_nonneg r)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
