import OAI.Geometry.SurfaceImmersion.Correction.SmoothingTailBounds

namespace OAI

/-! Smoothing bounds with an unweighted finite derivative prefix. In the
correction scheme the map has prefix order two and the metric defect order zero. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates MeasureTheory
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def ShiftedBound (q m : ℕ) (s C : ℝ) (f : Base → V) : Prop :=
  ∀ j ≤ q + m, ∀ x, s ^ (j - q) * ‖iteratedFDeriv ℝ j f x‖ ≤ C

lemma ShiftedBound.deriv_le {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) {j : ℕ} (hj : j ≤ q + m) (x : Base) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C / s ^ (j - q) := by
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  simpa only [mul_comm] using h j hj x

/-- An unweighted prefix of any lower order is controlled by a shifted bound. -/
lemma ShiftedBound.prefix {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    {j : ℕ} (hj : j ≤ q + m) :
    WeightedBound Set.univ 1 j (C / s ^ (j - q)) f := by
  intro i hi x _
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ]
  apply (h.deriv_le hs (hi.trans hj) x).trans
  exact div_le_div_of_nonneg_left hC (pow_pos hs _)
    (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le_sub_right hi q))

/-- No derivative in the unweighted prefix incurs a smoothing-scale loss. -/
theorem finiteSmooth_shifted_gain (r q m : ℕ) {s C : ℝ} (hs : 0 < s)
    (hC : 0 ≤ C) {f : Base → V} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hb : WeightedBound Set.univ 1 q C f) :
    ShiftedBound q m s
      (((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) + weightedGainConstant r m) * C)
      (finiteSmooth r s f) := by
  intro j hj x
  by_cases hjq : j ≤ q
  · have hi : ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ C := fun y => by
      simpa only [one_pow, one_mul, iteratedFDerivWithin_univ] using hb j hjq y (Set.mem_univ y)
    have h := finiteSmooth_bounded r j hs hf hc hi x
    rw [Nat.sub_eq_zero_of_le hjq, pow_zero, one_mul]
    apply h.trans
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (weightedGainConstant_nonneg r m)) hC
  · have hi : ∀ y, ‖iteratedFDeriv ℝ q f y‖ ≤ C := fun y => by
      simpa only [one_pow, one_mul, iteratedFDerivWithin_univ] using hb q le_rfl y (Set.mem_univ y)
    have h := finiteSmooth_gain_from_derivatives r q (j - q) hs hf hc hi x
    rw [Nat.add_sub_of_le (by omega : q ≤ j)] at h
    have hsum : gainConstant r (j - q) ≤ weightedGainConstant r m :=
      Finset.single_le_sum (fun i _ => gainConstant_nonneg r i) (Finset.mem_range.mpr (by omega))
    calc
      _ ≤ s ^ (j - q) * ((s ^ (j - q))⁻¹ * gainConstant r (j - q) * C) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hs.le _)
      _ = gainConstant r (j - q) * C := by field_simp
      _ ≤ (((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) + weightedGainConstant r m) * C) := by
        apply mul_le_mul_of_nonneg_right _ hC
        exact hsum.trans (le_add_of_nonneg_left (by positivity))

/-- The original shifted norm remains bounded independently of the smoothing scale. -/
theorem finiteSmooth_shifted_bounded (r q m : ℕ) {s t C : ℝ}
    (hs : 0 < s) (ht : 0 < t) {f : Base → V}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hb : ShiftedBound q m t C f) :
    ShiftedBound q m t ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C)
      (finiteSmooth r s f) := by
  intro j hj x
  have h := finiteSmooth_bounded r j hs hf hc (fun y => hb.deriv_le ht hj y) x
  calc
    _ ≤ t ^ (j - q) * ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) *
        (C / t ^ (j - q))) := mul_le_mul_of_nonneg_left h (pow_nonneg ht.le _)
    _ = _ := by field_simp

variable [CompleteSpace V]

/-- A finite shifted input order suffices for the approximation term. Higher
input derivatives occur linearly, with the two-scale decaying factor. -/
theorem shifted_smoothing_tail (r q m : ℕ) {s t τ B C : ℝ}
    (hτ : 0 < τ) (hτs : τ ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1)
    (hB : 0 ≤ B) (hC : 0 ≤ C) {f : Base → V}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hBr : ShiftedBound q r t B f) (hCm : ShiftedBound q m t C f) :
    ShiftedBound q m τ
      (tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
      (f - finiteSmooth r s f) := by
  have hs : 0 < s := hτ.trans_le hτs
  have ht : 0 < t := hs.trans_le hst
  have hτt : τ ≤ t := hτs.trans hst
  have hprefix := hBr.prefix ht ht1 hB (j := q + r) le_rfl
  intro j hj x
  by_cases hjr : j - q ≤ r
  · have hbr : ∀ y, ‖iteratedFDeriv ℝ (min j q + r) f y‖ ≤ B / t ^ r := fun y => by
      have h := hprefix.deriv_le (by norm_num) (show min j q + r ≤ q + r by omega)
        (Set.mem_univ y)
      simpa only [one_pow, div_one, iteratedFDerivWithin_univ, Nat.add_sub_cancel_left] using h
    have h := finiteSmooth_approximation r (min j q) (j - q) hjr hs hf hfc hbr x
    rw [show min j q + (j - q) = j by omega] at h
    have hp : τ ^ (j - q) * s ^ (r - (j - q)) ≤ s ^ r := by
      calc
        _ ≤ s ^ (j - q) * s ^ (r - (j - q)) := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hτ.le hτs _) (pow_nonneg hs.le _)
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjr]
    calc
      _ ≤ τ ^ (j - q) * (approximationConstant r (j - q) *
          s ^ (r - (j - q)) * (B / t ^ r)) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hτ.le _)
      _ = (approximationConstant r (j - q) * B / t ^ r) *
          (τ ^ (j - q) * s ^ (r - (j - q))) := by ring
      _ ≤ (approximationConstant r (j - q) * B / t ^ r) * s ^ r :=
        mul_le_mul_of_nonneg_left hp (div_nonneg
          (mul_nonneg (approximationConstant_nonneg _ _) hB) (pow_nonneg ht.le _))
      _ = approximationConstant r (j - q) * (B * (s / t) ^ r) := by rw [div_pow]; ring
      _ ≤ tailConstant r * (B * (s / t) ^ r) :=
        mul_le_mul_of_nonneg_right (approximationConstant_le_tail hjr) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (tailConstant_nonneg r)
  · have hbc := fun y => hCm.deriv_le ht hj y
    have h := iterated_residual_bounded hs r j hf hfc hbc x
    rw [error_finiteSmooth]
    have hp : (τ / t) ^ (j - q) ≤ (τ / t) ^ r :=
      pow_le_pow_of_le_one (by positivity) ((div_le_one ht).mpr hτt) (by omega)
    calc
      _ ≤ τ ^ (j - q) * ((1 + ∫ y, ‖kernel 0 y‖) ^ r * (C / t ^ (j - q))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hτ.le _)
      _ = (1 + ∫ y, ‖kernel 0 y‖) ^ r * C * (τ / t) ^ (j - q) := by rw [div_pow]; ring
      _ ≤ (1 + ∫ y, ‖kernel 0 y‖) ^ r * C * (τ / t) ^ r :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ tailConstant r * (C * (τ / t) ^ r) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (residualConstant_le_tail r) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity))
        (tailConstant_nonneg r)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
