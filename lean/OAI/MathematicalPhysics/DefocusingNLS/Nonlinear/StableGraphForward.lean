import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphBackward

namespace OAI

/-! # The forward part of the weighted graph map

In weighted coordinates the stable recurrence has a factor two.  Rescaling
the unstable coordinates by a fixed constant makes the mixed block small.
The resulting estimates use the product sup norm, equivalent to the sum
norm in the manuscript and complete on the same weighted sequences.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem stableForward_term_bound (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ n, ‖A n‖ ≤ a) (hB : ∀ n, ‖B n‖ ≤ b)
    (w : ℕ →ᵇ E) (u : ℕ →ᵇ F) (r : ℕ →ᵇ E) (n : ℕ) :
    ‖(2 : ℝ) • (A n (w n) + B n (u n) + r n)‖ ≤
      2 * (a * ‖w‖ + b * ‖u‖ + ‖r‖) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    ‖A n (w n) + B n (u n) + r n‖ ≤ ‖A n (w n)‖ + ‖B n (u n)‖ + ‖r n‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ a * ‖w‖ + b * ‖u‖ + ‖r‖ := by
      apply add_le_add _ (r.norm_coe_le_norm n)
      apply add_le_add
      · exact ((A n).le_opNorm _).trans
          (mul_le_mul (hA n) (w.norm_coe_le_norm n) (norm_nonneg _) ha)
      · exact ((B n).le_opNorm _).trans
          (mul_le_mul (hB n) (u.norm_coe_le_norm n) (norm_nonneg _) hb)

noncomputable def stableForward (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ n, ‖A n‖ ≤ a) (hB : ∀ n, ‖B n‖ ≤ b)
    (w₀ : E) (w : ℕ →ᵇ E) (u : ℕ →ᵇ F) (r : ℕ →ᵇ E) : ℕ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => match n with
      | 0 => w₀
      | j + 1 => (2 : ℝ) • (A j (w j) + B j (u j) + r j))
    (max ‖w₀‖ (2 * (a * ‖w‖ + b * ‖u‖ + ‖r‖)))
    (fun n => by
      cases n with
      | zero => exact le_max_left _ _
      | succ j =>
          exact (stableForward_term_bound A B a b ha hb hA hB w u r j).trans (le_max_right _ _))

@[simp] theorem stableForward_zero (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ n, ‖A n‖ ≤ a) (hB : ∀ n, ‖B n‖ ≤ b)
    (w₀ : E) (w : ℕ →ᵇ E) (u : ℕ →ᵇ F) (r : ℕ →ᵇ E) :
    stableForward A B a b ha hb hA hB w₀ w u r 0 = w₀ := rfl

@[simp] theorem stableForward_succ (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ n, ‖A n‖ ≤ a) (hB : ∀ n, ‖B n‖ ≤ b)
    (w₀ : E) (w : ℕ →ᵇ E) (u : ℕ →ᵇ F) (r : ℕ →ᵇ E) (n : ℕ) :
    stableForward A B a b ha hb hA hB w₀ w u r (n + 1) =
      (2 : ℝ) • (A n (w n) + B n (u n) + r n) := rfl

theorem stableForward_norm_le (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ n, ‖A n‖ ≤ a) (hB : ∀ n, ‖B n‖ ≤ b)
    (w₀ : E) (w : ℕ →ᵇ E) (u : ℕ →ᵇ F) (r : ℕ →ᵇ E) :
    ‖stableForward A B a b ha hb hA hB w₀ w u r‖ ≤
      max ‖w₀‖ (2 * (a * ‖w‖ + b * ‖u‖ + ‖r‖)) := by
  apply (BoundedContinuousFunction.norm_le (le_max_of_le_left (norm_nonneg _))).2
  intro n
  cases n with
  | zero => exact le_max_left _ _
  | succ j =>
      exact (stableForward_term_bound A B a b ha hb hA hB w u r j).trans (le_max_right _ _)

theorem stableForward_sub (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ n, ‖A n‖ ≤ a) (hB : ∀ n, ‖B n‖ ≤ b)
    (w₀ : E) (w w' : ℕ →ᵇ E) (u u' : ℕ →ᵇ F) (r r' : ℕ →ᵇ E) :
    stableForward A B a b ha hb hA hB w₀ w u r -
        stableForward A B a b ha hb hA hB w₀ w' u' r' =
      stableForward A B a b ha hb hA hB 0 (w - w') (u - u') (r - r') := by
  apply BoundedContinuousFunction.ext
  intro n
  cases n with
  | zero => simp only [BoundedContinuousFunction.sub_apply, stableForward_zero, sub_self]
  | succ j =>
      simp only [BoundedContinuousFunction.sub_apply, stableForward_succ, map_sub]
      module

theorem stableForward_dist_le (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ n, ‖A n‖ ≤ a) (hB : ∀ n, ‖B n‖ ≤ b)
    (w₀ : E) (w w' : ℕ →ᵇ E) (u u' : ℕ →ᵇ F) (r r' : ℕ →ᵇ E) :
    dist (stableForward A B a b ha hb hA hB w₀ w u r)
      (stableForward A B a b ha hb hA hB w₀ w' u' r') ≤
        2 * (a * dist w w' + b * dist u u' + dist r r') := by
  simp only [dist_eq_norm, stableForward_sub]
  apply (stableForward_norm_le A B a b ha hb hA hB 0 (w - w') (u - u') (r - r')).trans
  rw [norm_zero, max_eq_right (by positivity)]

end DefocusingNLS

end OAI
