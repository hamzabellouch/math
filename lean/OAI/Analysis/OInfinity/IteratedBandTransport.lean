import OAI.Analysis.OInfinity.CocycleCancellation

namespace OAI

/-! # Actual endomorphism iterates on cyclic tower bands

Transport through a finite iterate costs the two endpoint tower errors.
The adjacent-depth row identity is exact. In particular, mixed-depth
orthogonality involves the inner letter of a two-letter word; it cannot
be replaced by the same-depth outer-letter condition.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma binaryRowIterate_mul (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (x y : E) :
    finiteRowShiftIterate s n (x * y) =
      finiteRowShiftIterate s n x * finiteRowShiftIterate s n y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [finiteRowShiftIterate, ih, finiteRowShift_mul s hs]; rfl

lemma binaryRowIterate_sub_norm_le (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (x y : E) :
    ‖finiteRowShiftIterate s n x - finiteRowShiftIterate s n y‖ ≤ ‖x - y‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      exact (finiteCuntzTransfer_sub_norm_le s s hs hs _ _).trans ih

lemma binaryRowIterate_norm_le (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (x : E) : ‖finiteRowShiftIterate s n x‖ ≤ ‖x‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (finiteCuntzTransfer_norm_le s s hs hs _).trans ih

/-- The concrete intertwining relation between adjacent endomorphism depths. -/
lemma binaryRowIterate_adjacent (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (x : E) (i : Fin 2) :
    finiteRowShiftIterate s (n + 1) x * finiteRowShiftIterate s n (s i) =
      finiteRowShiftIterate s n (s i * x) := by
  induction n with
  | zero => exact finiteRowShift_mul_row 1 s hs x (mul_one x) i
  | succ n ih =>
      change finiteRowShift s (finiteRowShiftIterate s (n + 1) x) *
        finiteRowShift s (finiteRowShiftIterate s n (s i)) =
          finiteRowShift s (finiteRowShiftIterate s n (s i * x))
      rw [← finiteRowShift_mul s hs, ih]

private lemma binaryRow_adjoint_left (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (x : E) (i : Fin 2) : star (s i) * finiteRowShift s x = x * star (s i) := by
  have h := congrArg star (finiteRowShift_mul_row 1 s hs (star x) (mul_one _) i)
  simpa only [star_mul, finiteRowShift_star, star_star] using h

/-- At neighboring depths the final letter, rather than the first
letter, determines orthogonality. -/
lemma binaryRowIterate_mixed_gram (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (i r l : Fin 2) :
    star (finiteRowShiftIterate s n (s i * s r)) *
        finiteRowShiftIterate s (n + 1) (s l) =
      if r = l then finiteRowShiftIterate s n (star (s i)) else 0 := by
  induction n with
  | zero =>
      change star (s i * s r) * finiteRowShift s (s l) = _
      rw [star_mul, mul_assoc, binaryRow_adjoint_left s hs, ← mul_assoc, hs]
      split_ifs <;> simp only [one_mul, zero_mul, finiteRowShiftIterate]
  | succ n ih =>
      change star (finiteRowShift s (finiteRowShiftIterate s n (s i * s r))) *
        finiteRowShift s (finiteRowShiftIterate s (n + 1) (s l)) = _
      rw [finiteRowShift_star, ← finiteRowShift_mul s hs, ih]
      split_ifs with h
      · rfl
      · exact map_zero (finiteCuntzDiagonalHom s hs)

/-- An iterate of a degree-d coefficient still transports by d; the
additional error is exactly the two endpoint tower errors. -/
lemma binaryRowIterate_band_transport {N : ℕ} (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (η : ℝ) (hη : 0 ≤ η)
    (hshift : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η)
    (x : E) (d : ZMod N) (δ : ℝ)
    (hx : ∀ j, ‖x * e j - e (j + d) * x‖ ≤ δ)
    (n : ℕ) (j : ZMod N) :
    ‖finiteRowShiftIterate s n x * e j -
        e (j + d) * finiteRowShiftIterate s n x‖ ≤
      δ + 2 * (n : ℝ) * η * ‖x‖ := by
  let y := finiteRowShiftIterate s n x
  let a := finiteRowShiftIterate s n (e (j - (n : ZMod N)))
  let b := finiteRowShiftIterate s n (e (j - (n : ZMod N) + d))
  have ha : ‖a - e j‖ ≤ (n : ℝ) * η := by
    simpa only [a, sub_add_cancel] using
      finiteRowShiftIterate_cyclic_error s hs e η hshift (j - (n : ZMod N)) n
  have hb : ‖b - e (j + d)‖ ≤ (n : ℝ) * η := by
    have hi : (j - (n : ZMod N) + d) + (n : ZMod N) = j + d := by abel
    simpa only [b, hi] using
      finiteRowShiftIterate_cyclic_error s hs e η hshift (j - (n : ZMod N) + d) n
  have hm : ‖y * a - b * y‖ ≤ δ := by
    have h := binaryRowIterate_sub_norm_le s hs n
      (x * e (j - (n : ZMod N))) (e (j - (n : ZMod N) + d) * x)
    rw [binaryRowIterate_mul s hs, binaryRowIterate_mul s hs] at h
    exact h.trans (hx _)
  have hyn : ‖y‖ ≤ ‖x‖ := binaryRowIterate_norm_le s hs n x
  have hr : 0 ≤ (n : ℝ) * η := mul_nonneg (Nat.cast_nonneg n) hη
  have heq : y * e j - e (j + d) * y =
      y * (e j - a) + (y * a - b * y) + (b - e (j + d)) * y := by noncomm_ring
  change ‖y * e j - e (j + d) * y‖ ≤ _
  rw [heq]
  calc
    _ ≤ (‖y * (e j - a)‖ + ‖y * a - b * y‖) + ‖(b - e (j + d)) * y‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖x‖ * ((n : ℝ) * η) + δ + ((n : ℝ) * η) * ‖x‖ := by
      apply add_le_add
      · apply add_le_add _ hm
        apply (norm_mul_le _ _).trans
        exact mul_le_mul hyn (by simpa only [norm_sub_rev] using ha) (norm_nonneg _) (norm_nonneg x)
      · apply (norm_mul_le _ _).trans
        exact mul_le_mul hb hyn (norm_nonneg _) hr
    _ = _ := by ring

end WeakPureInfiniteness

end

end OAI
