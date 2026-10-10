import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphContraction

namespace OAI

/-! # The fixed sequence solves the original two recurrences

The backward sum telescopes in the neutral coordinate as well as in the
strictly expanding coordinates.  Removing the `2^n` weights recovers the
forward and unstable-coordinate equations and gives actual endpoint decay.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem stableBackward_recurrence (R : F →L[ℝ] F) (hR : ‖R‖ ≤ 1)
    (f : ℕ →ᵇ F) (n : ℕ) :
    stableBackward R hR f n = R ((1 / 2 : ℝ) • stableBackward R hR f (n + 1) - f n) := by
  let t := fun n j : ℕ => (1 / 2 : ℝ) ^ j • (R ^ (j + 1)) (f (n + j))
  have hterm (j : ℕ) : t n (j + 1) = (1 / 2 : ℝ) • R (t (n + 1) j) := by
    dsimp [t]
    rw [pow_succ' R (j + 1), pow_succ]
    simp only [mul_apply_eq_comp, map_smul, smul_smul]
    rw [mul_comm ((1 / 2 : ℝ) ^ j) (1 / 2)]
    simp only [Nat.add_left_comm, Nat.add_comm]
  have hshift : (∑' j : ℕ, t n (j + 1)) =
      (1 / 2 : ℝ) • R (∑' j : ℕ, t (n + 1) j) := by
    rw [R.map_tsum (stableBackward_summable R hR f (n + 1)), ← tsum_const_smul'']
    exact tsum_congr hterm
  have hs := (stableBackward_summable R hR f n).tsum_eq_zero_add
  change (∑' j : ℕ, t n j) = t n 0 + ∑' j : ℕ, t n (j + 1) at hs
  rw [hshift] at hs
  have ht0 : t n 0 = R (f n) := by simp [t]
  rw [ht0] at hs
  change -(∑' j : ℕ, t n j) = R ((1 / 2 : ℝ) • -(∑' j : ℕ, t (n + 1) j) - f n)
  rw [hs]
  simp only [map_sub, map_smul, map_neg, smul_neg]
  abel

theorem stableBackward_unweighted_recurrence
    (R D : F →L[ℝ] F) (hR : ‖R‖ ≤ 1)
    (hinv : ∀ z : F, D (R z) = z) (f : ℕ →ᵇ F) (n : ℕ) :
    stableSequenceValue (stableBackward R hR f) (n + 1) =
      D (stableSequenceValue (stableBackward R hR f) n) + stableSequenceValue f n := by
  have h := congrArg D (stableBackward_recurrence R hR f n)
  rw [hinv] at h
  have hu : (1 / 2 : ℝ) • stableBackward R hR f (n + 1) =
      D (stableBackward R hR f n) + f n := by rw [h]; abel
  rw [stableSequenceValue_succ, hu]
  simp only [stableSequenceValue, map_smul, smul_add]

omit [CompleteSpace E] [CompleteSpace F] in
theorem stableForward_unweighted_recurrence
    (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ n, ‖A n‖ ≤ a) (hB : ∀ n, ‖B n‖ ≤ b)
    (w₀ : E) (w : ℕ →ᵇ E) (u : ℕ →ᵇ F) (r : ℕ →ᵇ E)
    (hfix : stableForward A B a b ha hb hA hB w₀ w u r = w) (n : ℕ) :
    stableSequenceValue w (n + 1) = A n (stableSequenceValue w n) +
      B n (stableSequenceValue u n) + stableSequenceValue r n := by
  have he := congrArg (fun x : ℕ →ᵇ E => x (n + 1)) hfix
  rw [stableForward_succ] at he
  rw [stableSequenceValue_succ, ← he]
  simp only [smul_smul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), one_smul,
    stableSequenceValue, map_smul, smul_add]

end DefocusingNLS

end OAI
