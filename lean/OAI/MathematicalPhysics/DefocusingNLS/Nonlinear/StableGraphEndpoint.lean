import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphProjectedRecurrence

namespace OAI

/-! # From the graph contraction to the original endpoint sequence

The source identities below are the exact projected nonlinear remainder and
coordinate defect. They permit the abstract contraction to reconstruct the
original endpoint dynamics, with a prescribed stable initial coordinate.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_stableGraph_endpoint_sequence
    (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F)
    (A : ℕ → E →L[ℝ] E) (D R : F →L[ℝ] F)
    (hR : ‖R‖ ≤ 1) (hinv : ∀ z, D (R z) = z)
    (hπζ : ∀ n v, π n (ζ n v) = v)
    (hA : ∀ n, ‖stableProjectedBlock (ζ n) (ζ (n + 1))
      (π n) (π (n + 1)) (A n)‖ ≤ 1 / 8)
    (hB : ∀ n, ‖stableMixedBlock (ζ n) (ζ (n + 1)) (π (n + 1)) (A n)‖ ≤ 1 / 16)
    (h : ℕ → E → E) (w₀ : E) (hw₀ : π 0 w₀ = 0)
    (N : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ E))
    (H : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ F))
    (ρ ε C : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hζ : ∀ n, ‖ζ n‖ ≤ C)
    (hN : ∀ x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      dist (N x) (N y) ≤ (1 / 16 : ℝ) * dist x y)
    (hH : ∀ x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      dist (H x) (H y) ≤ (1 / 16 : ℝ) * dist x y)
    (hN0 : ‖N 0‖ ≤ ε) (hH0 : ‖H 0‖ ≤ ε)
    (hsmall : ‖w₀‖ + 2 * ε ≤ ρ / 2)
    (hNs : ∀ x, ‖x‖ ≤ ρ → ∀ n, stableSequenceValue (N x) n =
      stableFrameProjection (ζ (n + 1)) (π (n + 1))
        (h n (stableFrameState ζ (stableSequenceValue x.1) (stableSequenceValue x.2) n)))
    (hHs : ∀ x, ‖x‖ ≤ ρ → ∀ n, stableSequenceValue (H x) n =
      ((π (n + 1)).comp (A n) - D.comp (π n))
          (stableFrameState ζ (stableSequenceValue x.1) (stableSequenceValue x.2) n) +
        π (n + 1)
          (h n (stableFrameState ζ (stableSequenceValue x.1) (stableSequenceValue x.2) n))) :
    ∃ z : ℕ → E,
      stableFrameProjection (ζ 0) (π 0) (z 0) = w₀ ∧
      (∀ n, z (n + 1) = A n (z n) + h n (z n)) ∧
      (∀ n, ‖z n‖ ≤ (2 * (‖w₀‖ + 2 * ε) * (1 + C)) * (1 / 2 : ℝ) ^ n) := by
  let A' := fun n => stableProjectedBlock (ζ n) (ζ (n + 1)) (π n) (π (n + 1)) (A n)
  let B' := fun n => stableMixedBlock (ζ n) (ζ (n + 1)) (π (n + 1)) (A n)
  obtain ⟨x, hx, hfix, hbound, _⟩ := exists_stableGraph_fixedPoint
    A' B' hA hB R hR w₀ N H ρ ε hρ hε hN hH hN0 hH0 hsmall
  have hforward : stableForward A' B' (1 / 8) (1 / 16) (by norm_num) (by norm_num)
      hA hB w₀ x.1 x.2 (N x) = x.1 := congrArg Prod.fst hfix
  have hback : stableBackward R hR (H x) = x.2 := congrArg Prod.snd hfix
  have hwinit : stableSequenceValue x.1 0 = w₀ := by
    rw [stableSequenceValue_zero, ← hforward, stableForward_zero]
  have hw (n : ℕ) : stableSequenceValue x.1 (n + 1) =
      stableProjectedBlock (ζ n) (ζ (n + 1)) (π n) (π (n + 1)) (A n)
          (stableSequenceValue x.1 n) +
        stableMixedBlock (ζ n) (ζ (n + 1)) (π (n + 1)) (A n)
          (stableSequenceValue x.2 n) +
        stableFrameProjection (ζ (n + 1)) (π (n + 1))
          (h n (stableFrameState ζ (stableSequenceValue x.1) (stableSequenceValue x.2) n)) := by
    simpa only [A', B', hNs x hx n] using stableForward_unweighted_recurrence
      A' B' (1 / 8) (1 / 16) (by norm_num) (by norm_num) hA hB
      w₀ x.1 x.2 (N x) hforward n
  have hu (n : ℕ) : stableSequenceValue x.2 (n + 1) =
      D (stableSequenceValue x.2 n) +
        ((π (n + 1)).comp (A n) - D.comp (π n))
          (stableFrameState ζ (stableSequenceValue x.1) (stableSequenceValue x.2) n) +
        π (n + 1)
          (h n (stableFrameState ζ (stableSequenceValue x.1) (stableSequenceValue x.2) n)) := by
    have hh := stableBackward_unweighted_recurrence R D hR hinv (H x) n
    rw [hback, hHs x hx n] at hh
    simpa only [add_assoc] using hh
  have hk₀ : π 0 (stableSequenceValue x.1 0) = 0 := by rw [hwinit]; exact hw₀
  obtain ⟨hker, hrec⟩ := stableProjected_reconstruct_recurrence ζ π A D h
    (stableSequenceValue x.1) (stableSequenceValue x.2) hπζ hk₀ hw hu
  refine ⟨stableFrameState ζ (stableSequenceValue x.1) (stableSequenceValue x.2), ?_, hrec, ?_⟩
  · change (stableSequenceValue x.1 0 + ζ 0 (stableSequenceValue x.2 0)) -
      ζ 0 (π 0 (stableSequenceValue x.1 0 + ζ 0 (stableSequenceValue x.2 0))) = w₀
    rw [map_add, hker 0, hπζ 0, zero_add, add_sub_cancel_right, hwinit]
  · intro n
    have hx₁ : ‖x.1‖ ≤ 2 * (‖w₀‖ + 2 * ε) := (norm_fst_le x).trans hbound
    have hx₂ : ‖x.2‖ ≤ 2 * (‖w₀‖ + 2 * ε) := (norm_snd_le x).trans hbound
    apply (stableFrameState_weighted_norm_le ζ x.1 x.2 C hζ n).trans
    calc
      _ ≤ (1 / 2 : ℝ) ^ n *
          (2 * (‖w₀‖ + 2 * ε) + C * (2 * (‖w₀‖ + 2 * ε))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hx₁ (mul_le_mul_of_nonneg_left hx₂ hC)) (by positivity)
      _ = _ := by ring

end DefocusingNLS

end OAI
