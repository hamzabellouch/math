import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphRecurrence

namespace OAI

/-! # Initial stable coordinates select a Lipschitz graph

This selects the unique small fixed sequence of the contracting recurrence map.
Its zeroth unstable coordinate is Lipschitz in the prescribed stable data.
The torus spectral blocks and endpoint remainder estimates are hypotheses
of this construction.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] in
theorem stableGraphMap_initial_dist_le
    (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (hA : ∀ n, ‖A n‖ ≤ 1 / 8) (hB : ∀ n, ‖B n‖ ≤ 1 / 16)
    (R : F →L[ℝ] F) (hR : ‖R‖ ≤ 1) (w₀ w₁ : E)
    (N : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ E))
    (H : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ F))
    (x : (ℕ →ᵇ E) × (ℕ →ᵇ F)) :
    dist (stableGraphMap A B hA hB R hR w₀ N H x)
      (stableGraphMap A B hA hB R hR w₁ N H x) ≤ dist w₀ w₁ := by
  dsimp only [stableGraphMap]
  rw [Prod.dist_eq]
  apply max_le
  · apply (BoundedContinuousFunction.dist_le (show 0 ≤ dist w₀ w₁ from dist_nonneg)).2
    intro n
    cases n with
    | zero => simp only [stableForward_zero, le_refl]
    | succ n => simp only [stableForward_succ, dist_self]; exact dist_nonneg
  · simp only [dist_self]; exact dist_nonneg

omit [CompleteSpace E] in
theorem stableGraph_fixedPoint_data_dist_le
    (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (hA : ∀ n, ‖A n‖ ≤ 1 / 8) (hB : ∀ n, ‖B n‖ ≤ 1 / 16)
    (R : F →L[ℝ] F) (hR : ‖R‖ ≤ 1) (w₀ w₁ : E)
    (N : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ E))
    (H : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ F))
    (x y : (ℕ →ᵇ E) × (ℕ →ᵇ F))
    (hx : stableGraphMap A B hA hB R hR w₀ N H x = x)
    (hy : stableGraphMap A B hA hB R hR w₁ N H y = y)
    (hN : dist (N x) (N y) ≤ (1 / 16 : ℝ) * dist x y)
    (hH : dist (H x) (H y) ≤ (1 / 16 : ℝ) * dist x y) :
    dist x y ≤ 2 * dist w₀ w₁ := by
  have htri := dist_triangle
    (stableGraphMap A B hA hB R hR w₀ N H x)
    (stableGraphMap A B hA hB R hR w₀ N H y)
    (stableGraphMap A B hA hB R hR w₁ N H y)
  have hfirst := stableGraphMap_dist_le A B hA hB R hR w₀ N H x y hN hH
  have hsecond := stableGraphMap_initial_dist_le A B hA hB R hR w₀ w₁ N H y
  rw [hx, hy] at htri
  rw [hx] at hfirst
  rw [hy] at hsecond
  linarith

theorem exists_stableGraph_selection
    (A : ℕ → E →L[ℝ] E) (B : ℕ → F →L[ℝ] E)
    (hA : ∀ n, ‖A n‖ ≤ 1 / 8) (hB : ∀ n, ‖B n‖ ≤ 1 / 16)
    (R : F →L[ℝ] F) (hR : ‖R‖ ≤ 1)
    (N : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ E))
    (H : ((ℕ →ᵇ E) × (ℕ →ᵇ F)) → (ℕ →ᵇ F))
    (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε)
    (hN : ∀ x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      dist (N x) (N y) ≤ (1 / 16 : ℝ) * dist x y)
    (hH : ∀ x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      dist (H x) (H y) ≤ (1 / 16 : ℝ) * dist x y)
    (hN0 : ‖N 0‖ ≤ ε) (hH0 : ‖H 0‖ ≤ ε) :
    ∃ G : {w : E // ‖w‖ + 2 * ε ≤ ρ / 2} → F,
      LipschitzWith 2 G ∧ ∀ w,
        ‖G w‖ ≤ 2 * (‖w.1‖ + 2 * ε) ∧
        ∃ x : (ℕ →ᵇ E) × (ℕ →ᵇ F),
          stableGraphMap A B hA hB R hR w.1 N H x = x ∧
          x.1 0 = w.1 ∧ x.2 0 = G w ∧ ‖x‖ ≤ ρ ∧
          Filter.Tendsto (stableSequenceValue x.1) Filter.atTop (nhds 0) ∧
          Filter.Tendsto (stableSequenceValue x.2) Filter.atTop (nhds 0) := by
  classical
  choose x hx hfix hbound huniq using fun w : {w : E // ‖w‖ + 2 * ε ≤ ρ / 2} =>
    exists_stableGraph_fixedPoint A B hA hB R hR w.1 N H ρ ε hρ hε hN hH hN0 hH0 w.2
  let G := fun w : {w : E // ‖w‖ + 2 * ε ≤ ρ / 2} => (x w).2 0
  refine ⟨G, LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro w v
    have hd := stableGraph_fixedPoint_data_dist_le A B hA hB R hR w.1 v.1 N H
      (x w) (x v) (hfix w) (hfix v) (hN _ _ (hx w) (hx v)) (hH _ _ (hx w) (hx v))
    have he : dist (G w) (G v) ≤ dist (x w) (x v) :=
      (BoundedContinuousFunction.dist_coe_le_dist (f := (x w).2) (g := (x v).2) 0).trans (le_max_right _ _)
    exact he.trans hd
  · intro w
    have hG : ‖G w‖ ≤ ‖x w‖ := ((x w).2.norm_coe_le_norm 0).trans (norm_snd_le _)
    refine ⟨hG.trans (hbound w), x w, hfix w, ?_, rfl, hx w,
      stableSequenceValue_tendsto_zero _, stableSequenceValue_tendsto_zero _⟩
    have he := congrArg (fun y : (ℕ →ᵇ E) × (ℕ →ᵇ F) => y.1 0) (hfix w)
    exact he.symm

end DefocusingNLS

end OAI
