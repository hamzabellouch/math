import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphRecurrence

namespace OAI

/-! # Reconstructing the actual endpoint recurrence from graph coordinates

The frame and coordinate maps are explicit operators.  Their identities
ensure the projected stable recurrence stays in the correct kernel and the
two graph recurrences combine into the original nonlinear endpoint step.
No spectral estimates are assumed by this algebraic supporting lemma.
-/

open Filter Topology
open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def stableFrameProjection (ζ : F →L[ℝ] E) (π : E →L[ℝ] F) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - ζ.comp π

theorem stableFrameProjection_coordinate (ζ : F →L[ℝ] E) (π : E →L[ℝ] F)
    (hπζ : ∀ u, π (ζ u) = u) (x : E) : π (stableFrameProjection ζ π x) = 0 := by
  change π (x - ζ (π x)) = 0
  rw [map_sub, hπζ, sub_self]

theorem stableFrameProjection_decomposition (ζ : F →L[ℝ] E) (π : E →L[ℝ] F) (x : E) :
    stableFrameProjection ζ π x + ζ (π x) = x := sub_add_cancel _ _

noncomputable def stableFrameState (ζ : ℕ → F →L[ℝ] E) (w : ℕ → E) (u : ℕ → F)
    (n : ℕ) : E := w n + ζ n (u n)

theorem stableFrameState_coordinate (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F)
    (w : ℕ → E) (u : ℕ → F) (hπζ : ∀ n v, π n (ζ n v) = v)
    (hw : ∀ n, π n (w n) = 0) (n : ℕ) : π n (stableFrameState ζ w u n) = u n := by
  simp only [stableFrameState, map_add, hw, hπζ, zero_add]

theorem stableFrame_forward_split (ζ : F →L[ℝ] E) (π : E →L[ℝ] F)
    (A : E →L[ℝ] E) (w : E) (u : F) :
    stableFrameProjection ζ π (A (w + ζ u)) =
      (stableFrameProjection ζ π |>.comp A) w +
        ((stableFrameProjection ζ π |>.comp A).comp ζ) u := by
  simp only [map_add, ContinuousLinearMap.comp_apply]

theorem stableFrame_forward_kernel (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F)
    (w : ℕ → E) (y : ℕ → E) (hπζ : ∀ n v, π n (ζ n v) = v)
    (hw₀ : π 0 (w 0) = 0)
    (hw : ∀ n, w (n + 1) = stableFrameProjection (ζ (n + 1)) (π (n + 1)) (y n)) :
    ∀ n, π n (w n) = 0 := by
  intro n
  cases n with
  | zero => exact hw₀
  | succ n =>
      rw [hw n]
      exact stableFrameProjection_coordinate _ _ (hπζ (n + 1)) _

theorem stableGraph_reconstruct_recurrence
    (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F)
    (A : ℕ → E →L[ℝ] E) (D : F →L[ℝ] F) (h : ℕ → E → E)
    (w : ℕ → E) (u : ℕ → F)
    (hπζ : ∀ n v, π n (ζ n v) = v) (hw₀ : π 0 (w 0) = 0)
    (hw : ∀ n, w (n + 1) = stableFrameProjection (ζ (n + 1)) (π (n + 1))
      (A n (stableFrameState ζ w u n) + h n (stableFrameState ζ w u n)))
    (hu : ∀ n, u (n + 1) = D (u n) +
      ((π (n + 1)).comp (A n) - D.comp (π n)) (stableFrameState ζ w u n) +
        π (n + 1) (h n (stableFrameState ζ w u n))) :
    ∀ n, stableFrameState ζ w u (n + 1) =
      A n (stableFrameState ζ w u n) + h n (stableFrameState ζ w u n) := by
  have hker : ∀ n, π n (w n) = 0 :=
    stableFrame_forward_kernel ζ π w
      (fun n => A n (stableFrameState ζ w u n) + h n (stableFrameState ζ w u n)) hπζ hw₀ hw
  have hcoord := stableFrameState_coordinate ζ π w u hπζ hker
  intro n
  have hu' : u (n + 1) = π (n + 1)
      (A n (stableFrameState ζ w u n) + h n (stableFrameState ζ w u n)) := by
    rw [hu n]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, hcoord, map_add]
    abel
  change w (n + 1) + ζ (n + 1) (u (n + 1)) = _
  rw [hw n, hu']
  exact stableFrameProjection_decomposition _ _ _

theorem stableFrameState_norm_le (ζ : ℕ → F →L[ℝ] E) (w : ℕ → E) (u : ℕ → F)
    (C : ℝ) (hC : ∀ n, ‖ζ n‖ ≤ C) (n : ℕ) :
    ‖stableFrameState ζ w u n‖ ≤ ‖w n‖ + C * ‖u n‖ :=
  (norm_add_le _ _).trans (add_le_add le_rfl
    (((ζ n).le_opNorm (u n)).trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))))

theorem stableFrameState_weighted_norm_le (ζ : ℕ → F →L[ℝ] E)
    (w : ℕ →ᵇ E) (u : ℕ →ᵇ F) (C : ℝ) (hC : ∀ n, ‖ζ n‖ ≤ C) (n : ℕ) :
    ‖stableFrameState ζ (stableSequenceValue w) (stableSequenceValue u) n‖ ≤
      (1 / 2 : ℝ) ^ n * (‖w‖ + C * ‖u‖) := by
  have hC0 : 0 ≤ C := (norm_nonneg (ζ 0)).trans (hC 0)
  apply (stableFrameState_norm_le ζ (stableSequenceValue w) (stableSequenceValue u) C hC n).trans
  calc
    _ ≤ (1 / 2 : ℝ) ^ n * ‖w‖ + C * ((1 / 2 : ℝ) ^ n * ‖u‖) :=
      add_le_add (norm_stableSequenceValue_le w n)
        (mul_le_mul_of_nonneg_left (norm_stableSequenceValue_le u n) hC0)
    _ = _ := by ring

theorem stableFrameState_weighted_tendsto_zero (ζ : ℕ → F →L[ℝ] E)
    (w : ℕ →ᵇ E) (u : ℕ →ᵇ F) (C : ℝ) (hC : ∀ n, ‖ζ n‖ ≤ C) :
    Tendsto (stableFrameState ζ (stableSequenceValue w) (stableSequenceValue u)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (stableFrameState_weighted_norm_le ζ w u C hC)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (‖w‖ + C * ‖u‖)

end DefocusingNLS

end OAI
