import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphFrameBounds

namespace OAI

/-! # The projected contraction retains the original endpoint dynamics

Preprojecting the stable block extends its kernel estimate to a bounded
operator on the fixed ambient space.  The fixed forward sequence remains
in the correct kernels, so that extension does not alter its recurrence.
-/

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem stableProjected_forward_identity (ζ₀ ζ₁ : F →L[ℝ] E)
    (π₀ π₁ : E →L[ℝ] F) (A : E →L[ℝ] E) (w h : E) (u : F) :
    stableProjectedBlock ζ₀ ζ₁ π₀ π₁ A w + stableMixedBlock ζ₀ ζ₁ π₁ A u +
        stableFrameProjection ζ₁ π₁ h =
      stableFrameProjection ζ₁ π₁
        (A (stableFrameProjection ζ₀ π₀ w + ζ₀ u) + h) := by
  simp only [stableProjectedBlock, stableMixedBlock, ContinuousLinearMap.comp_apply, map_add]

theorem stableProjected_reconstruct_recurrence
    (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F)
    (A : ℕ → E →L[ℝ] E) (D : F →L[ℝ] F) (h : ℕ → E → E)
    (w : ℕ → E) (u : ℕ → F)
    (hπζ : ∀ n v, π n (ζ n v) = v) (hw₀ : π 0 (w 0) = 0)
    (hw : ∀ n, w (n + 1) =
      stableProjectedBlock (ζ n) (ζ (n + 1)) (π n) (π (n + 1)) (A n) (w n) +
      stableMixedBlock (ζ n) (ζ (n + 1)) (π (n + 1)) (A n) (u n) +
      stableFrameProjection (ζ (n + 1)) (π (n + 1))
        (h n (stableFrameState ζ w u n)))
    (hu : ∀ n, u (n + 1) = D (u n) +
      ((π (n + 1)).comp (A n) - D.comp (π n)) (stableFrameState ζ w u n) +
        π (n + 1) (h n (stableFrameState ζ w u n))) :
    (∀ n, π n (w n) = 0) ∧
      ∀ n, stableFrameState ζ w u (n + 1) =
        A n (stableFrameState ζ w u n) + h n (stableFrameState ζ w u n) := by
  have hprojected (n : ℕ) : w (n + 1) =
      stableFrameProjection (ζ (n + 1)) (π (n + 1))
        (A n (stableFrameProjection (ζ n) (π n) (w n) + ζ n (u n)) +
          h n (stableFrameState ζ w u n)) :=
    (hw n).trans (stableProjected_forward_identity _ _ _ _ _ _ _ _)
  have hker : ∀ n, π n (w n) = 0 := stableFrame_forward_kernel ζ π w
    (fun n => A n (stableFrameProjection (ζ n) (π n) (w n) + ζ n (u n)) +
      h n (stableFrameState ζ w u n)) hπζ hw₀ hprojected
  refine ⟨hker, stableGraph_reconstruct_recurrence ζ π A D h w u hπζ hw₀ ?_ hu⟩
  intro n
  rw [hprojected n, stableFrameProjection_eq_self _ _ _ (hker n)]
  rfl

end DefocusingNLS

end OAI
