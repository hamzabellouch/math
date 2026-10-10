import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ParameterOpenness
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphReconstruction

namespace OAI

/-! # The finite-dimensional zero placing physical data on a stable graph -/

open Metric

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem stableGraph_parameter_zero
    (C : F ≃L[ℝ] F) (r M ε B : ℝ) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (f g : closedBall (0 : F) r → E)
    (π : closedBall (0 : F) r → E →L[ℝ] F)
    (ζ : closedBall (0 : F) r → F →L[ℝ] E)
    (hf : Continuous f) (hg : Continuous g)
    (hπ : Continuous (fun q : closedBall (0 : F) r × E => π q.1 q.2))
    (hπζ : ∀ p v, π p (ζ p v) = v)
    (hπbound : ∀ p, ‖π p‖ ≤ M)
    (herror : ∀ p, ‖f p - ζ p (C p.1)‖ ≤ ε)
    (hgbound : ∀ p, ‖g p‖ ≤ B)
    (hstable : ∀ p, stableFrameProjection (ζ p) (π p) (g p) =
      stableFrameProjection (ζ p) (π p) (f p))
    (hsmall : ‖C.symm.toContinuousLinearMap‖ * M * (ε + B) ≤ r) :
    ∃ p, f p = g p := by
  let Φ := fun p => π p (f p - g p)
  have hc : Continuous Φ := hπ.comp (continuous_id.prodMk (hf.sub hg))
  have he (p : closedBall (0 : F) r) :
      ‖C.symm (Φ p) - p.1‖ ≤ ‖C.symm.toContinuousLinearMap‖ * M * (ε + B) := by
    have hlin : Φ p - C p.1 = π p ((f p - ζ p (C p.1)) - g p) := by
      simp only [Φ, map_sub, hπζ]
      abel
    calc
      _ = ‖C.symm (Φ p - C p.1)‖ := by
        rw [map_sub, C.symm_apply_apply]
      _ ≤ ‖C.symm.toContinuousLinearMap‖ * ‖Φ p - C p.1‖ :=
        C.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖C.symm.toContinuousLinearMap‖ * (M * (ε + B)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [hlin]
        apply ((π p).le_opNorm _).trans
        apply (mul_le_mul_of_nonneg_right (hπbound p) (norm_nonneg _)).trans
        exact mul_le_mul_of_nonneg_left
          ((norm_sub_le _ _).trans (add_le_add (herror p) (hgbound p))) hM
      _ = _ := by ring
  obtain ⟨p, hp⟩ := zero_of_near_invertible_linear_map C r
    (‖C.symm.toContinuousLinearMap‖ * M * (ε + B)) hr hsmall Φ hc he
  have hcoord : π p (f p) = π p (g p) := by
    have hh : π p (f p) - π p (g p) = 0 := by simpa only [Φ, map_sub] using hp
    exact sub_eq_zero.mp hh
  refine ⟨p, ?_⟩
  calc
    f p = stableFrameProjection (ζ p) (π p) (f p) + ζ p (π p (f p)) :=
      (stableFrameProjection_decomposition _ _ _).symm
    _ = stableFrameProjection (ζ p) (π p) (g p) + ζ p (π p (g p)) := by
      rw [hstable p, hcoord]
    _ = g p := stableFrameProjection_decomposition _ _ _

end DefocusingNLS

end OAI
