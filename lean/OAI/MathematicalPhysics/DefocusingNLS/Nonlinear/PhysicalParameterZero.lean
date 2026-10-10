import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphCoordinateZero
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalFrame

namespace OAI

/-! # Brouwer selection when physical parameters and retained coordinates use different norms -/

open Metric
namespace DefocusingNLS
local notation "Params" => ProfileSymmetryParameters

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem physical_parameter_zero_of_coordinate_bound
    (C : Params ≃L[ℝ] V) (r ε B : ℝ) (hr : 0 ≤ r)
    (f g : closedBall (0 : Params) r → FourierL2)
    (π : closedBall (0 : Params) r → FourierL2 →L[ℝ] V)
    (ζ : closedBall (0 : Params) r → V →L[ℝ] FourierL2)
    (hf : Continuous f) (hg : Continuous g)
    (hπ : Continuous (fun q : closedBall (0 : Params) r × FourierL2 => π q.1 q.2))
    (herror : ∀ p, ‖π p (f p) - C p.1‖ ≤ ε)
    (hgbound : ∀ p, ‖π p (g p)‖ ≤ B)
    (hstable : ∀ p, stableFrameProjection (ζ p) (π p) (g p) =
      stableFrameProjection (ζ p) (π p) (f p))
    (hsmall : ‖C.symm.toContinuousLinearMap‖ * (ε + B) ≤ r) :
    ∃ p, f p = g p := by
  let Φ := fun p => C.symm (π p (f p - g p))
  have hc : Continuous Φ := C.symm.continuous.comp
    (hπ.comp (continuous_id.prodMk (hf.sub hg)))
  have he (p : closedBall (0 : Params) r) :
      ‖Φ p - p.1‖ ≤ ‖C.symm.toContinuousLinearMap‖ * (ε + B) := by
    calc
      _ = ‖C.symm ((π p (f p) - C p.1) - π p (g p))‖ := by
        simp only [Φ, map_sub, C.symm_apply_apply]
        congr 1
        abel
      _ ≤ ‖C.symm.toContinuousLinearMap‖ * ‖(π p (f p) - C p.1) - π p (g p)‖ :=
        C.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((norm_sub_le _ _).trans (add_le_add (herror p) (hgbound p))) (norm_nonneg _)
  obtain ⟨p, hp⟩ := zero_of_small_continuous_error r
    (‖C.symm.toContinuousLinearMap‖ * (ε + B)) hr hsmall Φ hc he
  have hcoord : π p (f p) = π p (g p) := by
    have hzero : π p (f p - g p) = 0 := by
      have h := congrArg C hp
      simpa only [Φ, C.apply_symm_apply, map_zero] using h
    simpa only [map_sub, sub_eq_zero] using hzero
  refine ⟨p, ?_⟩
  calc
    f p = stableFrameProjection (ζ p) (π p) (f p) + ζ p (π p (f p)) :=
      (stableFrameProjection_decomposition _ _ _).symm
    _ = stableFrameProjection (ζ p) (π p) (g p) + ζ p (π p (g p)) := by
      rw [hstable p, hcoord]
    _ = g p := stableFrameProjection_decomposition _ _ _

end DefocusingNLS

end OAI
