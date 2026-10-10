import OAI.MathematicalPhysics.DefocusingNLS.Linear.SemigroupSymmetryFrame
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphFrameBounds

namespace OAI

/-! The real stable-graph blocks obtained from the actual complex contour projection. -/

open scoped NNReal
namespace DefocusingNLS
variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem projectionFrame_stableProjection (P : V →L[ℂ] V) (e : F ≃L[ℂ] P.range) :
    stableFrameProjection ((projectionFrame P e).restrictScalars ℝ)
      ((projectionCoordinates P e).restrictScalars ℝ)=(1-P).restrictScalars ℝ := by
  ext v
  change v-projectionFrame P e (projectionCoordinates P e v)=v-P v
  rw [projectionFrame_coordinates]

theorem semigroup_stableProjectedBlock_bound
    (S : ℝ≥0 → V →L[ℂ] V) (P : V →L[ℂ] V) (hP : IsIdempotentElem P)
    (hcomm : ∀ t, Commute (S t) P) (e : F ≃L[ℂ] P.range)
    (D δ : ℝ) (hD : 0≤D)
    (hdecay : ∀ t : ℝ≥0, ∀ v, P v=0 → ‖S t v‖ ≤ D*Real.exp (-δ*(t : ℝ))*‖v‖)
    (t : ℝ≥0) :
    ‖stableProjectedBlock ((projectionFrame P e).restrictScalars ℝ)
      ((projectionFrame P e).restrictScalars ℝ)
      ((projectionCoordinates P e).restrictScalars ℝ)
      ((projectionCoordinates P e).restrictScalars ℝ) ((S t).restrictScalars ℝ)‖ ≤
      (D*Real.exp (-δ*(t : ℝ)))*‖(1-P).restrictScalars ℝ‖ := by
  apply stableProjectedBlock_norm_le _ _ _ _ _ _ _ (by positivity) (norm_nonneg _)
  · exact projectionCoordinates_frame P hP e
  · rw [projectionFrame_stableProjection]
  · intro v hv
    have hPv := (projectionCoordinates_zero_iff P e v).mp hv
    have hPS : P (S t v)=0 := by
      have hh := congrArg (fun L : V →L[ℂ] V => L v) (hcomm t).eq
      change S t (P v)=P (S t v) at hh
      rw [hPv,map_zero] at hh
      exact hh.symm
    rw [projectionFrame_stableProjection]
    change ‖S t v-P (S t v)‖ ≤ _
    rw [hPS,sub_zero]
    exact hdecay t v hPv

theorem semigroup_stableMixedBlock_zero
    (S : ℝ≥0 → V →L[ℂ] V) (P : V →L[ℂ] V) (hP : IsIdempotentElem P)
    (hcomm : ∀ t, Commute (S t) P) (e : F ≃L[ℂ] P.range) (t : ℝ≥0) :
    stableMixedBlock ((projectionFrame P e).restrictScalars ℝ)
      ((projectionFrame P e).restrictScalars ℝ)
      ((projectionCoordinates P e).restrictScalars ℝ) ((S t).restrictScalars ℝ)=0 := by
  rw [stableMixedBlock,projectionFrame_stableProjection]
  ext v
  change S t (projectionFrame P e v)-P (S t (projectionFrame P e v))=0
  have hpv : P (projectionFrame P e v)=projectionFrame P e v :=
    idempotent_range_fixed P hP (e v)
  have hh := congrArg (fun L : V →L[ℂ] V => L (projectionFrame P e v)) (hcomm t).eq
  change S t (P (projectionFrame P e v))=P (S t (projectionFrame P e v)) at hh
  rw [hpv] at hh
  exact sub_eq_zero.mpr hh

end DefocusingNLS

end OAI
