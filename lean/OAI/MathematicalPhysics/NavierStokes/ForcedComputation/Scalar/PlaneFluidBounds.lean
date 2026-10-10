import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarComparison

namespace OAI

/-! Finite-time velocity and gradient bounds required by the whole-plane
comparison class. Compact support is needed only for the prescribed drift. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter
open scoped ContDiff Topology

theorem CompactPlaneCoefficients.drift_derivative_bound {a : ℝ → Plane → Plane}
    {h : ℝ → Plane → ℝ} (hc : CompactPlaneCoefficients a h)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (a t) x‖ ≤ B := by
  have hs : ContDiff ℝ ∞ (fun y : ℝ × Plane => fderiv ℝ (a y.1) y.2) := by
    have hp : ContDiff ℝ ∞
        (Function.uncurry (fun y : ℝ × Plane => fun x : Plane => a y.1 x)) :=
      ha.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact hp.fderiv contDiff_snd (by simp)
  obtain ⟨K, hK, hz⟩ := hc T hT
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).bddAbove_image hs.continuous.norm.continuousOn
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · exact (hB ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_right _ _)
  · have he : a t =ᶠ[𝓝 x] fun _ => (0 : Plane) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact (hz t ht y hy).1
    rw [he.fderiv_eq]
    simpa only [fderiv_fun_const, Pi.zero_apply, norm_zero] using (le_max_left (0 : ℝ) B)

theorem triangularLift_norm_bound {a : Plane → Plane} {w : Plane → ℝ}
    {A B : ℝ} (ha : ∀ x, ‖a x‖ ≤ A) (hw : ∀ x, |w x| ≤ B) (x : Space) :
    ‖triangularLift a w x‖ ≤ ‖planeInclusion‖ * A + B * ‖basis 2‖ := by
  unfold triangularLift
  calc
    _ ≤ ‖planeInclusion (a (horizontalLinear x))‖ + ‖w (horizontalLinear x) • basis 2‖ := norm_add_le _ _
    _ ≤ ‖planeInclusion‖ * A + B * ‖basis 2‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add
        ((planeInclusion.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (ha _) (norm_nonneg _)))
        (mul_le_mul_of_nonneg_right (hw _) (norm_nonneg _))

theorem triangularLift_fderiv_norm_bound {a : Plane → Plane} {w : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hda : ∀ x, ‖fderiv ℝ a x‖ ≤ A) (hdw : ∀ x, ‖fderiv ℝ w x‖ ≤ B) (x : Space) :
    ‖fderiv ℝ (triangularLift a w) x‖ ≤
      (‖planeInclusion‖ * A + B * ‖basis 2‖) * ‖horizontalLinear‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [triangularLift_fderiv ha hw]
  have hav : ‖fderiv ℝ a (horizontalLinear x) (horizontalLinear v)‖ ≤
      A * (‖horizontalLinear‖ * ‖v‖) := by
    apply ((fderiv ℝ a (horizontalLinear x)).le_opNorm _).trans
    exact mul_le_mul (hda _) (horizontalLinear.le_opNorm _) (norm_nonneg _) hA
  have hwv : ‖fderiv ℝ w (horizontalLinear x) (horizontalLinear v)‖ ≤
      B * (‖horizontalLinear‖ * ‖v‖) := by
    apply ((fderiv ℝ w (horizontalLinear x)).le_opNorm _).trans
    exact mul_le_mul (hdw _) (horizontalLinear.le_opNorm _) (norm_nonneg _) hB
  calc
    _ ≤ ‖planeInclusion (fderiv ℝ a (horizontalLinear x) (horizontalLinear v))‖ +
        ‖fderiv ℝ w (horizontalLinear x) (horizontalLinear v) • basis 2‖ := norm_add_le _ _
    _ ≤ ‖planeInclusion‖ * (A * (‖horizontalLinear‖ * ‖v‖)) +
        (B * (‖horizontalLinear‖ * ‖v‖)) * ‖basis 2‖ := by
      rw [norm_smul]
      exact add_le_add
        ((planeInclusion.le_opNorm _).trans (mul_le_mul_of_nonneg_left hav (norm_nonneg _)))
        (mul_le_mul_of_nonneg_right hwv (norm_nonneg _))
    _ = _ := by ring

theorem PlaneScalarSolution.velocity_gradient_bound {T ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 ≤ T)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (hc : CompactPlaneCoefficients a h) :
    ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ x,
      ‖triangularVelocity a w (t,x)‖ +
        ‖fderiv ℝ (fun y => triangularVelocity a w (t,y)) x‖ ≤ B := by
  obtain ⟨A, hA, hab⟩ := hc.drift_bound ha T hT
  obtain ⟨D, hD, hdb⟩ := hc.drift_derivative_bound ha T hT
  obtain ⟨C, hC⟩ := hw.bounded
  let B := max 0 C
  have hB : 0 ≤ B := le_max_left _ _
  refine ⟨‖planeInclusion‖ * A + B * ‖basis 2‖ +
    (‖planeInclusion‖ * D + B * ‖basis 2‖) * ‖horizontalLinear‖, ?_⟩
  intro t ht x
  apply add_le_add
  · exact triangularLift_norm_bound (hab t ht)
      (fun y => (hC t ht y).1.trans (le_max_right _ _)) x
  · exact triangularLift_fderiv_norm_bound
      (ha.comp (contDiff_const.prodMk contDiff_id)) (hw.slice_smooth ht) hD hB (hdb t ht)
      (fun y => (hC t ht y).2.trans (le_max_right _ _)) x

end ForcedComputation.VelocityDetector

end

end OAI
