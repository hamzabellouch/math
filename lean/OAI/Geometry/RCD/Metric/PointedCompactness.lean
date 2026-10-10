import OAI.Geometry.RCD.Metric.RescalingLimitApproximation

namespace OAI

/-! # Pointed precompactness of RCD rescalings

Uniform finite nets, a countable distance-matrix limit, and metric
completion supply the precise pointed compactness input. The only tail
restriction makes the rescaled curvature at least minus one.
-/

open Set Metric Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The pointed rescaling compactness premise follows from the actual CD
condition and completeness in the manuscript's dimension range. -/
theorem NoncollapsedRCD.pointedRescalingPrecompactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) :
    PointedRescalingPrecompactness p := by
  intro r hr hrzero
  have hcurvzero : Tendsto (fun i => K*(r i)^2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)] using
      hrzero.pow 2 |>.const_mul K
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hcurvzero.eventually (lt_mem_nhds (by norm_num : (-1:ℝ) < 0)))
  let r' (i : ℕ) := r (i+N)
  have hr' (i : ℕ) : 0 < r' i := hr (i+N)
  have hc (i : ℕ) : -1 ≤ K*(r' i)^2 := (hN (i+N) (by omega)).le
  obtain ⟨s⟩ := hX.rescalingNetFamily hn p r' hr' hc
  obtain ⟨phi, hphi, d, hconv⟩ := s.exists_limit hr'
  let := d
  let Y0 := UniformSpace.Completion s.Index
  let : ProperSpace Y0 := s.completion_proper phi hr' hconv
  let Y := ULift.{u} Y0
  let e : Y0 ≃ᵢ Y := {
    toEquiv := Equiv.ulift.symm
    isometry_toFun := isometry_iff_dist_eq.mpr (fun _ _ => rfl) }
  have hproper : ProperSpace Y := by
    refine ⟨fun z R => ?_⟩
    have hball : closedBall z R = e '' closedBall (e.symm z) R := by
      ext w
      constructor
      · intro hw
        refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
        simpa only [mem_closedBall, e.symm.dist_eq] using hw
      · rintro ⟨w, hw, rfl⟩
        simpa only [mem_closedBall, ← e.dist_eq w (e.symm z), e.apply_symm_apply] using hw
    rw [hball]
    exact (isCompact_closedBall (e.symm z) R).image e.continuous
  refine ⟨fun i => phi i+N, ?_, Y, inferInstance, hproper, e (none : s.Index), ?_⟩
  · intro i j hij
    exact Nat.add_lt_add_right (hphi hij) N
  · have hlimit := (s.rescalingsConverge phi hr' hconv).postcomp_isometry e
    simpa only [r', Function.comp_def] using hlimit

end RegularPointCoordinates

end

end OAI
