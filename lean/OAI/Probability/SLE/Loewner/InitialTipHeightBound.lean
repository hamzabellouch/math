import OAI.Probability.SLE.Loewner.InitialHeightCapacityIncrement
import OAI.Probability.SLE.Loewner.MovingForwardBoundaryHeight
import OAI.Probability.SLE.Geometry.ApproachIntervalEndpoint

namespace OAI

/-! A future point has initial-chart height controlled by the capacity
remaining before that point is swallowed. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

theorem initialForward_tip_height_bound (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) :
    (initialForwardChart p hi h0 hH s (p t)).im^2≤
      2*(initialCapacity p hi h0 hH t-initialCapacity p hi h0 hH s) := by
  let r := approachIntervalEndpoint hst
  have hr (n : ℕ) : r n∈Ico s t := approachIntervalEndpoint_mem hst n
  have hrt : Tendsto r atTop (𝓝 t) := approachIntervalEndpoint_tendsto hst
  obtain ⟨M,hM⟩ := (isCompact_range p.continuous).isBounded.exists_norm_le
  let R := max M 0+1
  have hR : 0<R := by dsimp only [R]; linarith [le_max_right M (0:ℝ)]
  have hp : ∀ u : unitInterval, ‖p u‖<R := by
    intro u
    have hh := hM (p u) (mem_range_self u)
    dsimp only [R]
    linarith [le_max_left M (0:ℝ)]
  have hzd (n : ℕ) : p t∈upperHalfPlane \ range (initialSubarc p (r n)) :=
    point_after_prefix_mem_domain p hi hH (hr n).2
  have hheight : Tendsto (fun n => (initialForwardChart p hi h0 hH (r n) (p t)).im)
      atTop (𝓝 0) :=
    initialForward_boundary_height_zero p hi h0 hH hrt tendsto_const_nhds hzd
      (slit_tip_not_mem_domain p t)
      (fun n => initialForward_uniform_near p hi h0 hH hR hp (r n) (hzd n)
        (by linarith [hp t]))
  have hcap := ((initialCapacity_continuous p hi h0 hH).tendsto t).comp hrt
  have hlim := (hheight.pow 2).add
    ((hcap.sub_const (initialCapacity p hi h0 hH s)).const_mul 2)
  have hineq (n : ℕ) :
      (initialForwardChart p hi h0 hH s (p t)).im^2≤
        (initialForwardChart p hi h0 hH (r n) (p t)).im^2+
          2*(initialCapacity p hi h0 hH (r n)-initialCapacity p hi h0 hH s) := by
    obtain ⟨T,hrT,hTt⟩ := exists_between (hr n).2
    exact initialForward_height_capacity_increment p hi h0 hH (hr n).1 hrT.le
      (hTt.trans ht) (point_after_prefix_mem_domain p hi hH hTt)
  have hh := ge_of_tendsto hlim (Eventually.of_forall hineq)
  simpa only [zero_pow two_ne_zero,zero_add] using hh

end SLEExactGauge

end

end OAI
