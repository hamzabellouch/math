import OAI.Probability.SLE.Loewner.InitialForwardNormalFamily
import OAI.Probability.SLE.Loewner.InitialForwardBaseBounds
import OAI.Probability.SLE.Geometry.HolomorphicDiskInterior

namespace OAI

/-! Limits of the compactified forward charts stay in the open disk. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma initialForwardCayley_limit_interior (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {A : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (upperHalfPlane \ range p))
    (hlim : TendstoLocallyUniformlyOn
      (fun n z => halfPlaneCayley (initialForwardChart p hi h0 hH (t n) z))
      A atTop (upperHalfPlane \ range p)) :
    ∀ z∈upperHalfPlane \ range p, ‖A z‖<1 := by
  obtain ⟨R0,hR0⟩ := (isCompact_range p.continuous).isBounded.exists_norm_le
  let R := max R0 1
  have hR : 0<R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hp (u : unitInterval) : ‖p u‖≤R := (hR0 _ (mem_range_self u)).trans (le_max_left _ _)
  let b : ℂ := ((2*R:ℝ):ℂ)*I
  have hb : b∈upperHalfPlane \ range p := initialForward_base_mem_domain p hR hp
  have hbound (n : ℕ) := initialForwardChart_base_bounds p hi h0 hH hR hp (t n)
  obtain ⟨v,_,φ,hφ,hv⟩ := (isCompact_closedBall (0:ℂ) (3*R)).tendsto_subseq (fun n => by
    rw [mem_closedBall,dist_zero_right]
    exact (hbound n).2)
  have hvim : 3*R/2≤v.im := ge_of_tendsto (continuous_im.continuousAt.tendsto.comp hv)
    (Eventually.of_forall fun n => (hbound (φ n)).1)
  have hvH : v∈upperHalfPlane := lt_of_lt_of_le (by positivity : 0<3*R/2) hvim
  have he : A b=halfPlaneCayley v := by
    apply tendsto_nhds_unique ((hlim.tendsto_at hb).comp hφ.tendsto_atTop)
    exact (halfPlaneCayley_differentiableOn.continuousOn v hvH).continuousAt
      (isOpen_upperHalfPlane.mem_nhds hvH) |>.tendsto.comp hv
  have hAb : ‖A b‖<1 := by rw [he]; exact halfPlaneCayley_norm_lt hvH
  have hnorm : ∀ z∈upperHalfPlane \ range p, ‖A z‖≤1 := by
    intro z hz
    apply le_of_tendsto (hlim.tendsto_at hz).norm
    exact Eventually.of_forall fun n => (halfPlaneCayley_norm_lt
      (initialForwardChart_mapsTo p hi h0 hH (t n) hz)).le
  exact holomorphic_disk_strict_of_point
    (isOpen_upperHalfPlane.sdiff (isCompact_range p.continuous).isClosed)
    (simple_arc_halfPlane_complement_connected p hi h0 hH).isPreconnected hA hnorm hb hAb

end SLEExactGauge

end

end OAI
