import OAI.Geometry.RCD.Transport.CompressedEntropyConvexity

namespace OAI

/-! # Strong entropy convexity on each subinterval of a compressed plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem compressed_plan_segment_entropy (hn : 2≤n) (p : X) {R : ℝ} (hR : 0≤R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p≤R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p≤R) (s t r : Time) :
    boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ (timeSegment s t r))) ≤
      (1-(r:ℝ))*boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ s))+
      (r:ℝ)*boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ t))-
      (K/2)*(r:ℝ)*(1-(r:ℝ))*|(s:ℝ)-(t:ℝ)|^2*
        (wassersteinSq (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))).toReal := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure (π.map (fun γ => γ 0))
  let : CompleteSpace X := hX.complete
  have hfin := coupling_transportCost_ne_top hp.1 hp.2.1 p
    (integrable_dist_sq_of_ae_bounded _ p hs₀) (integrable_dist_sq_of_ae_bounded _ p hs₁)
  obtain ⟨hprob,hg',hp'⟩ := geodesic_subpath_law π hg hp hfin s t
  have hsupport (u : Time) : ∀ᵐ x ∂π.map (fun γ => γ u), dist x p≤3*R := by
    apply (ae_map_iff (measurable_path_eval u).aemeasurable
      (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)).mpr
    exact (optimal_geodesic_plan_bounded _ _ π hg hp p hR hs₀ hs₁).mono fun γ hγ => hγ.2 u
  have hp'' : IsOptimalCoupling
      ((π.map (subpath s t)).map (fun γ => γ 0))
      ((π.map (subpath s t)).map (fun γ => γ 1))
      ((π.map (subpath s t)).map (fun γ => (γ 0,γ 1))) := by
    simpa only [subpath_map_eval,timeSegment_zero,timeSegment_one] using hp'
  have hcomp' (u : Time) :
      (π.map (subpath s t)).map (fun γ => γ u)≤ENNReal.ofReal C • hausdorff n X := by
    rw [subpath_map_eval]
    exact hcomp _
  have h := hX.compressed_plan_entropy_convexity hn p (R:=3*R)
    (mul_nonneg (by norm_num) hR) (π.map (subpath s t)) hg' hp'' hcomp'
    (by simpa only [subpath_map_eval,timeSegment_zero] using hsupport s)
    (by simpa only [subpath_map_eval,timeSegment_one] using hsupport t) r
  simp only [subpath_map_eval,timeSegment_zero,timeSegment_one] at h
  have he : (wassersteinSq (π.map (fun γ => γ s)) (π.map (fun γ => γ t))).toReal=
      |(s:ℝ)-(t:ℝ)|^2*
        (wassersteinSq (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))).toReal := by
    rw [wassersteinSq_eq_cost (geodesic_plan_optimal_marginals π hg hp hfin s t),
      geodesic_plan_cost π hg,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),wassersteinSq_eq_cost hp]
  rw [he] at h
  convert h using 1
  ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
