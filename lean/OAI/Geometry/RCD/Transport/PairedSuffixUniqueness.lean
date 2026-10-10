import OAI.Geometry.RCD.Transport.PairedPathUniqueness
import OAI.Geometry.RCD.Transport.PathReversal

namespace OAI

/-! # The same uniqueness argument for a common terminal interval -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem paired_common_suffix_unique (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ]
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π)
    (q : Time) (hq : q < 1)
    (hsuffix : ∀ᵐ z ∂σ, ∀ r : Time, q ≤ r → z.1 r=z.2 r) :
    ∀ᵐ z ∂σ, z.1=z.2 := by
  let : CompleteSpace X := hX.complete
  let : Nonempty X := nonempty_of_isProbabilityMeasure (π.map (fun γ => γ 0))
  have hfin := coupling_transportCost_ne_top hp.1 hp.2.1 p
    (integrable_dist_sq_of_ae_bounded _ p hs₀) (integrable_dist_sq_of_ae_bounded _ p hs₁)
  obtain ⟨_,hgrev,hprev⟩ := geodesic_subpath_law π hg hp hfin 1 0
  let πr := π.map (subpath 1 0)
  have hcomp (r : Time) : πr.map (fun γ => γ r) ≤ ENNReal.ofReal C • hausdorff n X := by
    rw [show πr=π.map (subpath 1 0) from rfl,subpath_map_eval]
    exact hc _
  have hprev' : IsOptimalCoupling (πr.map (fun γ => γ 0)) (πr.map (fun γ => γ 1))
      (πr.map (fun γ => (γ 0,γ 1))) := by
    simpa only [πr,subpath_map_eval,timeSegment_zero,timeSegment_one] using hprev
  have hsrev₀ : ∀ᵐ x ∂πr.map (fun γ => γ 0), dist x p ≤ R := by
    simpa only [πr,subpath_map_eval,timeSegment_zero] using hs₁
  have hsrev₁ : ∀ᵐ x ∂πr.map (fun γ => γ 1), dist x p ≤ R := by
    simpa only [πr,subpath_map_eval,timeSegment_one] using hs₀
  let F := fun z : C(Time,X)×C(Time,X) => (subpath 1 0 z.1,subpath 1 0 z.2)
  have hF : Measurable F := ((subpath_measurable 1 0).comp measurable_fst).prodMk
    ((subpath_measurable 1 0).comp measurable_snd)
  have hlr : (σ.map F).map Prod.fst ≤ πr := by
    simpa only [Measure.map_map measurable_fst hF,
      Measure.map_map (subpath_measurable 1 0) measurable_fst,Function.comp_def,F] using
      Measure.map_mono hl (subpath_measurable 1 0)
  have hrr : (σ.map F).map Prod.snd ≤ πr := by
    simpa only [Measure.map_map measurable_snd hF,
      Measure.map_map (subpath_measurable 1 0) measurable_snd,Function.comp_def,F] using
      Measure.map_mono hr (subpath_measurable 1 0)
  have hqr : 0 < timeSegment 1 0 q := by
    change (0:ℝ) < (timeSegment 1 0 q:ℝ)
    rw [timeSegment_one_zero_coe]
    exact sub_pos.mpr hq
  have hpast : ∀ᵐ z ∂σ.map F, z ∈ pathAgreement (timeSegment 1 0 q:ℝ) := by
    apply (ae_map_iff hF.aemeasurable (measurableSet_pathAgreement _)).mpr
    filter_upwards [hsuffix] with z hz
    intro r hr
    exact reversed_pair_agreement q z.1 z.2 hz r
      (by simpa only [timeSegment_one_zero_coe] using hr)
  have hu := hX.paired_common_prefix_unique hn p hR πr hgrev hprev' hC hcomp hsrev₀ hsrev₁
    (σ.map F) hlr hrr (timeSegment 1 0 q) hqr hpast
  have hpull := ae_of_ae_map (p:=fun z : C(Time,X)×C(Time,X) => z.1=z.2) hF.aemeasurable hu
  exact hpull.mono fun z hz => subpath_reverse_injective hz

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
