import OAI.Geometry.RCD.Transport.CompressedInitialInverse

namespace OAI

/-! # Measurable inverses for every evaluation, including both endpoints -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem compressed_final_inverse (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    :
    ∃ g : X → C(Time,X), Measurable g ∧ ∀ᵐ γ ∂π, g (γ 1)=γ := by
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
  obtain ⟨g,hg,hgi⟩ := hX.compressed_initial_inverse hn p hR πr hgrev hprev' hC hcomp hsrev₀ hsrev₁
  refine ⟨(subpath 1 0) ∘ g,(subpath_measurable 1 0).comp hg,?_⟩
  have hi := ae_of_ae_map (μ:=π) (subpath_measurable 1 0).aemeasurable hgi
  filter_upwards [hi] with γ hγ
  change g (γ (timeSegment 1 0 0))=subpath 1 0 γ at hγ
  rw [timeSegment_zero] at hγ
  have hγ' : g (γ 1)=subpath 1 0 γ := hγ
  change subpath 1 0 (g (γ 1))=γ
  rw [hγ',subpath_reverse_reverse]

theorem compressed_time_inverse (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (t : Time) :
    ∃ g : X → C(Time,X), Measurable g ∧ ∀ᵐ γ ∂π, g (γ t)=γ := by
  by_cases h0 : t=0
  · subst t
    exact hX.compressed_initial_inverse hn p hR π hg hp hC hc hs₀ hs₁
  by_cases h1 : t=1
  · subst t
    exact hX.compressed_final_inverse hn p hR π hg hp hC hc hs₀ hs₁
  exact hX.compressed_evaluation_inverse hn p hR π hg hp hC hc hs₀ hs₁ t
    (lt_of_le_of_ne t.property.1 (by intro he; exact h0 (Subtype.ext he.symm)))
    (lt_of_le_of_ne t.property.2 (by intro he; exact h1 (Subtype.ext he)))

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
