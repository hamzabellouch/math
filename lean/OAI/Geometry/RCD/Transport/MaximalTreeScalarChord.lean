import OAI.Geometry.RCD.Transport.CompressedPlanChildren
import OAI.Geometry.RCD.Transport.ReducedChord

namespace OAI

/-! # Scalar interpolation on any compressed tree of maximal midpoints

The construction need not be a particular selected tree. Only its actual
midpoint maximality and uniform compression enter the induction.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.maximal_tree_scalar_chord
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) {C : ℝ≥0∞} (hC : C≠∞) (m : ℕ) :
    ∀ (a : RenyiTransportNode n X) (π : Measure C(Time,X)) (_hπ : IsProbabilityMeasure π),
      (∀ᵐ γ ∂π, IsGeodesic γ) →
      IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))) →
      (∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X) →
      RenyiDyadicMaximal (hausdorff n X) (1-1/N) (fun t => π.map (fun γ => γ t)) m →
      ∀ t∈dyadicGrid m,
        reducedChord K (N+1) a.distance
          (renyiIntegral (hausdorff n X) (π.map (fun γ => γ 0)) N)
          (renyiIntegral (hausdorff n X) (π.map (fun γ => γ 1)) N) t ≤
            renyiIntegral (hausdorff n X) (π.map (fun γ => γ t)) N := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  have hNp : 1<N+1 := by
    have hnR : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  induction m with
  | zero =>
    intro a π hπ hg hp hc hm t ht
    rcases ht with rfl | ht
    · rw [reducedChord_zero hK hNp a.distance_nonneg]
    · have he : t=1 := ht
      subst t
      rw [reducedChord_one hK hNp a.distance_nonneg]
  | succ m ih =>
    intro a π hπ hg hp hc hm t ht
    let := hπ
    let : Nonempty X := ⟨a.center⟩
    let := a.left_probability
    let := a.right_probability
    have he := optimalPlan_endpoints a.left a.right π hp
    have hroot := hm.1
    dsimp only at hroot
    rw [he.1,he.2] at hroot
    have hmid := hX.maximal_scalar_midpoint K n hn hK hN a π hg hp hroot
    rw [←he.1,←he.2] at hmid
    obtain ⟨a₀,a₁,h00,h0m,h1m,h11,hd0,hd1⟩ := compressed_plan_children a π hg hp hC hc
    have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
        (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
    have hfin := finite_second_moment_cost
      (finiteSecondMoment_of_bounded a.left a.center a.left_support)
      (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
    obtain ⟨hL,hgL,hpL⟩ := geodesic_subpath_law π hg hpp hfin 0 midpointTime
    obtain ⟨hR,hgR,hpR⟩ := geodesic_subpath_law π hg hpp hfin midpointTime 1
    have hpL' : IsOptimalCoupling a₀.left a₀.right
        ((π.map (subpath 0 midpointTime)).map (fun γ => (γ 0,γ 1))) := by rw [h00,h0m]; exact hpL
    have hpR' : IsOptimalCoupling a₁.left a₁.right
        ((π.map (subpath midpointTime 1)).map (fun γ => (γ 0,γ 1))) := by rw [h1m,h11]; exact hpR
    have hcL (s : Time) : (π.map (subpath 0 midpointTime)).map (fun γ => γ s)≤C • hausdorff n X := by
      rw [subpath_map_eval]; exact hc _
    have hcR (s : Time) : (π.map (subpath midpointTime 1)).map (fun γ => γ s)≤C • hausdorff n X := by
      rw [subpath_map_eval]; exact hc _
    have hmL := hm.2.1.congr (fun s => (subpath_map_eval π 0 midpointTime s).symm)
    have hmR := hm.2.2.congr (fun s => (subpath_map_eval π midpointTime 1 s).symm)
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [reducedChord_lower hK hNp a.distance_nonneg]
      refine (reducedChord_mono le_rfl hmid s).trans ?_
      simpa only [hd0,subpath_map_eval,lowerTime,timeSegment_zero,timeSegment_one] using
        ih a₀ _ hL hgL hpL' hcL hmL s hs
    · rw [reducedChord_upper hK hNp a.distance_nonneg]
      refine (reducedChord_mono hmid le_rfl s).trans ?_
      simpa only [hd1,subpath_map_eval,upperTime,timeSegment_zero,timeSegment_one] using
        ih a₁ _ hR hgR hpR' hcR hmR s hs

end RegularPointCoordinates

end

end OAI
