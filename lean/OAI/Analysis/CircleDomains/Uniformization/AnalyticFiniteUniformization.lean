import OAI.Analysis.CircleDomains.Reflection.AnalyticRoundCapImages
import OAI.Analysis.CircleDomains.Reflection.AnalyticStraighteningHolomorphic
import OAI.Analysis.CircleDomains.Topology.ExteriorHomeomorphGerm
import OAI.Analysis.CircleDomains.Uniformization.ConformalInverse
import OAI.Analysis.CircleDomains.Topology.BoundedRoundDisks

namespace OAI

/-! Unconditional uniformization of a finite analytic Jordan configuration.
The conformal map is the actual principal solution composed with the smooth
rounding comparison; the round cap images are proved from reflection. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_analytic_finite_uniformization {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) (ha : ∀i,IsAnalyticJordanCap (C.hole i)) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f C.region V := by
  obtain ⟨D⟩ := exists_analytic_reflection_data C ha
  obtain ⟨s,hs,hcaps⟩ := D.exists_round_cap_images
  let H : ℂ ≃ₜ ℂ := D.comparison.trans D.principal
  let V : Set Sphere := H.onePointCongr '' C.region
  let K : Set ℂ := ⋃i,closure (jordanInterior (C.hole i))
  have hK : IsCompact K := isCompact_iUnion fun i => isCompact_closure_jordanInterior (C.hole i)
  have hr : C.region=(((↑) : ℂ → Sphere) '' K)ᶜ := by
    change (⋃i,((↑) : ℂ → Sphere) '' closure (jordanInterior (C.hole i)))ᶜ=_
    rw [image_iUnion]
  have hconf : IsConformalOn H.onePointCongr C.region := by
    rw [hr]
    apply exterior_homeomorph_conformalOn H hK
    intro z hz
    have hp : (z : Sphere)∈C.region := by
      rw [hr]
      simpa only [mem_compl_iff,OnePoint.coe_injective.mem_set_image] using hz
    exact (D.straightening_holomorphic z hp).differentiableAt
      ((C.region_open.preimage OnePoint.continuous_coe).mem_nhds hp)
  have hcomp : Vᶜ=⋃i,((↑) : ℂ → Sphere) '' closedBall (D.principal (D.center i)) (s i) := by
    have hh := rounding_spherical_exterior_image C H (fun i => D.principal (D.center i)) s hcaps
    change (H.onePointCongr '' C.region)ᶜ=_
    rw [hh,compl_compl]
  have hdisj := rounding_round_disks_disjoint C H (fun i => D.principal (D.center i)) s hcaps
  have hV : IsCircleDomain V := by
    refine ⟨H.onePointCongr.isOpenMap _ C.region_open,
      C.region_connected.image _ H.onePointCongr.continuous.continuousOn,?_⟩
    intro p hp
    have hp' := hp
    rw [hcomp] at hp'
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp'
    right
    rw [hcomp,connectedComponentIn_finite_disjoint_closed
      (fun i => ((↑) : ℂ → Sphere) '' closedBall (D.principal (D.center i)) (s i))
      (fun i => ((isCompact_closedBall _ _).image OnePoint.continuous_coe).isClosed)
      (fun i => (convex_closedBall (D.principal (D.center i)) (s i)).isPreconnected.image _
        OnePoint.continuous_coe.continuousOn) hdisj hi]
    exact isRoundClosedDisk_coe_closedBall _ (hs i)
  exact ⟨V,H.onePointCongr,hV,isConformalEquivalence_of_injOn hconf C.region_open
    H.onePointCongr.injective.injOn⟩

end CircleDomainRigidity

end

end OAI
