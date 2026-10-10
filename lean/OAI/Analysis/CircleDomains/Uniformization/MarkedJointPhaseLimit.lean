import OAI.Analysis.CircleDomains.Uniformization.JointPhaseLimit

namespace OAI

/-! The selected disk parameters and the actual reflected conformal
maps converge together. The limiting collar has exact circular values. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}

lemma PhaseCollar.exists_marked_joint_limit (P:PhaseCollar C i) :
    ∃s:ℕ→ℕ, ∃F G:ℂ→ℂ, ∃a:ℂ, ∃ρ:ℝ, StrictMono s ∧ 0≤ρ ∧
      Tendsto (fun n => selectedCenter C (cyclicSchedule m) (visitTime (s n) i)) atTop (𝓝 a) ∧
      Tendsto (fun n => selectedRadius C (cyclicSchedule m) (visitTime (s n) i)) atTop (𝓝 ρ) ∧
      TendstoLocallyUniformlyOn (fun n => P.reflected (s n)) F atTop
        (symmetricCircleAnnulus P.radius) ∧
      TendstoLocallyUniformlyOn (fun n (z:ℂ) => finiteCoord
        (cumulativeMap C (cyclicSchedule m) (visitTime (s n) i+1) (z:Sphere)))
        G atTop C.planeRegion ∧
      DifferentiableOn ℂ F (symmetricCircleAnnulus P.radius) ∧
      IsPrincipalNormalized (extendAtInfinity G) ∧
      IsConformalEquivalence (extendAtInfinity G) C.region (extendAtInfinity G '' C.region) ∧
      (∀z∈symmetricCircleAnnulus P.radius,1<‖z‖ → F z=G (P.coordinate z)) ∧
      InjOn F (symmetricCircleAnnulus P.radius∩{z | 1<‖z‖}) ∧
      ∀z∈symmetricCircleAnnulus P.radius,‖z‖=1 → ‖F z-a‖=ρ := by
  obtain ⟨t,c,r,ht,hr,hc,hρ,_⟩ := exists_cyclic_selected_disk_limits C
  obtain ⟨s,F,G,hs,hF,hG,hFd,hGn,hGc,he,hi⟩ := P.exists_joint_limit t
  refine ⟨t ∘ s,F,G,c i,r i,ht.comp hs,hr i,
    (hc i).comp hs.tendsto_atTop,(hρ i).comp hs.tendsto_atTop,
    hF,hG,hFd,hGn,hGc,he,hi,?_⟩
  intro z hz hz1
  exact moving_circle_reflection_limit_boundary
    (f := fun n => P.trace (t n))
    (c := fun n => selectedCenter C (cyclicSchedule m) (visitTime (t n) i))
    (r := fun n => selectedRadius C (cyclicSchedule m) (visitTime (t n) i)) (F := F)
    (fun n => selectedRadius_pos C (cyclicSchedule m) (visitTime (t n) i)) hs hF
    (hc i) (hρ i) (fun n => P.circle (t n)) hz hz1

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
