import OAI.Analysis.CircleDomains.Uniformization.InjectivePhaseLimit
import OAI.Analysis.CircleDomains.Selection.CyclicSelectedSubsequence

namespace OAI

/-! Every sequence of selected radii has a positive subsequential limit;
this excludes all degeneration, not only collapse of one chosen limit. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}

lemma PhaseCollar.exists_positive_radius_limit_along (P:PhaseCollar C i) (t:ℕ→ℕ) :
    ∃s:ℕ→ℕ,∃ρ:ℝ,StrictMono s ∧ 0<ρ ∧
      Tendsto (fun n => selectedRadius C (cyclicSchedule m) (visitTime (t (s n)) i)) atTop (𝓝 ρ) := by
  obtain ⟨a,c,r,ha,hr,hc,hρ⟩ := exists_cyclic_selected_disk_limits_along C t
  obtain ⟨b,F,G,hb,hF,_,hFd,_,_,_,hi⟩ := P.exists_joint_limit (t ∘ a)
  have hcircle : ∀z∈symmetricCircleAnnulus P.radius,‖z‖=1 → ‖F z-c i‖=r i := by
    intro z hz hz1
    exact moving_circle_reflection_limit_boundary
      (f:=fun n => P.trace (t (a n)))
      (c:=fun n => selectedCenter C (cyclicSchedule m) (visitTime (t (a n)) i))
      (r:=fun n => selectedRadius C (cyclicSchedule m) (visitTime (t (a n)) i)) (F:=F)
      (fun n => selectedRadius_pos C (cyclicSchedule m) (visitTime (t (a n)) i)) hb hF
      (hc i) (hρ i) (fun n => P.circle (t (a n))) hz hz1
  exact ⟨a ∘ b,r i,ha.comp hb,circle_radius_pos_of_injective_outer P.radius_gt (hr i) hFd hi hcircle,
    (hρ i).comp hb.tendsto_atTop⟩

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
