import OAI.Probability.ContinuumTransition.NearbySupport

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma nearby_support_of_uniform {F P : Parameter → ℝ} (hP : ConvexOn ℝ pressureDomain P)
    {x g : Parameter} {γ r ε : ℝ} (hγ : 0 < γ) (hr : 0 < r)
    (hball : closedBall x r ⊆ pressureDomain)
    (hsl : closedBall g γ ⊆ subgradients pressureDomain F x)
    (happ : ∀ y ∈ closedBall x r, |P y-F y| ≤ ε) (he : 2*ε < γ*r) :
    ∃ z ∈ ball x r, SupportOn pressureDomain P z g := by
  have hcont : ContinuousOn (fun y => P y-pDot g y) (closedBall x r) :=
    (hP.continuousOn isOpen_pressureDomain |>.mono hball).sub
      (show Continuous (fun y => pDot g y) by unfold pDot; fun_prop).continuousOn
  obtain ⟨z,hz,hmin⟩ := (isCompact_closedBall x r).exists_isMinOn ⟨x,mem_closedBall_self hr.le⟩ hcont
  have hi : z ∈ ball x r := by
    by_contra hn
    have hd : dist z x = r := le_antisymm hz (le_of_not_gt hn)
    have hg := support_ball_growth hγ.le (fun v hv => hsl hv) (hball hz)
    have he1 := (abs_le.mp (happ z hz)).1
    have he2 := (abs_le.mp (happ x (mem_closedBall_self hr.le))).2
    have hm := hmin (mem_closedBall_self hr.le)
    change P z-pDot g z ≤ P x-pDot g x at hm
    rw [← dist_eq_norm_sub,hd] at hg
    have hex : pDot g (z-x)=pDot g z-pDot g x := by dsimp [pDot]; ring
    rw [hex] at hg
    linarith only [hg,he1,he2,hm,he]
  refine ⟨z,hi,support_of_interior_min hP (hball hz) ?_ (fun y hy => hmin hy)⟩
  exact mem_of_superset (isOpen_ball.mem_nhds hi) ball_subset_closedBall

end ContinuumTemperature
end
end

end OAI
