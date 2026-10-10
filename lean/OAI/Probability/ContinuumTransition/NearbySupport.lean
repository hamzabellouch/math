import OAI.Probability.ContinuumTransition.LocalSupports

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma support_ball_growth {F : Parameter → ℝ} {x g : Parameter} {γ : ℝ} (hγ : 0 ≤ γ)
    (hb : ∀ v ∈ closedBall g γ, SupportOn pressureDomain F x v)
    {y : Parameter} (hy : y ∈ pressureDomain) :
    γ*‖y-x‖ ≤ F y-F x-pDot g (y-x) := by
  have h1 := hb (g.1+γ,g.2) (by simpa [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,abs_of_nonneg hγ] using hγ) y hy
  have h2 := hb (g.1-γ,g.2) (by simpa [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,abs_of_nonneg hγ] using hγ) y hy
  have h3 := hb (g.1,g.2+γ) (by simpa [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,abs_of_nonneg hγ] using hγ) y hy
  have h4 := hb (g.1,g.2-γ) (by simpa [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,abs_of_nonneg hγ] using hγ) y hy
  rw [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs,Real.norm_eq_abs]
  dsimp [pDot] at *
  rcases le_total |y.1-x.1| |y.2-x.2| with hh | hh
  · rw [max_eq_right hh]
    rcases le_total 0 (y.2-x.2) with hs | hs
    · rw [abs_of_nonneg hs]; nlinarith only [h3]
    · rw [abs_of_nonpos hs]; nlinarith only [h4]
  · rw [max_eq_left hh]
    rcases le_total 0 (y.1-x.1) with hs | hs
    · rw [abs_of_nonneg hs]; nlinarith only [h1]
    · rw [abs_of_nonpos hs]; nlinarith only [h2]

lemma nearby_center_support {F Q P : Parameter → ℝ} {x g : Parameter} {γ r C S a : ℝ}
    (_hF : ConvexOn ℝ pressureDomain F) (hP : ConvexOn ℝ pressureDomain P)
    (_hx : x ∈ pressureDomain) (hγ : 0 < γ) (hS : 0 < S) (ha : 0 < a) (ha1 : a < 1)
    (hCS : C+2 < γ*S) (hr : S*a < r) (hball : ball x r ⊆ pressureDomain)
    (hsl : ∀ v ∈ closedBall g γ, SupportOn pressureDomain F x v)
    (happ : ∀ y ∈ ball x r, |Q y-F y| ≤ a^2)
    (hge : ∀ y ∈ ball x r, Q y ≤ P y) (hgain : P x ≤ Q x+C*a) :
    ∃ z ∈ ball x (S*a), SupportOn pressureDomain P z g := by
  have hSa : 0 < S*a := mul_pos hS ha
  have hr0 : 0 < r := hSa.trans hr
  have hsub : closedBall x (S*a) ⊆ ball x r := fun y hy => lt_of_le_of_lt hy hr
  have hcont : ContinuousOn (fun y => P y-pDot g y) (closedBall x (S*a)) :=
    (hP.continuousOn isOpen_pressureDomain |>.mono (hsub.trans hball)).sub
      (show Continuous (fun y => pDot g y) by unfold pDot; fun_prop).continuousOn
  obtain ⟨z,hz,hmin⟩ := (isCompact_closedBall x (S*a)).exists_isMinOn
    ⟨x,mem_closedBall_self hSa.le⟩ hcont
  have hi : z ∈ ball x (S*a) := by
    by_contra hn
    have hd : dist z x = S*a := le_antisymm hz (le_of_not_gt hn)
    have hg := support_ball_growth hγ.le hsl (hball (hsub hz))
    have he1 := (abs_le.mp (happ z (hsub hz))).1
    have he2 := (abs_le.mp (happ x (mem_ball_self hr0))).2
    have he3 := hge z (hsub hz)
    have he4 := hmin (mem_closedBall_self hSa.le)
    change P z-pDot g z ≤ P x-pDot g x at he4
    rw [← dist_eq_norm_sub,hd] at hg
    have hex : pDot g (z-x) = pDot g z-pDot g x := by dsimp [pDot]; ring
    rw [hex] at hg
    have hmul := mul_lt_mul_of_pos_right hCS ha
    have hsq := mul_lt_mul_of_pos_left ha1 (show 0 < 2*a by positivity)
    nlinarith only [hg,he1,he2,he3,he4,hgain,hmul,hsq]
  refine ⟨z,hi,support_of_interior_min hP (hball (hsub hz)) ?_ (fun y hy => hmin hy)⟩
  exact mem_of_superset (isOpen_ball.mem_nhds hi) ball_subset_closedBall

end ContinuumTemperature
end
end

end OAI
