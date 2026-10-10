import Mathlib
import OAI.Combinatorics.UniformKServer.RadiusFirstHit

namespace OAI

                                 
section

/-! One universal finite radius seed covers every possible input-driven
center, so the seed law is independent of the hidden input. -/
noncomputable section
namespace UniformKServer.TierRadius
open FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X]
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def probability (lam r : ℝ) (a : X × X) : ℝ := RadiusTail.tail lam (dist a.1 a.2/r)
abbrev Sample (lam r : ℝ) := FiniteThreshold.Signature (@probability X _ lam r)
def law (lam r : ℝ) : Law (Sample (X:=X) lam r) := FiniteThreshold.experiment (probability lam r : X × X → ℝ)

def entry (lam r : ℝ) (c x y : X) : FirstHit.Entry where
  Sample := Sample (X:=X) lam r
  finite := inferInstance
  law := law lam r
  hit ω := ω.val (c,x) || ω.val (c,y)
  separates ω := ω.val (c,x) != ω.val (c,y)
  separates_hit := by
    intro ω h
    cases hx : ω.val (c,x) <;> cases hy : ω.val (c,y) <;> simp_all

omit [Fintype X] in
theorem cover_inner (lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r) (ω : Sample (X:=X) lam r)
    (c p : X) (hd : dist c p ≤ r) : ω.val (c,p)=true := by
  obtain ⟨u,hu,he⟩ := ω.property
  rw [he]
  change decide (u ≤ probability lam r (c,p))=true
  apply decide_eq_true
  change u ≤ RadiusTail.tail lam (dist c p/r)
  rw [RadiusTail.tail_eq_one lam _ hlam ((div_le_one hr).mpr hd)]
  exact hu.2

omit [Fintype X] in
theorem cover_outer (lam r : ℝ) (hr : 0 < r) (ω : Sample (X:=X) lam r)
    (c p : X) (hc : ω.val (c,p)=true) : dist c p < 2*r := by
  by_contra hd
  have hd' : 2 ≤ dist c p/r := (le_div_iff₀ hr).mpr (le_of_not_gt hd)
  obtain ⟨u,hu,he⟩ := ω.property
  rw [he] at hc
  simp only [FiniteThreshold.threshold,decide_eq_true_eq,probability,RadiusTail.tail_eq_zero lam _ hd'] at hc
  exact (not_le_of_gt hu.1) hc

theorem local_bound (lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r) (c x y : X) :
    FirstHit.separationProbability (entry lam r c x y) ≤
      (lam*dist x y/r)*(FirstHit.hitProbability (entry lam r c x y)+1/(Real.exp lam-1)) := by
  have hp (a : X × X) : probability lam r a ∈ Set.Icc (0:ℝ) 1 := RadiusTail.tail_bounds lam _ hlam
  change (FiniteThreshold.experiment (probability lam r : X × X → ℝ)).expect
      (fun ω => if ω.val (c,x) != ω.val (c,y) then (1:ℝ) else 0) ≤
    (lam*dist x y/r)*((FiniteThreshold.experiment (probability lam r : X × X → ℝ)).expect
      (fun ω => if ω.val (c,x) || ω.val (c,y) then (1:ℝ) else 0)+_)
  rw [FiniteThreshold.threshold_separation (probability lam r) hp,
    FiniteThreshold.threshold_hit (probability lam r) hp]
  unfold probability
  rw [mul_div_assoc]
  rcases le_total (dist c x) (dist c y) with hxy|hyx
  · apply RadiusFirstHit.ordered_tail lam _ _ _ hlam (div_le_div_of_nonneg_right hxy hr.le)
    rw [←sub_div]
    apply div_le_div_of_nonneg_right _ hr.le
    linarith [dist_triangle c x y]
  · rw [abs_sub_comm,max_comm]
    apply RadiusFirstHit.ordered_tail lam _ _ _ hlam (div_le_div_of_nonneg_right hyx hr.le)
    rw [←sub_div]
    apply div_le_div_of_nonneg_right _ hr.le
    linarith [dist_triangle c y x,dist_comm x y]

theorem hit_zero (lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r) (c x y : X)
    (hx : 2*r ≤ dist c x) (hy : 2*r ≤ dist c y) :
    FirstHit.hitProbability (entry lam r c x y)=0 := by
  have hp (a : X × X) : probability lam r a ∈ Set.Icc (0:ℝ) 1 := RadiusTail.tail_bounds lam _ hlam
  change (FiniteThreshold.experiment (probability lam r : X × X → ℝ)).expect
    (fun ω => if ω.val (c,x) || ω.val (c,y) then (1:ℝ) else 0)=0
  rw [FiniteThreshold.threshold_hit (probability lam r) hp]
  unfold probability
  rw [RadiusTail.tail_eq_zero lam _ ((le_div_iff₀ hr).mpr hx),
    RadiusTail.tail_eq_zero lam _ ((le_div_iff₀ hr).mpr hy),max_self]

end UniformKServer.TierRadius

end


end

end OAI
