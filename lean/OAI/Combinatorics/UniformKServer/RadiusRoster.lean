import Mathlib
import OAI.Combinatorics.UniformKServer.ChronologicalRoster
import OAI.Combinatorics.UniformKServer.FirstHitSupport
import OAI.Combinatorics.UniformKServer.RadiusFirstHit

namespace OAI

                                   
section

/-! The first-hit estimate for the entire actual present roster.  The global
roster may have far more than K² records. Only centers that can hit one of the
two points incur a truncated-tail correction; all other coordinates remain
in the actual independent product law. -/
namespace UniformKServer.RadiusRoster
noncomputable section
open FiniteProbability
attribute [local instance] Classical.propDecidable
variable {I : Type*} [LinearOrder I] {X : Type} [Fintype X] [MetricSpace X]

omit [Fintype X] in
/-- Repeated centers are distinct chronological identities, not collapsed
into a set of sites. This count therefore applies to the actual roster. -/
theorem candidate_count (S : Finset I) (is : List I) (c : I → X) (r : ℝ)
    (A : ℕ) (x y : X) (hr : 0 ≤ r) (hxy : dist x y ≤ r)
    (hnodup : is.Nodup) (hsub : ∀ i ∈ is, i ∈ S)
    (hage : ∀ i ∈ is, ChronologicalRoster.age S c r i < A) :
    (is.filter (fun i => decide (dist (c i) x ≤ 2*r ∨ dist (c i) y ≤ 2*r))).length ≤ A := by
  let P : I → Prop := fun i => dist (c i) x ≤ 2*r ∨ dist (c i) y ≤ 2*r
  let T := (is.filter (fun i => decide (P i))).toFinset
  have hmem (i : I) : i ∈ T ↔ i ∈ is ∧ P i := by simp [T]
  have hnear (i : I) (hi : i ∈ T) : dist (c i) x ≤ 3*r := by
    rcases (hmem i).mp hi with ⟨_,hi|hi⟩
    · linarith
    · have ht := dist_triangle (c i) y x
      rw [dist_comm y x] at ht
      linarith
  have hc : T.card ≤ A := ChronologicalRoster.local_age_count S T c r A
    (fun i hi => hsub i ((hmem i).mp hi).1)
    (fun i hi => hage i ((hmem i).mp hi).1)
    (by
      intro i hi j hj
      have ht := dist_triangle (c i) x (c j)
      rw [dist_comm x (c j)] at ht
      linarith [hnear i hi,hnear j hj])
  simpa only [T,List.toFinset_card_of_nodup (hnodup.filter _)] using hc

/-- Outside the geometric support the hit probability is exactly zero.
The endpoint convention matches the zero tail at 2r. -/
theorem hit_zero (lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r) (c x y : X)
    (hx : 2*r ≤ dist c x) (hy : 2*r ≤ dist c y) :
    FirstHit.hitProbability (RadiusFirstHit.entry lam r c x y) = 0 := by
  have hp (z : X) : RadiusFirstHit.coverage lam r c z ∈ Set.Icc (0:ℝ) 1 :=
    RadiusTail.tail_bounds lam _ hlam
  change (FiniteThreshold.experiment (RadiusFirstHit.coverage lam r c)).expect
    (fun ω => if ω.val x || ω.val y then (1:ℝ) else 0) = 0
  rw [FiniteThreshold.threshold_hit (RadiusFirstHit.coverage lam r c) hp x y]
  unfold RadiusFirstHit.coverage
  rw [RadiusTail.tail_eq_zero lam _ ((le_div_iff₀ hr).mpr hx),
    RadiusTail.tail_eq_zero lam _ ((le_div_iff₀ hr).mpr hy),max_self]

/-- Source lemma first-hit, with the real chronological age hypothesis rather
than a false bound on the length of the whole present roster. -/
theorem present_first_hit (S : Finset I) (is : List I) (c : I → X)
    (K : ℕ) (hK : 2 ≤ K) (r : ℝ) (hr : 0 < r) (x y : X)
    (hxy : dist x y < r/4) (hnodup : is.Nodup)
    (hsub : ∀ i ∈ is, i ∈ S)
    (hage : ∀ i ∈ is, ChronologicalRoster.age S c r i < K^2) :
    (FirstHit.experiment (is.map (fun i =>
      RadiusFirstHit.entry (Real.log (1+(K:ℝ)^2)) r (c i) x y))).expect
      (fun ω => if FirstHit.firstSeparates _ ω then 1 else 0) ≤
        2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  let lam := Real.log (1+(K:ℝ)^2)
  let P : I → Prop := fun i => dist (c i) x ≤ 2*r ∨ dist (c i) y ≤ 2*r
  have hKr : (0:ℝ) < K := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hK)
  have hsq : 0 < (K:ℝ)^2 := sq_pos_of_pos hKr
  have hlam : 0 < lam := Real.log_pos (by linarith)
  have hexp : Real.exp lam-1 = (K:ℝ)^2 := by
    rw [Real.exp_log (by positivity)]
    ring
  have hb := FirstHit.first_hit_support is
    (fun i => RadiusFirstHit.entry lam r (c i) x y) P
    (lam*dist x y/r) (1/(K:ℝ)^2) (by positivity) (by positivity)
    (by
      intro i _ _
      simpa only [hexp] using RadiusFirstHit.local_bound lam r hlam hr (c i) x y)
    (by
      intro i _ hi
      have hmiss := not_or.mp hi
      exact hit_zero lam r hlam hr (c i) x y
        (le_of_not_ge hmiss.1) (le_of_not_ge hmiss.2))
  have hcount := candidate_count S is c r (K^2) x y hr.le (by linarith)
    hnodup hsub hage
  have hcR : ((is.filter (fun i => decide (P i))).length:ℝ) ≤ (K:ℝ)^2 := by
    exact_mod_cast hcount
  have hc : ((is.filter (fun i => decide (P i))).length:ℝ)*(1/(K:ℝ)^2) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hsq).mpr hcR
  calc
    _ ≤ (lam*dist x y/r)*(1+((is.filter (fun i => decide (P i))).length:ℝ)*(1/(K:ℝ)^2)) := by simpa [lam,P] using hb
    _ ≤ (lam*dist x y/r)*2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by dsimp [lam]; ring

end
end UniformKServer.RadiusRoster

end



end OAI
