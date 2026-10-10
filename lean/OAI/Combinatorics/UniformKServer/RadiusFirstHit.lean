import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteThreshold
import OAI.Combinatorics.UniformKServer.FirstHit
import OAI.Combinatorics.UniformKServer.RadiusTail

namespace OAI

                                     
section
namespace UniformKServer.RadiusFirstHit
noncomputable section
open FiniteProbability
attribute [local instance] Classical.propDecidable
variable {X : Type} [Fintype X] [MetricSpace X]

def coverage (lam r : ℝ) (c : X) : X → ℝ := fun p => RadiusTail.tail lam (dist c p/r)

def entry (lam r : ℝ) (c x y : X) : FirstHit.Entry where
  Sample := FiniteThreshold.Signature (coverage lam r c)
  finite := inferInstance
  law := FiniteThreshold.experiment (coverage lam r c)
  hit ω := ω.val x || ω.val y
  separates ω := ω.val x != ω.val y
  separates_hit := by
    intro ω h
    cases hx : ω.val x <;> cases hy : ω.val y <;> simp_all
theorem ordered_tail (lam a b D : ℝ) (hlam : 0 < lam) (hab : a ≤ b) (hD : b-a ≤ D) :
    |RadiusTail.tail lam a-RadiusTail.tail lam b| ≤
      lam*D*(max (RadiusTail.tail lam a) (RadiusTail.tail lam b)+1/(Real.exp lam-1)) := by
  have hanti := RadiusTail.tail_antitone lam hlam hab
  rw [abs_of_nonneg (sub_nonneg.mpr hanti),max_eq_left hanti]
  apply (RadiusTail.tail_difference lam a b hlam hab).trans
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hlam.le)
  exact add_nonneg (RadiusTail.tail_bounds lam a hlam).1
    (one_div_nonneg.mpr (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hlam.le)))

theorem local_bound (lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r) (c x y : X) :
    FirstHit.separationProbability (entry lam r c x y) ≤
      (lam*dist x y/r)*(FirstHit.hitProbability (entry lam r c x y)+1/(Real.exp lam-1)) := by
  have hp (z : X) : coverage lam r c z ∈ Set.Icc (0:ℝ) 1 := RadiusTail.tail_bounds lam _ hlam
  change (FiniteThreshold.experiment (coverage lam r c)).expect
      (fun ω => if ω.val x != ω.val y then (1:ℝ) else 0) ≤
    (lam*dist x y/r)*((FiniteThreshold.experiment (coverage lam r c)).expect
      (fun ω => if ω.val x || ω.val y then (1:ℝ) else 0)+_)
  rw [FiniteThreshold.threshold_separation (coverage lam r c) hp x y,
    FiniteThreshold.threshold_hit (coverage lam r c) hp x y]
  unfold coverage
  rw [mul_div_assoc]
  rcases le_total (dist c x) (dist c y) with hxy|hyx
  · apply ordered_tail lam _ _ _ hlam (div_le_div_of_nonneg_right hxy hr.le)
    rw [←sub_div]
    apply div_le_div_of_nonneg_right _ hr.le
    linarith [dist_triangle c x y]
  · rw [abs_sub_comm,max_comm]
    apply ordered_tail lam _ _ _ hlam (div_le_div_of_nonneg_right hyx hr.le)
    rw [←sub_div]
    apply div_le_div_of_nonneg_right _ hr.le
    linarith [dist_triangle c y x,dist_comm x y]
/-- The radius laws are constructed, not postulated. Chronological candidate
count is used only in the tail correction, never multiplying the main term. -/
theorem actual_first_hit (cs : List X) (K : ℕ) (hK : 2 ≤ K) (r : ℝ) (hr : 0 < r)
    (x y : X) (hcount : cs.length ≤ K^2) :
    (FirstHit.experiment (cs.map (fun c => entry (Real.log (1+(K:ℝ)^2)) r c x y))).expect
      (fun ω => if FirstHit.firstSeparates _ ω then 1 else 0) ≤
        2*Real.log (1+(K:ℝ)^2)*dist x y/r
 := by
  have hKr : (0:ℝ) < K := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hK)
  have hsq : 0 < (K:ℝ)^2 := sq_pos_of_pos hKr
  have hlog : 0 < Real.log (1+(K:ℝ)^2) := Real.log_pos (by linarith)
  have hexp : Real.exp (Real.log (1+(K:ℝ)^2))-1 = (K:ℝ)^2 := by
    rw [Real.exp_log (by positivity)]
    ring
  have hb := FirstHit.first_hit_bound (cs.map (fun c => entry (Real.log (1+(K:ℝ)^2)) r c x y))
    (Real.log (1+(K:ℝ)^2)*dist x y/r) (1/(K:ℝ)^2) (by positivity) (by positivity)
    (by
      intro E hE
      obtain ⟨c,_,rfl⟩ := List.mem_map.mp hE
      simpa only [hexp] using local_bound (Real.log (1+(K:ℝ)^2)) r hlog hr c x y)
  have hcountR : (cs.length:ℝ) ≤ (K:ℝ)^2 := by exact_mod_cast hcount
  have hc : (cs.length:ℝ)*(1/(K:ℝ)^2) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hsq).mpr hcountR
  simp only [List.length_map] at hb
  calc
    _ ≤ (Real.log (1+(K:ℝ)^2)*dist x y/r)*(1+(cs.length:ℝ)*(1/(K:ℝ)^2)) := hb
    _ ≤ (Real.log (1+(K:ℝ)^2)*dist x y/r)*2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring
end
end UniformKServer.RadiusFirstHit

end



end OAI
