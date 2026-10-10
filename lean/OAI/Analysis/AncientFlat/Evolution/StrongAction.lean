import Mathlib

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace AncientMild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (T : ℝ → E →L[ℂ] E)
  (hc : ∀ v : E, ContinuousOn (fun t => T t v) (Ici (0:ℝ)))
include hc in
lemma bounded_on (b : ℝ) : ∃ C : ℝ, 0≤C ∧ ∀ t ∈ Icc (0:ℝ) b, ‖T t‖≤C := by
  have hv : ∀ v : E, ∃ M, ∀ t : Icc (0:ℝ) b, ‖T t v‖≤M := by
    intro v
    obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image ((hc v).mono Icc_subset_Ici_self).norm
    exact ⟨M,fun t => hM ⟨t,t.property,rfl⟩⟩
  obtain ⟨C,hC⟩ := banach_steinhaus hv
  refine ⟨max 0 C,le_max_left _ _,fun t ht => ?_⟩
  exact (hC ⟨t,ht⟩).trans (le_max_right _ _)
include hc in
lemma continuousOn_action : ContinuousOn (fun p : ℝ × E => T p.1 p.2)
    (Ici (0:ℝ) ×ˢ (univ : Set E)) := by
  intro p hp
  obtain ⟨C,hC,hCb⟩ := bounded_on T hc (p.1+1)
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨η,hη,hηbound⟩ := Metric.continuousWithinAt_iff.mp
    (hc p.2 p.1 hp.1) (ε/2) (by positivity)
  refine ⟨min 1 (min η (ε/(2*(C+1)))),by positivity,fun r hr hdist => ?_⟩
  have hd1 : dist r.1 p.1 < min 1 (min η (ε/(2*(C+1)))) :=
    (le_max_left (dist r.1 p.1) (dist r.2 p.2)).trans_lt hdist
  have hd2 : dist r.2 p.2 < ε/(2*(C+1)) :=
    (le_max_right (dist r.1 p.1) (dist r.2 p.2)).trans_lt (hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hrb : r.1 ∈ Icc (0:ℝ) (p.1+1) := by
    refine ⟨hr.1,?_⟩
    have := (abs_lt.mp (show |r.1-p.1|<1 from hd1.trans_le (min_le_left _ _))).2
    linarith
  have hsmall : ‖T r.1 p.2-T p.1 p.2‖<ε/2 := by
    simpa only [dist_eq_norm] using hηbound hr.1 (hd1.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  rw [dist_eq_norm]
  calc
    ‖T r.1 r.2-T p.1 p.2‖ ≤ ‖T r.1 (r.2-p.2)‖+‖T r.1 p.2-T p.1 p.2‖ := by
      rw [map_sub]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C*‖r.2-p.2‖+‖T r.1 p.2-T p.1 p.2‖ := by
      gcongr
      exact (T r.1).le_opNorm_of_le (le_rfl) |>.trans (mul_le_mul_of_nonneg_right (hCb _ hrb) (norm_nonneg _))
    _ ≤ (C+1)*‖r.2-p.2‖+‖T r.1 p.2-T p.1 p.2‖ := by gcongr; linarith
    _ < (C+1)*(ε/(2*(C+1)))+ε/2 := by gcongr; simpa only [dist_eq_norm] using hd2
    _=ε := by field_simp; ring
include hc in
lemma continuous_action_clamp : Continuous (fun p : ℝ × E => T (max 0 p.1) p.2) := by
  apply continuousOn_univ.mp
  exact (continuousOn_action T hc).comp
    ((continuous_const.max continuous_fst).prodMk continuous_snd).continuousOn
    (fun p _ => ⟨show (0:ℝ) ≤ max 0 p.1 from le_max_left _ _,mem_univ _⟩)
end AncientMild

end

end OAI
