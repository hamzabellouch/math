import OAI.Probability.RadialTransition.PhaseGeometry

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma support_ball_of_groups {Q : Pressure} {x : Parameter} {r : ℝ}
    (hgroup : HasPhaseGroups Q x r) (hr : r ≤ phaseRadius)
    (hg : targetSlope ∈ supportSet (onParameters Q) positiveParameters x) :
    Metric.closedBall targetSlope pressureRadius ⊆ supportSet (onParameters Q) positiveParameters x := by
  classical
  let S := supportSet (onParameters Q) positiveParameters x
  have hex (i : Fin 3) : ∃ w ∈ S, w ∈ Metric.closedBall (phaseSlope i) phaseRadius := by
    by_contra hn
    let n := exclusionNormal i
    let c := inner ℝ targetSlope n-packingDensity/2
    let H : Set Parameter := {v | inner ℝ v n ≤ c}
    have hc : Convex ℝ H := by
      intro v hv w hw a b ha hb hab
      change inner ℝ (a • v+b • w) n ≤ c
      rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
      have hh := add_le_add (mul_le_mul_of_nonneg_left hv ha) (mul_le_mul_of_nonneg_left hw hb)
      calc
        _ ≤ a*c+b*c := hh
        _ = c := by rw [← add_mul,hab,one_mul]
    have hclosed : IsClosed H := isClosed_le (continuous_id.inner continuous_const) continuous_const
    have hSH : S ⊆ H := by
      change supportSet (onParameters Q) positiveParameters x ⊆ H
      rw [hgroup]
      apply closure_minimal _ hclosed
      apply convexHull_min _ hc
      rintro v ⟨hv,j,hj⟩
      have hj' := Metric.closedBall_subset_closedBall hr hj
      have hij : j ≠ i := by
        intro heq
        exact hn ⟨v,hv,heq ▸ hj'⟩
      exact exclusion_ball i j hij hj'
    have hh := hSH hg
    change inner ℝ targetSlope n ≤ inner ℝ targetSlope n-packingDensity/2 at hh
    linarith [packingDensity_pos]
  choose w hw hwball using hex
  intro v hv
  have htri := robust_phase_triangle w hwball hv
  have hsub : closure (convexHull ℝ (range w)) ⊆ S := by
    apply closure_minimal _ (isClosed_supportSet _ _ _)
    apply convexHull_min _ (convex_supportSet _ _ _)
    rintro _ ⟨i,rfl⟩
    exact hw i
  exact hsub htri

lemma pressure_ball_exists {Q : Pressure}
    (hQ : ConvexOn ℝ positiveParameters (onParameters Q))
    (hclose : ∀ x ∈ phaseWindow (1/8), |onParameters Q x-onParameters threePlane x| ≤ pressureRadius/32)
    (hgroups : ∀ x ∈ phaseWindow (1/8), ∃ r ≤ phaseRadius, HasPhaseGroups Q x r) :
    ∃ x ∈ Metric.ball phaseCenter (1/8),
      Metric.closedBall targetSlope pressureRadius ⊆ supportSet (onParameters Q) positiveParameters x := by
  have hW : phaseWindow (1/8) ⊆ positiveParameters := by
    intro x hx
    exact phaseWindow_positive (by norm_num) hx
  have hQc := hQ.continuousOn isOpen_positiveParameters
  let F : Parameter → ℝ := fun x => onParameters Q x-inner ℝ targetSlope x
  have hFc : ContinuousOn F (phaseWindow (1/8)) :=
    (hQc.mono hW).sub (continuous_const.inner continuous_id).continuousOn
  have hcenter : phaseCenter ∈ phaseWindow (1/8) := Metric.mem_closedBall_self (by norm_num)
  obtain ⟨x,hx,hmin⟩ := (isCompact_closedBall phaseCenter (1/8)).exists_isMinOn ⟨phaseCenter,hcenter⟩ hFc
  have hdist : dist x phaseCenter < 1/8 := by
    by_contra hh
    have hxbound := Metric.mem_closedBall.mp hx
    have heq : dist x phaseCenter=1/8 := le_antisymm hxbound (le_of_not_gt hh)
    have hgrow := threePlane_growth x
    rw [← dist_eq_norm,heq] at hgrow
    have ha := abs_le.mp (hclose x hx)
    have hb := abs_le.mp (hclose phaseCenter hcenter)
    have hm := hmin hcenter
    dsimp [F] at hm
    rw [inner_sub_right] at hgrow
    linarith [pressureRadius_pos]
  have hg : targetSlope ∈ supportSet (onParameters Q) positiveParameters x := by
    apply supportsOn_of_local hQ (hW hx) (sub_pos.mpr hdist)
    intro y hy
    have hyW : y ∈ phaseWindow (1/8) := by
      change dist y phaseCenter ≤ 1/8
      calc
        _ ≤ dist y x+dist x phaseCenter := dist_triangle _ _ _
        _ ≤ 1/8 := by have ht := Metric.mem_closedBall.mp hy.2; linarith
    have hm := hmin hyW
    dsimp [F] at hm
    rw [inner_sub_right]
    linarith
  obtain ⟨r,hr,hgrp⟩ := hgroups x hx
  exact ⟨x,hdist,support_ball_of_groups hgrp hr hg⟩

end RadialTransition
end

end OAI
