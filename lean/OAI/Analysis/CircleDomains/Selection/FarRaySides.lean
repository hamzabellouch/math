import OAI.Analysis.CircleDomains.Topology.RayJordanSides
import OAI.Analysis.CircleDomains.Selection.VerticalRayAvoidance

namespace OAI

/-! Uniform eventual values of the translated side functions on bounded
rectangles of the half-plane. This gives the finite range of possible indices. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

namespace HalfPlaneRay

theorem side_eq_boundary_of_vertical_avoidance (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ}
    (hH : R.IsJordan H) (x y : ℝ) (hy : 0 ≤ y)
    (hmiss : Disjoint (range (verticalCayleyPath x y hy)) (range R.crosscut)) :
    (if halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∈ closure (jordanInterior H)
      then false else true) = if x ≤ (R.curve ⟨0, bot_lt_top⟩).re then false else true := by
  have hm (t : PathTime) : verticalCayleyPath x y hy t ∉ range R.crosscut :=
    Set.disjoint_left.mp hmiss (mem_range_self t)
  let f : PathTime → R.CutDomain := fun t =>
    ⟨verticalCayleyPath x y hy t, Metric.mem_closedBall.mpr
      (by simpa only [dist_zero_right] using verticalCayleyPath_norm_le x y hy t), hm t⟩
  have hc : Continuous f := (verticalCayleyPath x y hy).continuous.subtype_mk _
  have he := ((R.isLocallyConstant_side hH).comp_continuous hc).apply_eq_of_preconnectedSpace
    (1 : PathTime) 0
  have h0 : halfPlaneDisk x ∉ range R.crosscut := by simpa only [verticalCayleyPath_zero] using hm 0
  have hb := R.side_boundary hH x h0
  have he' : (if halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∈ closure (jordanInterior H)
      then false else true) = (if halfPlaneDisk x ∈ closure (jordanInterior H) then false else true) := by
    simpa only [Function.comp_apply, side, f, verticalCayleyPath_zero, verticalCayleyPath_one] using he
  exact he'.trans hb

end HalfPlaneRay

theorem translated_sides_eventually_fixed
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ∃ N : ℝ, 0 < N ∧ ∀ (γ : K) (x y : ℝ), |x| ≤ X → ∀ _hy : 0 ≤ y, y ≤ Y →
      ∀ (k : ℤ) (H : ℂ ≃ₜ ℂ), (translatedHalfPlaneRay γ.val (hKS γ.property) k).IsJordan H →
      (N < (k : ℝ) → halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∈ closure (jordanInterior H)) ∧
      ((k : ℝ) < -N → halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∉ closure (jordanInterior H)) := by
  obtain ⟨M, hM⟩ := verticalCayleyPath_common_strip_bound K hK hKS Y
  obtain ⟨A, hA⟩ := compact_disk_rays_angle_bound_on_strip K hK hKS Y
  let N := |M| + |A| + X + 2
  refine ⟨N, by dsimp [N]; positivity, ?_⟩
  intro γ x y hx hy hyY k H hH
  have hzero : diskRayDepth γ.val ⟨0, bot_lt_top⟩ = 0 := by
    simp only [diskRayDepth, (hKS γ.property).2.1, Real.log_one, neg_zero]
  have ha := hA γ ⟨0, bot_lt_top⟩ (by simpa only [hzero] using hY)
  have hlo : -|A| ≤ diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨0, bot_lt_top⟩ :=
    (abs_le.mp ha).1.trans' (neg_le_neg (le_abs_self A))
  have hhi : diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨0, bot_lt_top⟩ ≤ |A| :=
    (abs_le.mp ha).2.trans (le_abs_self A)
  have hstart : ((translatedHalfPlaneRay γ.val (hKS γ.property) k).curve ⟨0, bot_lt_top⟩).re =
      diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨0, bot_lt_top⟩ + (k : ℝ) := by
    simp [translatedHalfPlaneRay, diskRayComplex]
  have hside (hk : M < |x - (k : ℝ)|) := by
    have hmiss : Disjoint (range (verticalCayleyPath x y hy))
        (range (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut) := by
      by_contra hn
      exact (not_le_of_gt hk) (hM x y hy hyY γ k hn)
    exact HalfPlaneRay.side_eq_boundary_of_vertical_avoidance _ hH x y hy hmiss
  constructor
  · intro hk
    have hlarge : M < |x - (k : ℝ)| := by
      have hab := neg_le_abs (x - (k : ℝ))
      have hm := le_abs_self M
      have hx' := (abs_le.mp hx).2
      dsimp [N] at hk
      linarith [abs_nonneg A]
    have hs := hside hlarge
    have hle : x ≤ ((translatedHalfPlaneRay γ.val (hKS γ.property) k).curve ⟨0, bot_lt_top⟩).re := by
      rw [hstart]
      have hx' := (abs_le.mp hx).2
      dsimp [N] at hk
      linarith [abs_nonneg M]
    simp only [ite_eq_left hle] at hs
    by_contra hn
    simp only [ite_eq_right hn] at hs
    cases hs
  · intro hk
    have hlarge : M < |x - (k : ℝ)| := by
      have hab := le_abs_self (x - (k : ℝ))
      have hm := le_abs_self M
      have hx' := (abs_le.mp hx).1
      dsimp [N] at hk
      linarith [abs_nonneg A]
    have hs := hside hlarge
    have hlt : ((translatedHalfPlaneRay γ.val (hKS γ.property) k).curve ⟨0, bot_lt_top⟩).re < x := by
      rw [hstart]
      have hx' := (abs_le.mp hx).1
      dsimp [N] at hk
      linarith [abs_nonneg M]
    simp only [ite_eq_right (not_le_of_gt hlt)] at hs
    intro hin
    simp only [ite_eq_left hin] at hs
    cases hs

end CircleDomainRigidity

end

end OAI
