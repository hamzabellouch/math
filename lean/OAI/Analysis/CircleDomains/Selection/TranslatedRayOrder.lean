import OAI.Analysis.CircleDomains.Topology.GeometricIndexBoundary
import OAI.Analysis.CircleDomains.Selection.RaySideConnectivity

namespace OAI

/-! The side of one translated ray relative to another is fixed by their
starting order on the real boundary. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem translated_curve_avoids_crosscut (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) {k l : ℤ} (hkl : k ≠ l) (t : DiskRayTime) :
    halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∉
      range (translatedHalfPlaneRay γ hγ k).crosscut := by
  let R := translatedHalfPlaneRay γ hγ k
  let S := translatedHalfPlaneRay γ hγ l
  rintro ⟨s, hs⟩
  have hst : s < ⊤ := by
    by_contra hn
    have he : s = ⊤ := top_le_iff.mp (not_lt.mp hn)
    subst s
    change R.compactify ⊤ = halfPlaneDisk (S.curve t) at hs
    rw [R.compactify_top] at hs
    exact halfPlaneDisk_ne_one (S.nonneg t) hs.symm
  change R.compactify s = halfPlaneDisk (S.curve t) at hs
  rw [HalfPlaneRay.compactify, dite_eq_left hst] at hs
  have hc := halfPlaneDisk_injOn (R.nonneg ⟨s, hst⟩) (S.nonneg t) hs
  exact hkl ((translatedHalfPlaneRay_meet_iff γ hγ k l ⟨s, hst⟩ t).mp hc).1

theorem translated_ray_side_value (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) {k l : ℤ} (hkl : k ≠ l)
    (H : ℂ ≃ₜ ℂ) (hH : (translatedHalfPlaneRay γ hγ k).IsJordan H) (t : DiskRayTime) :
    (if halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∈ closure (jordanInterior H)
      then false else true) = if l ≤ k then false else true := by
  let R := translatedHalfPlaneRay γ hγ k
  let S := translatedHalfPlaneRay γ hγ l
  let f : DiskRayTime → R.CutDomain := fun u => ⟨halfPlaneDisk (S.curve u),
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le (S.nonneg u)),
    translated_curve_avoids_crosscut γ hγ hkl u⟩
  have hc : Continuous f := by
    apply Continuous.subtype_mk
    exact continuousOn_halfPlaneDisk.comp_continuous S.curve.continuous S.nonneg
  let : PreconnectedSpace DiskRayTime := Subtype.preconnectedSpace
    (isPreconnected_Iio (a := (⊤ : PathTime)))
  have he := ((R.isLocallyConstant_side hH).comp_continuous hc).apply_eq_of_preconnectedSpace
    t (⟨0, bot_lt_top⟩ : DiskRayTime)
  have hs0 : S.curve ⟨0, bot_lt_top⟩ = ((S.curve ⟨0, bot_lt_top⟩).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using S.start
  have hm : halfPlaneDisk ((S.curve ⟨0, bot_lt_top⟩).re : ℂ) ∉ range R.crosscut := by
    rw [← hs0]
    exact translated_curve_avoids_crosscut γ hγ hkl ⟨0, bot_lt_top⟩
  have hb := R.side_boundary hH (S.curve ⟨0, bot_lt_top⟩).re hm
  have he' : (if halfPlaneDisk (S.curve t) ∈ closure (jordanInterior H) then false else true) =
      (if halfPlaneDisk ((S.curve ⟨0, bot_lt_top⟩).re : ℂ) ∈ closure (jordanInterior H) then false else true) := by
    change (if halfPlaneDisk (S.curve t) ∈ closure (jordanInterior H) then false else true) =
      (if halfPlaneDisk (S.curve ⟨0, bot_lt_top⟩) ∈ closure (jordanInterior H) then false else true) at he
    rw [hs0] at he
    exact he
  have hle : (S.curve ⟨0, bot_lt_top⟩).re ≤ (R.curve ⟨0, bot_lt_top⟩).re ↔ l ≤ k := by
    simp only [S, R, translatedHalfPlaneRay, ContinuousMap.coe_mk, Complex.add_re,
      diskRayComplex, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.intCast_re,
      add_le_add_iff_left, Int.cast_le]
  exact he'.trans (hb.trans (by simp only [hle]))

theorem later_ray_right (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {k l : ℤ} (hkl : k < l) (H : ℂ ≃ₜ ℂ)
    (hH : (translatedHalfPlaneRay γ hγ k).IsJordan H) (t : DiskRayTime) :
    halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∉ closure (jordanInterior H) := by
  have h := translated_ray_side_value γ hγ hkl.ne H hH t
  rw [ite_eq_right (not_le_of_gt hkl)] at h
  intro hi
  rw [ite_eq_left hi] at h
  cases h

theorem earlier_ray_left (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {k l : ℤ} (hlk : l < k) (H : ℂ ≃ₜ ℂ)
    (hH : (translatedHalfPlaneRay γ hγ k).IsJordan H) (t : DiskRayTime) :
    halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∈ closure (jordanInterior H) := by
  have h := translated_ray_side_value γ hγ hlk.ne' H hH t
  rw [ite_eq_left hlk.le] at h
  by_contra hi
  rw [ite_eq_right hi] at h
  cases h

end CircleDomainRigidity

end

end OAI
