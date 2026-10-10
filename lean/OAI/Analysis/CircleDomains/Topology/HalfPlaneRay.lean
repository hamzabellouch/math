import OAI.Analysis.CircleDomains.Topology.DiskRayCrosscut
import OAI.Analysis.CircleDomains.Topology.BoundaryClosingArc

namespace OAI

/-! Compactification of the integer translates of a lifted ray. The curve
escapes in height, so the added endpoint is the single boundary point 1. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

structure HalfPlaneRay where
  curve : C(DiskRayTime, ℂ)
  injective : Injective curve
  nonneg : ∀ t, 0 ≤ (curve t).im
  start : (curve ⟨0, bot_lt_top⟩).im = 0
  positive : ∀ t : DiskRayTime, 0 < t.val → 0 < (curve t).im
  escape : ∀ Y : ℝ, ∃ c : PathTime, c < 1 ∧ ∀ t : DiskRayTime, c ≤ t.val → Y < (curve t).im

def HalfPlaneRay.compactify (R : HalfPlaneRay) (t : PathTime) : ℂ :=
  if ht : t < ⊤ then halfPlaneDisk (R.curve ⟨t, ht⟩) else 1

@[simp] theorem HalfPlaneRay.compactify_top (R : HalfPlaneRay) : R.compactify ⊤ = 1 := by
  simp only [HalfPlaneRay.compactify, lt_self_iff_false, dite_false]

theorem HalfPlaneRay.continuousOn_compactify (R : HalfPlaneRay) :
    ContinuousOn R.compactify (Iio ⊤) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc := continuousOn_halfPlaneDisk.comp_continuous R.curve.continuous R.nonneg
  apply hc.congr
  intro t
  change halfPlaneDisk (R.curve t) = R.compactify t.val
  simp only [HalfPlaneRay.compactify, dite_eq_left t.property]

theorem HalfPlaneRay.continuousAt_compactify_top (R : HalfPlaneRay) :
    ContinuousAt R.compactify ⊤ := by
  rw [ContinuousAt, R.compactify_top]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨c, hc, htail⟩ := R.escape (2 / ε)
  filter_upwards [Ioi_mem_nhds (show c < (⊤ : PathTime) from hc)] with t ht
  by_cases htt : t < ⊤
  · rw [HalfPlaneRay.compactify, dite_eq_left htt]
    have hy := htail ⟨t, htt⟩ ht.le
    apply (halfPlaneDisk_dist_one_le (R.nonneg ⟨t, htt⟩)).trans_lt
    apply (div_lt_iff₀ (show 0 < (R.curve ⟨t, htt⟩).im + 1 by linarith [R.nonneg ⟨t, htt⟩])).mpr
    have hy' : 2 < (R.curve ⟨t, htt⟩).im * ε := (div_lt_iff₀ hε).mp hy
    nlinarith
  · simp only [HalfPlaneRay.compactify, htt, dite_false, dist_self, hε]

theorem HalfPlaneRay.continuous_compactify (R : HalfPlaneRay) : Continuous R.compactify := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t < ⊤
  · exact R.continuousOn_compactify.continuousAt (isOpen_Iio.mem_nhds ht)
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    exact R.continuousAt_compactify_top

theorem HalfPlaneRay.compactify_injective (R : HalfPlaneRay) : Injective R.compactify := by
  intro s t h
  by_cases hs : s < ⊤
  · by_cases ht : t < ⊤
    · rw [HalfPlaneRay.compactify, dite_eq_left hs, HalfPlaneRay.compactify, dite_eq_left ht] at h
      exact congrArg Subtype.val (R.injective (halfPlaneDisk_injOn (R.nonneg _) (R.nonneg _) h))
    · rw [HalfPlaneRay.compactify, dite_eq_left hs, HalfPlaneRay.compactify, dite_eq_right ht] at h
      exact (halfPlaneDisk_ne_one (R.nonneg _) h).elim
  · by_cases ht : t < ⊤
    · rw [HalfPlaneRay.compactify, dite_eq_right hs, HalfPlaneRay.compactify, dite_eq_left ht] at h
      exact (halfPlaneDisk_ne_one (R.nonneg _) h.symm).elim
    · exact (top_le_iff.mp (not_lt.mp hs)).trans (top_le_iff.mp (not_lt.mp ht)).symm

def HalfPlaneRay.crosscut (R : HalfPlaneRay) : Path (R.compactify 0) 1 where
  toFun := R.compactify
  continuous_toFun := R.continuous_compactify
  source' := rfl
  target' := R.compactify_top

theorem HalfPlaneRay.crosscut_start_norm (R : HalfPlaneRay) : ‖R.compactify 0‖ = 1 := by
  have ht : (0 : PathTime) < ⊤ := bot_lt_top
  rw [HalfPlaneRay.compactify, dite_eq_left ht]
  exact halfPlaneDisk_norm_eq R.start

theorem HalfPlaneRay.crosscut_start_ne (R : HalfPlaneRay) : R.compactify 0 ≠ 1 := by
  rw [← R.compactify_top]
  exact fun h => zero_ne_one (R.compactify_injective h)

theorem HalfPlaneRay.crosscut_interior (R : HalfPlaneRay) (t : PathTime)
    (ht : t ∈ Ioo 0 1) : ‖R.crosscut t‖ < 1 := by
  change ‖R.compactify t‖ < 1
  have ht' : t < ⊤ := ht.2
  rw [HalfPlaneRay.compactify, dite_eq_left ht']
  exact halfPlaneDisk_norm_lt (R.positive ⟨t, ht.2⟩ ht.1)

theorem HalfPlaneRay.exists_schoenflies (R : HalfPlaneRay) (hsch : PlanarSchoenflies) :
    ∃ H : ℂ ≃ₜ ℂ, ∀ z : Circle,
      H z = circleOfClosedPath (R.crosscut.trans
        (boundaryClosingArc _ R.crosscut_start_norm))
        ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z) :=
  exists_schoenflies_of_disk_crosscut hsch R.crosscut R.compactify_injective
    R.crosscut_interior R.crosscut_start_norm R.crosscut_start_ne

def translatedHalfPlaneRay (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (k : ℤ) : HalfPlaneRay where
  curve := ⟨fun t => diskRayComplex γ hγ.1 hγ.2.2.1 t + (k : ℂ),
    (diskRayComplex γ hγ.1 hγ.2.2.1).continuous.add continuous_const⟩
  injective := fun _ _ h => diskRayComplex_injective γ hγ.1 hγ.2.2.1 (add_right_cancel h)
  nonneg := by
    intro t
    simpa only [ContinuousMap.coe_mk, Complex.add_im, Complex.intCast_im, add_zero, diskRayComplex_im] using diskRayDepth_nonneg hγ t
  start := by
    simp only [ContinuousMap.coe_mk, Complex.add_im, Complex.intCast_im, add_zero, diskRayComplex_im,
      diskRayDepth]
    rw [hγ.2.1, Real.log_one, neg_zero]
  positive := by
    intro t ht
    simp only [ContinuousMap.coe_mk, Complex.add_im, Complex.intCast_im, add_zero, diskRayComplex_im]
    have hp : 0 < ‖γ t.val‖ := norm_pos_iff.mpr (diskRay_nonzero γ hγ.1 hγ.2.2.1 t)
    have hlt := Real.log_lt_log hp (hγ.2.2.2 t.val ⟨ht, t.property⟩)
    rw [Real.log_one] at hlt
    exact neg_pos.mpr hlt
  escape := by
    intro Y
    obtain ⟨c, _, hc, hh⟩ := compact_disk_rays_depth_escape {γ} isCompact_singleton
      (by simpa only [singleton_subset_iff] using hγ) Y
    refine ⟨c, hc, fun t ht => ?_⟩
    simpa only [ContinuousMap.coe_mk, Complex.add_im, Complex.intCast_im, add_zero, diskRayComplex_im]
      using hh γ (mem_singleton γ) t ht

theorem translatedHalfPlaneRay_meet_iff (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k l : ℤ) (s t : DiskRayTime) :
    (translatedHalfPlaneRay γ hγ k).curve s = (translatedHalfPlaneRay γ hγ l).curve t ↔
      k = l ∧ s = t := by
  have he : ((translatedHalfPlaneRay γ hγ k).curve s = (translatedHalfPlaneRay γ hγ l).curve t) ↔
      translatedDiskRay γ hγ.1 hγ.2.2.1 k s = translatedDiskRay γ hγ.1 hγ.2.2.1 l t := by
    constructor
    · intro h
      apply Prod.ext
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Complex.re h
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Complex.im h
    · intro h
      apply Complex.ext
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Prod.fst h
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Prod.snd h
  exact he.trans (translatedDiskRay_eq_iff γ hγ.1 hγ.2.2.1 k l s t)

end CircleDomainRigidity

end

end OAI
