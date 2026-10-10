import OAI.Analysis.CircleDomains.Selection.MeanGeometricIndex

namespace OAI

/-! Near an interior point, a simple lifted ray has index jump at most
one. The jump is zero when the projected point misses the arc. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem geometricRayIndex_on_translated_ray
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) (t : DiskRayTime) :
    geometricRayIndex hsch γ hγ ((translatedHalfPlaneRay γ hγ k).curve t) = k - 1 := by
  let z := (translatedHalfPlaneRay γ hγ k).curve t
  have hz : 0 ≤ z.im := (translatedHalfPlaneRay γ hγ k).nonneg t
  have hlo : k - 1 ≤ geometricRayIndex hsch γ hγ z := by
    apply (mem_rayRightIndices_iff_le hsch hsep γ hγ z hz (k - 1)).mp
    exact later_ray_right γ hγ (by omega) _ (rayJordan_spec hsch γ hγ (k - 1)) t
  have hnot : k ∉ rayRightIndices hsch γ hγ z := by
    intro hk
    apply hk
    apply frontier_subset_closure
    rw [rayJordan_spec hsch γ hγ k]
    left
    exact ⟨t.val, by
      change (translatedHalfPlaneRay γ hγ k).compactify t.val = halfPlaneDisk z
      rw [HalfPlaneRay.compactify, dite_eq_left t.property]⟩
  have hhi : ¬ k ≤ geometricRayIndex hsch γ hγ z :=
    fun hk => hnot ((mem_rayRightIndices_iff_le hsch hsep γ hγ z hz k).mpr hk)
  change geometricRayIndex hsch γ hγ z = k - 1
  omega

 theorem rayInterior_of_index_lt_of_avoids
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {z : ℂ} (hz : 0 < z.im) (k : ℤ) (hk : geometricRayIndex hsch γ hγ z < k)
    (hmiss : halfPlaneDisk z ∉ range (translatedHalfPlaneRay γ hγ k).crosscut) :
    halfPlaneDisk z ∈ jordanInterior (rayJordan hsch γ hγ k) := by
  have hcl : halfPlaneDisk z ∈ closure (jordanInterior (rayJordan hsch γ hγ k)) := by
    by_contra hn
    exact (not_le_of_gt hk)
      ((mem_rayRightIndices_iff_le hsch hsep γ hγ z hz.le k).mp hn)
  by_contra hi
  have hfront : halfPlaneDisk z ∈ frontier (jordanInterior (rayJordan hsch γ hγ k)) := by
    rw [(jordanInterior_isOpen _).frontier_eq]
    exact ⟨hcl, hi⟩
  rw [rayJordan_spec hsch γ hγ k] at hfront
  rcases hfront with hc | ⟨t, ht⟩
  · exact hmiss hc
  · have hn := halfPlaneDisk_norm_lt hz
    rw [← ht, boundaryClosingArc_norm] at hn
    exact lt_irrefl _ hn

 theorem eventually_geometricRayIndex_bounds
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ClosedUpperHalfPlane) (hz : 0 < z.val.im) :
    ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z,
      geometricRayIndex hsch γ hγ z.val ≤ geometricRayIndex hsch γ hγ w.val ∧
      geometricRayIndex hsch γ hγ w.val ≤ geometricRayIndex hsch γ hγ z.val +
        if diskRayProjection z.val ∈ range γ then 1 else 0 := by
  let n := geometricRayIndex hsch γ hγ z.val
  let k := n + if diskRayProjection z.val ∈ range γ then 2 else 1
  have hnk : n < k := by dsimp [k]; split_ifs <;> omega
  have hmiss : halfPlaneDisk z.val ∉ range (translatedHalfPlaneRay γ hγ k).crosscut := by
    intro hh
    obtain ⟨t, ht⟩ := ((translatedHalfPlaneRay γ hγ k).cayley_mem_crosscut_iff z.property).mp hh
    have hidx := geometricRayIndex_on_translated_ray hsch hsep γ hγ k t
    rw [ht] at hidx
    have hhit : diskRayProjection z.val ∈ range γ := by
      refine ⟨t.val, ?_⟩
      rw [← diskRayProjection_translated γ hγ k t, ht]
    dsimp [k] at hidx
    rw [ite_eq_left hhit] at hidx
    dsimp [n] at hidx
    omega
  have hleft := rayInterior_of_index_lt_of_avoids hsch hsep γ hγ hz k hnk hmiss
  have hright : halfPlaneDisk z.val ∉ closure (jordanInterior (rayJordan hsch γ hγ n)) :=
    (geometricRayIndex_isGreatest hsch γ hγ z.val z.property).1
  have hD : Continuous (fun w : ClosedUpperHalfPlane => halfPlaneDisk w.val) :=
    continuousOn_halfPlaneDisk.comp_continuous continuous_subtype_val (fun w => w.property)
  have hnearlo := hD.continuousAt.eventually (isClosed_closure.isOpen_compl.mem_nhds hright)
  have hnearhi := hD.continuousAt.eventually ((jordanInterior_isOpen _).mem_nhds hleft)
  filter_upwards [hnearlo, hnearhi] with w hwlo hwhi
  refine ⟨(mem_rayRightIndices_iff_le hsch hsep γ hγ w.val w.property n).mp hwlo, ?_⟩
  have hlt : geometricRayIndex hsch γ hγ w.val < k := by
    by_contra hn
    have hm := (mem_rayRightIndices_iff_le hsch hsep γ hγ w.val w.property k).mpr
      (le_of_not_gt hn)
    exact hm (subset_closure hwhi)
  dsimp [k] at hlt
  dsimp [n] at *
  split_ifs at * <;> omega

 theorem eventually_geometricRayIndex_pair_difference
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ClosedUpperHalfPlane) (hz : 0 < z.val.im) :
    ∀ᶠ p : ClosedUpperHalfPlane × ClosedUpperHalfPlane in 𝓝 (z, z),
      |(geometricRayIndex hsch γ hγ p.1.val : ℝ) -
        (geometricRayIndex hsch γ hγ p.2.val : ℝ)| ≤
          if diskRayProjection z.val ∈ range γ then 1 else 0 := by
  have hb := eventually_geometricRayIndex_bounds hsch hsep γ hγ z hz
  have h₁ := (continuous_fst.tendsto (z, z)).eventually hb
  have h₂ := (continuous_snd.tendsto (z, z)).eventually hb
  filter_upwards [h₁, h₂] with p hp hq
  split_ifs at * with hhit
  · apply abs_le.mpr
    constructor
    · have h : -(1 : ℤ) ≤ geometricRayIndex hsch γ hγ p.1.val - geometricRayIndex hsch γ hγ p.2.val := by omega
      exact_mod_cast h
    · have h : geometricRayIndex hsch γ hγ p.1.val - geometricRayIndex hsch γ hγ p.2.val ≤ (1 : ℤ) := by omega
      exact_mod_cast h
  · have he : geometricRayIndex hsch γ hγ p.1.val =
        geometricRayIndex hsch γ hγ p.2.val := by omega
    simp only [he, sub_self, abs_zero, le_refl]

end CircleDomainRigidity

end

end OAI
