import OAI.Analysis.CircleDomains.Topology.CrosscutPathSides
import OAI.Analysis.CircleDomains.Selection.RayIndexCrossings
import OAI.Analysis.CircleDomains.Topology.HalfPlaneDiskInverse

namespace OAI

/-! The side path test in the original half-plane coordinates. -/

open Set Function Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def HalfPlaneAvoidingPath (R : HalfPlaneRay) (z w : ℂ) : Prop :=
  ∃ δ : C(PathTime, ℂ), δ 0 = z ∧ δ 1 = w ∧
    ∀ t, 0 ≤ (δ t).im ∧ δ t ∉ range R.curve

 theorem HalfPlaneRay.diskAvoiding_iff_halfPlaneAvoiding (R : HalfPlaneRay)
    {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    DiskAvoidingPath R.crosscut.toContinuousMap (halfPlaneDisk z) (halfPlaneDisk w) ↔
      HalfPlaneAvoidingPath R z w := by
  constructor
  · rintro ⟨δ, h0, h1, hδ⟩
    have hne : ∀ t, δ t ≠ 1 := by
      intro t ht
      apply (hδ t).2
      exact ⟨⊤, R.compactify_top.trans ht.symm⟩
    let ε : C(PathTime, ℂ) := ⟨diskHalfPlane ∘ δ,
      continuousOn_diskHalfPlane.comp_continuous δ.continuous hne⟩
    refine ⟨ε, ?_, ?_, ?_⟩
    · change diskHalfPlane (δ 0) = z
      rw [h0, diskHalfPlane_halfPlaneDisk hz]
    · change diskHalfPlane (δ 1) = w
      rw [h1, diskHalfPlane_halfPlaneDisk hw]
    · intro t
      have hn : ‖δ t‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using (hδ t).1
      refine ⟨diskHalfPlane_nonneg (hne t) hn, ?_⟩
      rintro ⟨s, hs⟩
      apply (hδ t).2
      have he : δ t = halfPlaneDisk (R.curve s) := by
        rw [← halfPlaneDisk_diskHalfPlane (hne t)]
        exact congrArg halfPlaneDisk hs.symm
      rw [he]
      exact (R.cayley_mem_crosscut_iff (R.nonneg s)).mpr (mem_range_self s)
  · rintro ⟨δ, h0, h1, hδ⟩
    let ε : C(PathTime, ℂ) := ⟨halfPlaneDisk ∘ δ,
      continuousOn_halfPlaneDisk.comp_continuous δ.continuous (fun t => (hδ t).1)⟩
    refine ⟨ε, congrArg halfPlaneDisk h0, congrArg halfPlaneDisk h1, ?_⟩
    intro t
    refine ⟨Metric.mem_closedBall.mpr ?_, ?_⟩
    · simpa only [ε, ContinuousMap.coe_mk, Function.comp_apply, dist_zero_right] using
        halfPlaneDisk_norm_le (hδ t).1
    · exact fun hm => (hδ t).2 ((R.cayley_mem_crosscut_iff (hδ t).1).mp hm)

 theorem HalfPlaneRay.right_iff_halfPlanePath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) {z : ℂ} (hz : 0 ≤ z.im) :
    halfPlaneDisk z ∉ closure (jordanInterior H) ↔ HalfPlaneAvoidingPath R z
      (((R.curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ) := by
  rw [R.right_iff_avoidingPath hsep hH
    (Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le hz))]
  exact R.diskAvoiding_iff_halfPlaneAvoiding hz (by simp)

 theorem HalfPlaneRay.translated_right (hsep : UnitDiskCrosscutSeparation)
    (R S : HalfPlaneRay) {H J : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (hJ : S.IsJordan J)
    (a : ℝ) (ha : ∀ t, S.curve t = R.curve t + (a : ℂ))
    {z : ℂ} (hz : 0 ≤ z.im) (hr : halfPlaneDisk z ∉ closure (jordanInterior H)) :
    halfPlaneDisk (z + (a : ℂ)) ∉ closure (jordanInterior J) := by
  have hza : 0 ≤ (z + (a : ℂ)).im := by simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hz
  apply (S.right_iff_halfPlanePath hsep hJ hza).mpr
  obtain ⟨δ, h0, h1, hδ⟩ := (R.right_iff_halfPlanePath hsep hH hz).mp hr
  refine ⟨⟨fun t => δ t + (a : ℂ), δ.continuous.add continuous_const⟩,
    congrArg (fun w => w + (a : ℂ)) h0, ?_, ?_⟩
  · change δ 1 + (a : ℂ) = _
    rw [h1, ha, Complex.add_re, Complex.ofReal_re]
    push_cast
    ring
  · intro t
    refine ⟨?_, ?_⟩
    · simpa only [ContinuousMap.coe_mk, Complex.add_im, Complex.ofReal_im, add_zero] using (hδ t).1
    · rintro ⟨s, hs⟩
      rw [ha s] at hs
      exact (hδ t).2 ⟨s, add_right_cancel hs⟩

end CircleDomainRigidity

end

end OAI
