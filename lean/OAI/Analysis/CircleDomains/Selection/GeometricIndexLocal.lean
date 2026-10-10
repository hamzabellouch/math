import OAI.Analysis.CircleDomains.Selection.GeometricRayIndex

namespace OAI

/-! Local constancy of the greatest-translate index follows from the common
finite strip bound and local constancy of each of the finitely many relevant sides. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

abbrev RayIndexDomain (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) :=
  {z : ℂ // 0 ≤ z.im ∧ ∀ k : ℤ, halfPlaneDisk z ∉ range (translatedHalfPlaneRay γ hγ k).crosscut}

def rayIndexSide (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) (z : RayIndexDomain γ hγ) : Bool :=
  (translatedHalfPlaneRay γ hγ k).side (rayJordan hsch γ hγ k)
    ⟨halfPlaneDisk z.val, Metric.mem_closedBall.mpr
      (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le z.property.1), z.property.2 k⟩

theorem isLocallyConstant_rayIndexSide (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) :
    IsLocallyConstant (rayIndexSide hsch γ hγ k) := by
  have hc : Continuous (fun z : RayIndexDomain γ hγ => halfPlaneDisk z.val) :=
    continuousOn_halfPlaneDisk.comp_continuous continuous_subtype_val (fun z => z.property.1)
  exact ((translatedHalfPlaneRay γ hγ k).isLocallyConstant_side
    (rayJordan_spec hsch γ hγ k)).comp_continuous (hc.subtype_mk _)

theorem rayIndexSide_eq_true_iff (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) (z : RayIndexDomain γ hγ) :
    rayIndexSide hsch γ hγ k z = true ↔ k ∈ rayRightIndices hsch γ hγ z.val := by
  unfold rayIndexSide HalfPlaneRay.side rayRightIndices
  split_ifs <;> simp_all

theorem isLocallyConstant_geometricRayIndex (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) :
    IsLocallyConstant (fun z : RayIndexDomain γ hγ => geometricRayIndex hsch γ hγ z.val) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro z
  let X := |z.val.re| + 1
  let Y := z.val.im + 1
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; linarith [z.property.1]
  obtain ⟨N, _, hN⟩ := translated_sides_eventually_fixed {γ} isCompact_singleton
    (by simpa only [singleton_subset_iff] using hγ) X Y hX hY
  obtain ⟨B, hB⟩ := exists_int_gt N
  have hfar (w : RayIndexDomain γ hγ) (hwX : |w.val.re| ≤ X) (hwY : w.val.im ≤ Y) (k : ℤ) :
      (N < (k : ℝ) → k ∉ rayRightIndices hsch γ hγ w.val) ∧
      ((k : ℝ) < -N → k ∈ rayRightIndices hsch γ hγ w.val) := by
    have h := hN ⟨γ, mem_singleton γ⟩ w.val.re w.val.im hwX w.property.1 hwY k
      (rayJordan hsch γ hγ k) (rayJordan_spec hsch γ hγ k)
    have he := Complex.re_add_im w.val
    constructor
    · intro hk hm
      exact hm (he ▸ h.1 hk)
    · intro hk
      exact he ▸ h.2 hk
  have hzX : |z.val.re| ≤ X := by dsimp [X]; linarith
  have hzY : z.val.im ≤ Y := by dsimp [Y]; linarith
  have hnearX : ∀ᶠ w : RayIndexDomain γ hγ in 𝓝 z, |w.val.re| ≤ X := by
    have hc : Continuous (fun w : RayIndexDomain γ hγ => |w.val.re|) :=
      (Complex.continuous_re.comp continuous_subtype_val).abs
    have hzlt : |z.val.re| < X := by dsimp [X]; linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hzlt)).mono
      (fun _ h => h.le)
  have hnearY : ∀ᶠ w : RayIndexDomain γ hγ in 𝓝 z, w.val.im ≤ Y := by
    have hc : Continuous (fun w : RayIndexDomain γ hγ => w.val.im) :=
      Complex.continuous_im.comp continuous_subtype_val
    have hzlt : z.val.im < Y := by dsimp [Y]; linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hzlt)).mono
      (fun _ h => h.le)
  have hfinite : ∀ᶠ w : RayIndexDomain γ hγ in 𝓝 z,
      ∀ k : {k : ℤ // k ∈ Icc (-B) B}, rayIndexSide hsch γ hγ k.val w = rayIndexSide hsch γ hγ k.val z := by
    apply Filter.eventually_all.mpr
    intro k
    exact (isLocallyConstant_rayIndexSide hsch γ hγ k.val).eventually_eq z
  filter_upwards [hnearX, hnearY, hfinite] with w hwX hwY hw
  have heq : rayRightIndices hsch γ hγ w.val = rayRightIndices hsch γ hγ z.val := by
    ext k
    by_cases hk : k ∈ Icc (-B) B
    · rw [← rayIndexSide_eq_true_iff, ← rayIndexSide_eq_true_iff, hw ⟨k, hk⟩]
    · have hsplit : k < -B ∨ B < k := by
        simpa only [mem_Icc, not_and_or, not_le] using hk
      rcases hsplit with hleft | hright
      · have hkn : (k : ℝ) < -N := by
          have hk' : (k : ℝ) < (-B : ℤ) := by exact_mod_cast hleft
          rw [Int.cast_neg] at hk'
          linarith
        exact iff_of_true ((hfar w hwX hwY k).2 hkn) ((hfar z hzX hzY k).2 hkn)
      · have hkn : N < (k : ℝ) := hB.trans (by exact_mod_cast hright)
        exact iff_of_false ((hfar w hwX hwY k).1 hkn) ((hfar z hzX hzY k).1 hkn)
  exact congrArg sSup heq

end CircleDomainRigidity

end

end OAI
