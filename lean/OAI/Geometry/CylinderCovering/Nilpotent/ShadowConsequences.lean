import OAI.Geometry.CylinderCovering.Nilpotent.ShadowSimilarity

namespace OAI

noncomputable section
open Set MeasureTheory RuledApproximation
namespace CylinderCovering.Nilpotent

theorem centerMap_shadowArea_range (S : Set Space) :
    {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = shadowArea (centerMap '' S) u} =
      (fun a : ℝ => (1 / 4 : ℝ) * a) ''
        {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = shadowArea S u} := by
  ext a
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨shadowArea S (centerDirection u),
      ⟨centerDirection u, by simpa only [centerDirection_norm] using hu, rfl⟩, ?_⟩
    have h := centerMap_shadowArea S (centerDirection u)
    rw [centerDirection_involutive] at h
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using h.symm
  · rintro ⟨a, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨centerDirection u, by simpa only [centerDirection_norm] using hu, ?_⟩
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (centerMap_shadowArea S u).symm

theorem centerMap_minimumShadowArea (S : Set Space) :
    minimumShadowArea (centerMap '' S) = minimumShadowArea S / 4 := by
  have hne : {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = shadowArea S u}.Nonempty := by
    obtain ⟨u, hu⟩ := exists_norm_eq Space (show (0 : ℝ) ≤ 1 by norm_num)
    exact ⟨shadowArea S u, u, hu, rfl⟩
  have hbdd : BddBelow {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = shadowArea S u} := by
    refine ⟨0, ?_⟩
    rintro a ⟨u, hu, rfl⟩
    exact ENNReal.toReal_nonneg
  calc
    minimumShadowArea (centerMap '' S) = (1 / 4 : ℝ) * minimumShadowArea S := by
      unfold minimumShadowArea
      rw [centerMap_shadowArea_range]
      exact ((OrderIso.mulLeft₀ (1 / 4 : ℝ) (by norm_num)).map_csInf' hne hbdd).symm
    _ = minimumShadowArea S / 4 := by ring

theorem centerMap_minimizingDirection_iff (S : Set Space) (u : Space) :
    (‖centerDirection u‖ = 1 ∧
      shadowArea (centerMap '' S) (centerDirection u) =
        minimumShadowArea (centerMap '' S)) ↔
    (‖u‖ = 1 ∧ shadowArea S u = minimumShadowArea S) := by
  rw [centerDirection_norm, centerMap_shadowArea, centerMap_minimumShadowArea]
  constructor
  · rintro ⟨hu, harea⟩
    exact ⟨hu, by linarith⟩
  · rintro ⟨hu, harea⟩
    exact ⟨hu, by rw [harea]⟩

theorem centerMap_minimumShadowArea_pos_iff (S : Set Space) :
    0 < minimumShadowArea (centerMap '' S) ↔ 0 < minimumShadowArea S := by
  rw [centerMap_minimumShadowArea]
  exact div_pos_iff_of_pos_right (by norm_num)

theorem centerMap_minimumShadowArea_zero_iff (S : Set Space) :
    minimumShadowArea (centerMap '' S) = 0 ↔ minimumShadowArea S = 0 := by
  rw [centerMap_minimumShadowArea]
  simp

end CylinderCovering.Nilpotent

end

end OAI
