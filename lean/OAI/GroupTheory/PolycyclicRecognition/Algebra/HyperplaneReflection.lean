import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace OAI

/-! # The reflection forced by agreement on a facet -/

noncomputable section
namespace PolycyclicRecognition

open scoped RealInnerProductSpace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

private theorem fixed_hyperplane_image_normal
    (A : W ≃ₗᵢ[ℝ] W) (v : W) (hv : v ≠ 0)
    (hfix : ∀ w, ⟪w, v⟫ = 0 → A w = w) :
    ∃ c : ℝ, A v = c • v := by
  let c := ⟪A v, v⟫ / ‖v‖ ^ 2
  let w := A v - c • v
  have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  have hw : ⟪w, v⟫ = 0 := by
    dsimp only [w]
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp only [c]
    simp [hn]
  have hvw : ⟪v, w⟫ = 0 := (real_inner_comm v w).symm.trans hw
  have haw : ⟪A v, w⟫ = 0 := by
    rw [← hfix w hw, A.inner_map_map]
    exact hvw
  have hww : ⟪w, w⟫ = 0 := by
    conv_lhs => lhs; rw [show w = A v - c • v from rfl]
    rw [inner_sub_left, inner_smul_left, haw, hvw]
    simp
  have hw0 : w = 0 := inner_self_eq_zero.mp hww
  exact ⟨c, sub_eq_zero.mp hw0⟩

/-- A nonidentity orthogonal map fixing a hyperplane reverses its normal.
This is the linear step in the neighboring-label reflection argument. -/
theorem orthogonal_map_fixing_hyperplane_negates_normal
    (A : W ≃ₗᵢ[ℝ] W) (v : W) (hv : v ≠ 0)
    (hfix : ∀ w, ⟪w, v⟫ = 0 → A w = w)
    (hne : A ≠ LinearIsometryEquiv.refl ℝ W) : A v = -v := by
  obtain ⟨c, hc⟩ := fixed_hyperplane_image_normal A v hv hfix
  have hnorm : |c| = 1 := by
    have he := A.norm_map v
    rw [hc, norm_smul, Real.norm_eq_abs] at he
    nlinarith [norm_pos_iff.mpr hv]
  rcases eq_or_eq_neg_of_abs_eq hnorm with h | h
  · have hav : A v = v := by simpa [h] using hc
    apply (hne ?_).elim
    ext x
    let d := ⟪x, v⟫ / ‖v‖ ^ 2
    have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
    have hw : ⟪x - d • v, v⟫ = 0 := by
      rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
      dsimp only [d]
      simp [hn]
    have he := hfix (x - d • v) hw
    rw [map_sub, map_smul, hav] at he
    exact sub_left_inj.mp he
  · simpa [h] using hc

end PolycyclicRecognition

end

end OAI
