import Mathlib

namespace OAI

noncomputable section

open scoped InnerProductSpace

noncomputable section

theorem norm_minimizer_unique {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (hK : Convex ℝ K) {a b : F} (ha : a ∈ K) (hb : b ∈ K)
    (hmin : ‖(0 : F) - a‖ = ⨅ z : K, ‖(0 : F) - z‖) (hn : ‖b‖ = ‖a‖) : a = b := by
  have hbmin : ‖(0 : F) - b‖ = ⨅ z : K, ‖(0 : F) - z‖ := by
    simpa only [zero_sub, norm_neg, hn] using hmin
  have h₁ := (norm_eq_iInf_iff_real_inner_le_zero hK ha).mp hmin b hb
  have h₂ := (norm_eq_iInf_iff_real_inner_le_zero hK hb).mp hbmin a ha
  simp only [zero_sub, inner_neg_left, inner_sub_right] at h₁ h₂
  have hz : ⟪a-b,a-b⟫_ℝ ≤ 0 := by
    simp only [inner_sub_left, inner_sub_right]
    linarith
  rw [real_inner_self_eq_norm_sq] at hz
  apply eq_of_norm_sub_eq_zero
  nlinarith [norm_nonneg (a-b)]

theorem mapsTo_hull {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F →L[ℝ] F) {S : Set F} (hf : Set.MapsTo f S S) :
    Set.MapsTo f (closure (convexHull ℝ S)) (closure (convexHull ℝ S)) := by
  apply Set.MapsTo.closure _ f.continuous
  intro x hx
  have hh : f x ∈ f '' convexHull ℝ S := ⟨x, hx, rfl⟩
  rw [show f '' convexHull ℝ S = convexHull ℝ (f '' S) from
    f.toLinearMap.image_convexHull S] at hh
  exact convexHull_mono hf.image_subset hh

theorem commute_all_of_unitary {A : Type*} [CStarAlgebra A] (a : A)
    (ha : ∀ u : unitary A, Commute a (u : A)) : ∀ b, Commute a b := by
  intro b
  have hb : b ∈ Submodule.span ℂ (unitary A : Set A) := by
    rw [CStarAlgebra.span_unitary]; trivial
  induction hb using Submodule.span_induction with
  | mem y hy => exact ha ⟨y,hy⟩
  | zero => exact Commute.zero_right _
  | add x y hx hy hx' hy' => exact hx'.add_right hy'
  | smul c x hx hx' => exact hx'.smul_right c
end
end

end OAI
