import OAI.Probability.SignedSweeps.TensorCommutant

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
open Module Set
variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] (ρ : G →* (H ≃ₗᵢ[ℝ] H))

def closedOrbitHull (x : H) : Set H := closure (convexHull ℝ (Set.range (fun g => ρ g x)))

lemma closedOrbitHull_nonempty {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (ρ : G →* (H ≃ₗᵢ[ℝ] H))
    (x : H) : (closedOrbitHull ρ x).Nonempty :=
  ⟨ρ 1 x, subset_closure (subset_convexHull ℝ _ (Set.mem_range_self 1))⟩

lemma closedOrbitHull_convex {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (ρ : G →* (H ≃ₗᵢ[ℝ] H))
    (x : H) : Convex ℝ (closedOrbitHull ρ x) :=
  (convex_convexHull ℝ _).closure

lemma closedOrbitHull_image {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (ρ : G →* (H ≃ₗᵢ[ℝ] H))
    (x : H) (g : G) :
    (ρ g) '' closedOrbitHull ρ x = closedOrbitHull ρ x := by
  have hr : (ρ g) '' Set.range (fun h => ρ h x) = Set.range (fun h => ρ h x) := by
    ext y
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp⟩
    · rintro ⟨h, rfl⟩
      exact ⟨ρ (g⁻¹ * h) x, ⟨g⁻¹ * h, rfl⟩, by simp [map_mul]⟩
  unfold closedOrbitHull
  change (ρ g).toHomeomorph '' closure _ = _
  rw [(ρ g).toHomeomorph.image_closure]
  change closure ((ρ g).toLinearEquiv.toLinearMap '' _) = _
  rw [LinearMap.image_convexHull]
  change closure (convexHull ℝ ((ρ g) '' _)) = _
  rw [hr]

theorem exists_invariant_in_closedOrbitHull (x : H) :
    ∃ y ∈ closedOrbitHull ρ x, ∀ g, ρ g y = y := by
  obtain ⟨y, hy, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (closedOrbitHull_nonempty ρ x) isClosed_closure.isComplete
    (closedOrbitHull_convex ρ x) 0
  refine ⟨y, hy, fun g => ?_⟩
  have hgy : ρ g y ∈ closedOrbitHull ρ x := by
    rw [← closedOrbitHull_image ρ x g]
    exact ⟨y, hy, rfl⟩
  have hmin' : ‖(0 : H) - ρ g y‖ = ⨅ z : closedOrbitHull ρ x, ‖(0 : H) - z‖ := by
    simpa only [zero_sub, norm_neg, LinearIsometryEquiv.norm_map] using hmin
  have h₁ := (norm_eq_iInf_iff_real_inner_le_zero (closedOrbitHull_convex ρ x) hy).mp hmin _ hgy
  have h₂ := (norm_eq_iInf_iff_real_inner_le_zero (closedOrbitHull_convex ρ x) hgy).mp hmin' _ hy
  simp only [zero_sub, inner_neg_left, inner_sub_right] at h₁ h₂
  have hzero : ‖ρ g y - y‖ ^ 2 = 0 := by
    rw [@norm_sub_sq ℝ]
    have hr := real_inner_comm y (ρ g y)
    have hn₁ := real_inner_self_eq_norm_sq y
    have hn₂ := real_inner_self_eq_norm_sq (ρ g y)
    have hn₃ := sq_nonneg ‖ρ g y - y‖
    rw [@norm_sub_sq ℝ] at hn₃
    simp only [RCLike.re_to_real] at hn₃ ⊢
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

lemma closedOrbitHull_approximation {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (ρ : G →* (H ≃ₗᵢ[ℝ] H))
    {x y : H} (hy : y ∈ closedOrbitHull ρ x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (I : Type) (_ : Fintype I) (w : I → ℝ) (g : I → G),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ‖y - ∑ i, w i • ρ (g i) x‖ < ε := by
  obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.mp hy ε hε
  obtain ⟨I, hI, w, z', hw, hs, hz', he⟩ := mem_convexHull_iff_exists_fintype.mp hz
  choose g hg using hz'
  refine ⟨I, hI, w, g, hw, hs, ?_⟩
  have hh : (∑ i, w i • ρ (g i) x) = z := by
    simpa only [hg] using he
  rw [hh]
  exact (dist_eq_norm y z) ▸ hd

end SignedSweeps
end

end OAI
