import OAI.Probability.SignedSweeps.ConvexTwirl

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module Set
variable {E F Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma linear_mem_closed_convex (L : E →ₗ[ℝ] Z) {S : Set E} {C : Set Z}
    (hC : IsClosed C) (hV : Convex ℝ C) (hS : ∀ s ∈ S, L s ∈ C)
    {x : E} (hx : x ∈ closedConvexHull ℝ S) : L x ∈ C := by
  exact closedConvexHull_min hS (hV.linear_preimage L)
    (hC.preimage L.continuous_of_finiteDimensional) hx

lemma bilinear_mem_closed_convex (L : E →ₗ[ℝ] F →ₗ[ℝ] Z)
    {S : Set E} {T : Set F} {C : Set Z}
    (hC : IsClosed C) (hV : Convex ℝ C)
    (hST : ∀ s ∈ S, ∀ t ∈ T, L s t ∈ C)
    {x : E} (hx : x ∈ closedConvexHull ℝ S)
    {y : F} (hy : y ∈ closedConvexHull ℝ T) : L x y ∈ C := by
  apply linear_mem_closed_convex (L.flip y) hC hV _ hx
  intro s hs
  exact linear_mem_closed_convex (L s) hC hV (hST s hs) hy

lemma linear_image_closedConvexHull {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →ₗ[ℝ] F) (S : Set E)
    (hS : IsCompact (closedConvexHull ℝ S)) :
    L '' closedConvexHull ℝ S = closedConvexHull ℝ (L '' S) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    apply linear_mem_closed_convex L isClosed_closedConvexHull convex_closedConvexHull _ hx
    intro s hs
    exact subset_closedConvexHull ⟨s,hs,rfl⟩
  · apply closedConvexHull_min
    · exact Set.image_mono subset_closedConvexHull
    · exact convex_closedConvexHull.linear_image L
    · exact (hS.image L.continuous_of_finiteDimensional).isClosed

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module Set
variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] (ρ : G →* (H ≃ₗᵢ[ℝ] H))

lemma isCompact_closedOrbitHull (x : H) : IsCompact (closedOrbitHull ρ x) := by
  apply (isCompact_closedBall (0 : H) ‖x‖).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  apply convexHull_min _ (convex_closedBall (0 : H) ‖x‖)
  rintro _ ⟨g,rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
    using (le_refl ‖x‖)

lemma closedOrbitHull_eq_closedConvexHull {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (ρ : G →* (H ≃ₗᵢ[ℝ] H)) (x : H) :
    closedOrbitHull ρ x = closedConvexHull ℝ (Set.range (fun g => ρ g x)) :=
  closedConvexHull_eq_closure_convexHull.symm

theorem orbitHull_lift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (L : H →ₗ[ℝ] F) (x : H) {y : F}
    (hy : y ∈ closedConvexHull ℝ (Set.range (fun g => L (ρ g x)))) :
    ∃ z ∈ closedOrbitHull ρ x, L z = y := by
  have he : L '' closedOrbitHull ρ x =
      closedConvexHull ℝ (Set.range (fun g => L (ρ g x))) := by
    rw [closedOrbitHull_eq_closedConvexHull]
    rw [linear_image_closedConvexHull L _ (by
      rw [← closedOrbitHull_eq_closedConvexHull]; exact isCompact_closedOrbitHull ρ x)]
    rw [← Set.range_comp']
  rwa [← he] at hy

end SignedSweeps
end

end OAI
