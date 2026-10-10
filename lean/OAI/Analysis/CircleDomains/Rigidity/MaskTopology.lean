import OAI.Analysis.CircleDomains.Sobolev.CircleEnergy
import OAI.Analysis.CircleDomains.Modulus.CircleWedgeCost

namespace OAI

/-!
# Masks away from their retained boundaries

A connected filling cap disjoint from the mask boundary is wholly on
one side. Away from that boundary, extending a circle coordinate by zero
outside the mask is smooth and its intrinsic differential is exactly
the indicated covector.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem connected_set_avoiding_mask_boundary
    {X : Type*} [TopologicalSpace X] {A M : Set X}
    (hA : IsPreconnected A) (hM : IsClosed M) (havoid : Disjoint A (frontier M)) :
    A ⊆ interior M ∨ A ⊆ Mᶜ := by
  apply hA.subset_or_subset isOpen_interior hM.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset)
  intro x hx
  by_cases hxM : x ∈ M
  · exact Or.inl ((mem_interior_iff_notMem_frontier hxM).mpr
      (Set.disjoint_left.mp havoid hx))
  · exact Or.inr hxM

def maskCircleMap {X : Type*} (M : Set X) (f : X → UnitAddCircle) (x : X) : UnitAddCircle := by
  classical
  exact if x ∈ M then f x else 0

theorem maskCircleMap_eventuallyEq_inside
    {X : Type*} [TopologicalSpace X] (M : Set X) (f : X → UnitAddCircle)
    {x : X} (hx : x ∈ interior M) : maskCircleMap M f =ᶠ[𝓝 x] f := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  simp only [maskCircleMap, ite_eq_left (interior_subset hy)]

theorem maskCircleMap_eventuallyEq_outside
    {X : Type*} [TopologicalSpace X] {M : Set X} (hM : IsClosed M) (f : X → UnitAddCircle)
    {x : X} (hx : x ∉ M) : maskCircleMap M f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hM.isOpen_compl.mem_nhds hx] with y hy
  simp only [maskCircleMap, ite_eq_right hy]

theorem circleGradient_zero (x : ℝ × ℝ) : circleGradient (fun _ => 0) x = 0 := by
  have heq : (fun _ : ℝ × ℝ => ((0 : ℝ) : UnitAddCircle)) =ᶠ[𝓝 x] fun _ => 0 := by simp
  simpa only [planarGradient_const] using
    circleGradient_eq_lift continuousAt_const continuousAt_const heq

theorem circleGradient_maskCircleMap
    {M : Set (ℝ × ℝ)} (hM : IsClosed M) (f : (ℝ × ℝ) → UnitAddCircle)
    {x : ℝ × ℝ} (hx : x ∉ frontier M) :
    circleGradient (maskCircleMap M f) x = M.indicator (circleGradient f) x := by
  by_cases hxM : x ∈ M
  · have hxi : x ∈ interior M := (mem_interior_iff_notMem_frontier hxM).mpr hx
    rw [circleGradient_congr_of_eventuallyEq (maskCircleMap_eventuallyEq_inside M f hxi),
      indicator_of_mem hxM]
  · rw [circleGradient_congr_of_eventuallyEq (maskCircleMap_eventuallyEq_outside hM f hxM),
      circleGradient_zero, indicator_of_notMem hxM]

theorem smoothCircleOn_mask_off_frontier
    {M G : Set (ℝ × ℝ)} (hM : IsClosed M) {f : (ℝ × ℝ) → UnitAddCircle}
    (hf : SmoothCircleOn f (G ∩ interior M)) :
    SmoothCircleOn (maskCircleMap M f) (G \ frontier M) := by
  apply smoothCircleOn_iff_local_lifts.mpr
  intro x hx
  by_cases hxM : x ∈ M
  · have hxi : x ∈ interior M := (mem_interior_iff_notMem_frontier hxM).mpr hx.2
    obtain ⟨u, hu, hproj⟩ := smoothCircleOn_iff_local_lifts.mp hf x ⟨hx.1, hxi⟩
    exact ⟨u, hu, hproj.trans (maskCircleMap_eventuallyEq_inside M f hxi).symm⟩
  · refine ⟨fun _ => 0, contDiffAt_const, ?_⟩
    simpa only [AddCircle.coe_zero] using (maskCircleMap_eventuallyEq_outside hM f hxM).symm

theorem circleWedges_maskCircleMap_eq
    {n : ℕ} (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) {z : ℝ × ℝ}
    (hz : ∀ i, z ∉ frontier (M i)) :
    circleWedges (fun i => maskCircleMap (M i) (f i)) z = maskedCircleWedges M f z := by
  rw [circleWedges, fieldWedges_eq_sum_upperPairs]
  apply Finset.sum_congr rfl
  intro p _
  rw [circleGradient_maskCircleMap (hM _) _ (hz _),
    circleGradient_maskCircleMap (hM _) _ (hz _)]

theorem smoothCircleOn_masks_off_boundaries
    {n : ℕ} {G : Set (ℝ × ℝ)} (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, SmoothCircleOn (f i) (G ∩ interior (M i))) :
    ∀ i, SmoothCircleOn (maskCircleMap (M i) (f i)) (G \ ⋃ j, frontier (M j)) := by
  intro i x hx a ha
  exact smoothCircleOn_mask_off_frontier (hM i) (hf i) x
    ⟨hx.1, fun h => hx.2 (mem_iUnion.mpr ⟨i, h⟩)⟩ a ha

end CircleDomainRigidity.FiniteTransfer

end

end OAI
