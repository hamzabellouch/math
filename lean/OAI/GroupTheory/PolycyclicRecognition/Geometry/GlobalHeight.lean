import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryMass

namespace OAI

/-!
# Assembling the scalar boundary bounds into global height bounds

The scalar estimates are uniform over all base points. Separating boundary
traces then control the full height on a transversal, and the leaf estimate
extends the same bound to the whole group. The existence of the boundary maps
and their shadow estimates remains the geometric obligation.
-/

namespace PolycyclicRecognition

/-- Finitely many uniform trace bounds give a uniform vector-valued affine
bound. No choice of a basis depending on the quasi-isometry is involved. -/
theorem affine_bound_of_trace_bounds
    {X W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I]
    (β : I → Module.Dual ℝ W)
    (hsep : ∀ w, (∀ i, β i w = 0) → w = 0)
    (π F : X → W) (A : W →ₗ[ℝ] W) (v : W)
    {B : ℝ} (hB : 0 ≤ B)
    (htrace : ∀ x i, |β i (F x - (v + A (π x)))| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖F x - (v + A (π x))‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_of_separating_forms β hsep
  exact ⟨C * B, mul_nonneg hC.le hB, fun x => hbound _ B hB (htrace x)⟩

/-- The bounded leaf and transversal estimates combine using `G = N D`.
The decomposition need not be unique, and its factors need not commute. -/
theorem global_affine_bound_of_leaf_transversal
    {G W : Type*} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (π F : G → W) (A : W →ₗ[ℝ] W) (v : W) (N D : Set G)
    (hdecomp : ∀ g, ∃ n ∈ N, ∃ d ∈ D, g = n * d)
    (hheight : ∀ n ∈ N, ∀ d ∈ D, π (n * d) = π d)
    {B C : ℝ}
    (hleaf : ∀ n ∈ N, ∀ d ∈ D, ‖F (n * d) - F d‖ ≤ B)
    (htrans : ∀ d ∈ D, ‖F d - (v + A (π d))‖ ≤ C) :
    ∀ g, ‖F g - (v + A (π g))‖ ≤ B + C := by
  intro g
  obtain ⟨n, hn, d, hd, rfl⟩ := hdecomp g
  rw [hheight n hn d hd]
  calc
    _ = ‖(F (n * d) - F d) + (F d - (v + A (π d)))‖ := by congr 1; abel
    _ ≤ ‖F (n * d) - F d‖ + ‖F d - (v + A (π d))‖ := norm_add_le _ _
    _ ≤ B + C := add_le_add (hleaf n hn d hd) (htrans d hd)

/-- Once the sublinear comparison identifies a trace coefficient, its bounded
scalar error has exactly the affine form required for vector assembly. -/
theorem affine_trace_bound_of_identified_coefficient
    {X W : Type*} [AddCommGroup W] [Module ℝ W]
    (π F : X → W) (α β : Module.Dual ℝ W) (A : W →ₗ[ℝ] W) (x₀ : X)
    (hπ₀ : π x₀ = 0) (hid : α = β.comp A) {B : ℝ}
    (hbound : ∀ x, |(β (F x) - β (F x₀)) - (α (π x) - α (π x₀))| ≤ B) :
    ∀ x, |β (F x - (F x₀ + A (π x)))| ≤ B := by
  intro x
  have h := hbound x
  simpa only [hπ₀, map_zero, sub_zero, hid, LinearMap.comp_apply,
    map_sub, map_add, sub_add_eq_sub_sub] using h

end PolycyclicRecognition

end OAI
