import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryGeneratorHeight

namespace OAI

/-! # Height control from the quotient actions invisible to each generator -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

/-- The compact-volume comparison controls all ray traces except the ray
containing the generator. The positive balanced relation recovers the full
height increment with a common constant. -/
theorem generator_height_bound_of_boundary_actions
    {P G W I J : Type*} [Group G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I]
    (α ell : I → W →ₗ[ℝ] ℝ) (c rate : I → ℝ)
    (hc : ∀ i, 0 < c i) (hrate : ∀ i, 0 < rate i)
    (hrel : ∀ w, ∑ i, c i * α i w = 0)
    (hsep : ∀ w, (∀ i, α i w = 0) → w = 0)
    (hell : ∀ i, ell i = rate i • α i)
    (S : I → Type*) (act : ∀ i, G →* Equiv.Perm (S i)) (U : ∀ i, Set (S i))
    (η : P → G → W) (gen : J → ℝ → G) (missing : J → I)
    (B : I → ℝ) (hB : ∀ i, 0 ≤ B i)
    (htrace : ∀ i p x y, act i x '' U i = act i y '' U i →
      |ell i (η p x - η p y)| ≤ B i)
    (hact : ∀ j i, α i ∉ positiveWeightRay (α (missing j)) → ∀ t, act i (gen j t) = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p x j t, ‖η p (x * gen j t) - η p x‖ ≤ K := by
  obtain ⟨K, hK, hb⟩ := uniform_height_bound_of_ray_trace_bounds α ell c rate hc hrate
    hrel hsep hell
    (fun z : P × G × J × ℝ => η z.1 (z.2.1 * gen z.2.2.1 z.2.2.2) - η z.1 z.2.1)
    (fun z => missing z.2.2.1) B hB (by
      rintro ⟨p, x, j, t⟩ i hi
      apply htrace i p (x * gen j t) x
      have he : act i (x * gen j t) = act i x := by rw [map_mul, hact j i hi t, mul_one]
      exact congrArg (fun q : Equiv.Perm (S i) => q '' U i) he)
  exact ⟨K, hK, fun p x j t => hb (p, x, j, t)⟩

end PolycyclicRecognition

end

end OAI
