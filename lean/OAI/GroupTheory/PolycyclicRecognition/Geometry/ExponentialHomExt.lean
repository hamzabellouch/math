import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBasisGeneration

namespace OAI

/-! # Homomorphisms are determined by exponential curves -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]
  [PreconnectedSpace G] [Group H]

theorem monoidHom_ext_exponential
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (f g : G →* H) (h : ∀ x, f (Exp x) = g (Exp x)) : f = g := by
  let S : Subgroup G :=
    { carrier := {x | f x = g x}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change f x = g x at hx
        change f y = g y at hy
        change f (x * y) = g (x * y)
        rw [map_mul, map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        change f x = g x at hx
        change f x⁻¹ = g x⁻¹
        rw [map_inv, map_inv, hx] }
  have hS : S = ⊤ := by
    apply subgroup_eq_top_of_exponential_basis hExp (Module.finBasis ℝ E)
    intro i t
    exact h _
  ext x
  have hx : x ∈ S := by rw [hS]; trivial
  exact hx

theorem height_eq_of_exponential_linear
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (ψ : G →* Multiplicative W') (e : W' →ₗ[ℝ] W)
    (he : ∀ x, (π (Exp x)).toAdd = e (ψ (Exp x)).toAdd) :
    ∀ g, (π g).toAdd = e (ψ g).toAdd := by
  let τ : G →* Multiplicative W :=
    { toFun := fun g => Multiplicative.ofAdd (e (ψ g).toAdd)
      map_one' := by simp
      map_mul' := by intro g h; simp only [map_mul, toAdd_mul, map_add]; rfl }
  have h : π = τ := monoidHom_ext_exponential hExp π τ
    (fun x => Multiplicative.ext (he x))
  intro g
  exact congrArg (fun f : G →* Multiplicative W => (f g).toAdd) h

end PolycyclicRecognition

end

end OAI
