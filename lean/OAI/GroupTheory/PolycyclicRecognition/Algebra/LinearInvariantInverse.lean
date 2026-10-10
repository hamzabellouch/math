import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

/-! # Inverting a finite-dimensional map preserves its invariant subspaces -/

namespace PolycyclicRecognition

theorem inverse_mem_of_preserves_submodule
    {L : Type*} [AddCommGroup L] [Module ℝ L] [FiniteDimensional ℝ L]
    (e : L ≃ₗ[ℝ] L) (V : Submodule ℝ L)
    (he : ∀ x ∈ V, e x ∈ V) {x : L} (hx : x ∈ V) : e.symm x ∈ V := by
  let f : V →ₗ[ℝ] V :=
    { toFun := fun v => ⟨e v, he v v.property⟩
      map_add' := fun a b => Subtype.ext (e.map_add a b)
      map_smul' := fun r a => Subtype.ext (e.map_smul r a) }
  have hi : Function.Injective f := by
    intro a b h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hi) ⟨x, hx⟩
  have heq : e (y : L) = x := congrArg Subtype.val hy
  rw [← heq, e.symm_apply_apply]
  exact y.property

end PolycyclicRecognition

end OAI
