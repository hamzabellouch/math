import OAI.GroupTheory.PolycyclicRecognition.Lattices.SemidirectUniformLattice

namespace OAI

/-! # Equivariant embeddings of two lattices into a semidirect product -/

noncomputable section
namespace PolycyclicRecognition
variable {H K N V : Type*} [Group H] [Group K] [Group N] [Group V]
  [TopologicalSpace N] [TopologicalSpace V]
  (ρ : K →* MulAut H) (φ : V →* MulAut N)
  (Λ : Subgroup N) (Δ : Subgroup V) (e : H ≃* Λ) (f : K ≃* Δ)
  (he : ∀ k x, (e (ρ k x) : N) = φ (f k) (e x))

attribute [local instance] semidirectProductTopology
include e f he

omit [TopologicalSpace N] [TopologicalSpace V] in
theorem semidirect_lattice_preserved : ∀ v ∈ Δ, ∀ x ∈ Λ, φ v x ∈ Λ := by
  intro v hv x hx
  obtain ⟨k, hk⟩ := f.surjective ⟨v, hv⟩
  obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
  have hv' : (f k : V) = v := congrArg Subtype.val hk
  have hx' : (e y : N) = x := congrArg Subtype.val hy
  rw [← hv', ← hx', ← he]
  exact (e (ρ k y)).property

theorem semidirect_lattice_embedding (hΛ : IsUniformLattice Λ) (hΔ : IsUniformLattice Δ) :
    ∃ Γ : Subgroup (N ⋊[φ] V), IsUniformLattice Γ ∧ Nonempty ((H ⋊[ρ] K) ≃* Γ) := by
  let j : H →* N := Λ.subtype.comp e.toMonoidHom
  let k : K →* V := Δ.subtype.comp f.toMonoidHom
  let F : (H ⋊[ρ] K) →* (N ⋊[φ] V) := SemidirectProduct.map j k (by
    intro a
    ext x
    exact he a x)
  let Γ := semidirectLattice φ Λ Δ (semidirect_lattice_preserved ρ φ Λ Δ e f he)
  have hF (x) : F x ∈ Γ := ⟨(e x.left).property, (f x.right).property⟩
  let F' : (H ⋊[ρ] K) →* Γ := F.codRestrict Γ hF
  have hinj : Function.Injective F' := by
    intro x y h
    apply SemidirectProduct.ext
    · apply e.injective
      apply Subtype.ext
      exact congrArg (fun z : Γ => z.val.left) h
    · apply f.injective
      apply Subtype.ext
      exact congrArg (fun z : Γ => z.val.right) h
  have hsurj : Function.Surjective F' := by
    intro z
    obtain ⟨x, hx⟩ := e.surjective ⟨z.val.left, z.property.1⟩
    obtain ⟨y, hy⟩ := f.surjective ⟨z.val.right, z.property.2⟩
    refine ⟨⟨x, y⟩, ?_⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact congrArg Subtype.val hx
    · exact congrArg Subtype.val hy
  exact ⟨Γ, semidirectLattice_uniform φ Λ Δ _ hΛ hΔ,
    ⟨MulEquiv.ofBijective F' ⟨hinj, hsurj⟩⟩⟩

end PolycyclicRecognition

end

end OAI
