import Mathlib

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
section Geometry
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)

def componentSpace (c : isotypicComponents ℂ[G] ρ.asModule) : Submodule ℂ V :=
  c.val.restrictScalars ℂ

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma componentSpace_invariant (c : isotypicComponents ℂ[G] ρ.asModule)
    (g : G) (v : V) (hv : v ∈ componentSpace ρ c) : ρ g v ∈ componentSpace ρ c := by
  have h := c.val.smul_mem (MonoidAlgebra.single g (1 : ℂ)) hv
  change ρ.asAlgebraHom (MonoidAlgebra.single g 1) v ∈ c.val at h
  change ρ g v ∈ c.val
  simpa using h

omit [FiniteDimensional ℂ V] in
lemma iSup_componentSpace : ⨆ c, componentSpace ρ c = ⊤ := by
  change (⨆ c : isotypicComponents ℂ[G] ρ.asModule, c.val.restrictScalars ℂ) = ⊤
  rw [← Submodule.restrictScalars_iSup, ← sSup_eq_iSup', sSup_isotypicComponents,
    Submodule.restrictScalars_top]

omit [Fintype G] in
lemma componentSpace_projection_commute
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (c : isotypicComponents ℂ[G] ρ.asModule) (g : G) (v : V) :
    ρ g ((componentSpace ρ c).starProjection v) =
      (componentSpace ρ c).starProjection (ρ g v) := by
  have he : (componentSpace ρ c).map (ρ g) = componentSpace ρ c := by
    apply le_antisymm
    · rintro x ⟨v, hv, rfl⟩
      exact componentSpace_invariant ρ c g v hv
    · intro v hv
      exact ⟨ρ g⁻¹ v, componentSpace_invariant ρ c g⁻¹ v hv, by simp⟩
  have hm := ((ρ g).isometryOfInner (hρ g)).map_starProjection (componentSpace ρ c) v
  simpa only [LinearMap.coe_isometryOfInner, LinearMap.isometryOfInner_toLinearMap, he] using hm

omit [Fintype G] in
lemma componentSpace_orthogonal
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y) :
    OrthogonalFamily ℂ (fun c => componentSpace ρ c) (fun c => (componentSpace ρ c).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro c d hcd x hx
  apply (Submodule.starProjection_apply_eq_zero_iff (K := componentSpace ρ d)).mp
  let p : ρ.IntertwiningMap ρ :=
    { toLinearMap := (componentSpace ρ d).starProjection.toLinearMap
      isIntertwining' g := by
        ext v
        exact (componentSpace_projection_commute ρ hρ d g v).symm }
  let f := Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ p
  have hi : c.val.IsFullyInvariant := .of_mem_isotypicComponents c.property
  have hmem : f x ∈ c.val := hi f hx
  have hmem' : f x ∈ d.val := (componentSpace ρ d).starProjection_apply_mem x
  have hd : Disjoint c.val d.val :=
    (sSupIndep_isotypicComponents ℂ[G] ρ.asModule).pairwiseDisjoint c.property d.property
      (Subtype.coe_ne_coe.mpr hcd)
  exact Submodule.disjoint_def.mp hd (f x) hmem hmem'

lemma sum_component_projections
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    [Fintype (isotypicComponents ℂ[G] ρ.asModule)] (v : V) :
    ∑ c, (componentSpace ρ c).starProjection v = v :=
  (componentSpace_orthogonal ρ hρ).sum_projection_of_mem_iSup v
    (by rw [iSup_componentSpace]; trivial)

lemma sum_component_norm_sq
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    [Fintype (isotypicComponents ℂ[G] ρ.asModule)] (v : V) :
    ∑ c, ‖(componentSpace ρ c).starProjection v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := (componentSpace_orthogonal ρ hρ).norm_sum
    (fun c => (componentSpace ρ c).orthogonalProjectionOnto v) Finset.univ
  change ‖∑ c, (componentSpace ρ c).starProjection v‖ ^ 2 =
    ∑ c, ‖(componentSpace ρ c).starProjection v‖ ^ 2 at h
  rw [sum_component_projections ρ hρ] at h
  exact h.symm

end Geometry
end
end PartialPermutation

end

end OAI
