import OAI.AlgebraicGeometry.StableCoordinate.LeadingComponent
import OAI.AlgebraicGeometry.StableCoordinate.DerivationTopShift

namespace OAI

/-!
# A nonzero leading locally nilpotent derivation

This module combines finite algebra generation with the actual homogeneous
component construction.  It establishes the auxiliary-grading passage in
§5 of the source without assuming a global degree-shift bound.
-/

noncomputable section

namespace StableCoordinate
namespace LeadingComponent

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A] [Fintype ι]
variable (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- Every nonzero locally nilpotent derivation of a finitely generated
integer-graded algebra with homogeneous generators has a nonzero leading
homogeneous locally nilpotent component. -/
theorem exists_nonzero_locallyNilpotent_component
    (g : ι → A) (d : ι → ℤ)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (hhom : ∀ i, g i ∈ 𝒜 (d i))
    (D : Derivation k A A) (hD : D ≠ 0)
    (hln : ∀ x : A, ∃ n : ℕ, (D : A → A)^[n] x = 0) :
    ∃ m : ℤ, component 𝒜 D m ≠ 0 ∧
      HasShiftLE 𝒜 D.toLinearMap m ∧
      (∀ x : A, ∃ n : ℕ, ((component 𝒜 D m : A → A)^[n] x) = 0) := by
  obtain ⟨m, hm, _, hbound⟩ :=
    DerivationTopShift.exists_top_component_and_global_bound 𝒜 g d hg hhom D hD
      (component 𝒜 D) (fun m _ _ hx => component_of_mem 𝒜 D m hx)
  exact ⟨m, hm, hbound, locallyNilpotent_component 𝒜 D hbound hln⟩

/-- The source's auxiliary-grading reduction: if a locally nilpotent
derivation annihilates a sum of two distinct homogeneous degrees, its
nonzero leading locally nilpotent component annihilates the higher part. -/
theorem exists_nonzero_locallyNilpotent_component_annihilating_top
    (g : ι → A) (d : ι → ℤ)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (hhom : ∀ i, g i ∈ 𝒜 (d i))
    (D : Derivation k A A) (hD : D ≠ 0)
    (hln : ∀ x : A, ∃ n : ℕ, (D : A → A)^[n] x = 0)
    {i j : ℤ} {x y : A} (hx : x ∈ 𝒜 i) (hy : y ∈ 𝒜 j)
    (hij : i < j) (hxy : D (x + y) = 0) :
    ∃ m : ℤ, component 𝒜 D m ≠ 0 ∧
      (∀ z : A, ∃ n : ℕ, ((component 𝒜 D m : A → A)^[n] z) = 0) ∧
      component 𝒜 D m y = 0 := by
  obtain ⟨m, hm, hbound, hnil⟩ :=
    exists_nonzero_locallyNilpotent_component 𝒜 g d hg hhom D hD hln
  exact ⟨m, hm, hnil, component_high_term_eq_zero 𝒜 D hbound hx hy hij hxy⟩

/-- The leading component also preserves a compatible second grading.
This packages the full leading-component step of the source's rigidity
proof, including preservation of the fiber weights. -/
theorem exists_nonzero_locallyNilpotent_component_compatible
    (ℬ : ℤ → Submodule k A) [GradedAlgebra ℬ]
    (hcomm : ∀ (i j : ℤ) (x : A),
      proj 𝒜 i (proj ℬ j x) = proj ℬ j (proj 𝒜 i x))
    (g : ι → A) (d : ι → ℤ)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (hhom : ∀ i, g i ∈ 𝒜 (d i))
    (D : Derivation k A A) (hD : D ≠ 0)
    (hln : ∀ x : A, ∃ n : ℕ, (D : A → A)^[n] x = 0)
    (hpres : ∀ (r : ℤ) (z : A), z ∈ ℬ r → D z ∈ ℬ r)
    {i j : ℤ} {x y : A} (hx : x ∈ 𝒜 i) (hy : y ∈ 𝒜 j)
    (hij : i < j) (hxy : D (x + y) = 0) :
    ∃ m : ℤ, component 𝒜 D m ≠ 0 ∧
      (∀ z : A, ∃ n : ℕ, ((component 𝒜 D m : A → A)^[n] z) = 0) ∧
      (∀ (r : ℤ) (z : A), z ∈ ℬ r → component 𝒜 D m z ∈ ℬ r) ∧
      component 𝒜 D m y = 0 := by
  obtain ⟨m, hm, hnil, htop⟩ :=
    exists_nonzero_locallyNilpotent_component_annihilating_top 𝒜 g d hg hhom D hD hln
      hx hy hij hxy
  refine ⟨m, hm, hnil, ?_, htop⟩
  intro r z hz
  exact component_preserves_compatible_grading 𝒜 ℬ hcomm D m hpres hz

end LeadingComponent
end StableCoordinate

end

end OAI
