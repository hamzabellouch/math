import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

namespace OAI

/-!
# A maximal degree shift detected on finitely many algebra generators

For an integer-graded algebra, the values of a derivation on finitely many
generators have only finitely many homogeneous components.  Thus a nonzero
derivation has a maximal degree shift which is attained on a generator.
These lemmas supply the finite-support step in the leading-derivation
construction of Sections 3 and 5 of the supplied manuscript.
-/

namespace StableCoordinate
namespace DerivationTopShift

open DirectSum GradedAlgebra

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- A nonzero element of an internally graded algebra has a nonzero
homogeneous projection. -/
theorem exists_proj_ne_zero {a : A} (ha : a ≠ 0) :
    ∃ j : ℤ, proj 𝒜 j a ≠ 0 := by
  classical
  by_contra! h
  apply ha
  apply (DirectSum.decompose 𝒜).injective
  ext j
  simpa using h j

/-- A nonzero derivation cannot vanish on all algebra generators. -/
theorem exists_generator_ne_zero (g : ι → A)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (D : Derivation k A A) (hD : D ≠ 0) :
    ∃ i, D (g i) ≠ 0 := by
  by_contra! h
  apply hD
  apply Derivation.ext_of_adjoin_eq_top (Set.range g) hg
  intro a ha
  obtain ⟨i, rfl⟩ := ha
  simpa using h i

variable [Fintype ι]

/-- Finitely many generator images admit a maximal degree shift, and for a
nonzero derivation the maximum is attained.  No sign restriction is imposed
on generator degrees or on the resulting shift. -/
theorem exists_maximal_generator_shift (g : ι → A) (d : ι → ℤ)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (D : Derivation k A A) (hD : D ≠ 0) :
    ∃ m : ℤ,
      (∀ i j, d i + m < j → proj 𝒜 j (D (g i)) = 0) ∧
      (∃ i, proj 𝒜 (d i + m) (D (g i)) ≠ 0) := by
  classical
  let S : Finset ℤ := Finset.univ.biUnion fun i =>
    ((DirectSum.decompose 𝒜 (D (g i))).support).image (fun j => j - d i)
  have memS (i : ι) (j : ℤ) (hj : proj 𝒜 j (D (g i)) ≠ 0) : j - d i ∈ S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨j, (GradedAlgebra.mem_support_iff 𝒜 _ _).mpr hj, rfl⟩
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := exists_generator_ne_zero g hg D hD
    obtain ⟨j, hj⟩ := exists_proj_ne_zero 𝒜 hi
    exact ⟨j - d i, memS i j hj⟩
  refine ⟨S.max' hS, ?_, ?_⟩
  · intro i j hj
    by_contra hne
    have hle := Finset.le_max' S (j - d i) (memS i j hne)
    omega
  · have hm : S.max' hS ∈ S := Finset.max'_mem S hS
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hi
    refine ⟨i, ?_⟩
    have hidx : d i + S.max' hS = j := by omega
    rw [hidx]
    exact (GradedAlgebra.mem_support_iff 𝒜 _ _).mp hj


/-- For a family of homogeneous component derivations, vanishing outside the
finite shift support can be tested solely on algebra generators. -/
theorem exists_maximal_component (g : ι → A) (d : ι → ℤ)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (D : Derivation k A A) (hD : D ≠ 0)
    (E : ℤ → Derivation k A A)
    (hE : ∀ m i, E m (g i) = proj 𝒜 (d i + m) (D (g i))) :
    ∃ m : ℤ, E m ≠ 0 ∧ ∀ n, m < n → E n = 0 := by
  obtain ⟨m, hbound, i, hi⟩ := exists_maximal_generator_shift 𝒜 g d hg D hD
  refine ⟨m, ?_, ?_⟩
  · intro hzero
    apply hi
    rw [← hE, hzero]
    rfl
  · intro n hn
    apply Derivation.ext_of_adjoin_eq_top (Set.range g) hg
    intro a ha
    obtain ⟨i, rfl⟩ := ha
    rw [hE]
    exact hbound i (d i + n) (by omega)

/-- Once homogeneous components are constructed, finite algebra generation
provides a single upper degree-shift bound on every homogeneous input, with
an attained nonzero top derivation.  This is the hypothesis needed for the
leading-component local-nilpotence argument. -/
theorem exists_top_component_and_global_bound
    (g : ι → A) (d : ι → ℤ)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (hhom : ∀ i, g i ∈ 𝒜 (d i))
    (D : Derivation k A A) (hD : D ≠ 0)
    (E : ℤ → Derivation k A A)
    (hE : ∀ m i (x : A), x ∈ 𝒜 i →
      E m x = proj 𝒜 (i + m) (D x)) :
    ∃ m : ℤ, E m ≠ 0 ∧
      (∀ n, m < n → E n = 0) ∧
      (∀ i (x : A), x ∈ 𝒜 i → ∀ j, i + m < j → proj 𝒜 j (D x) = 0) := by
  obtain ⟨m, hm, hmax⟩ := exists_maximal_component 𝒜 g d hg D hD E
    (fun m i => hE m (d i) (g i) (hhom i))
  refine ⟨m, hm, hmax, ?_⟩
  intro i x hx j hj
  have heq := hE (j - i) i x hx
  have hz := hmax (j - i) (by omega)
  rw [hz] at heq
  have hidx : i + (j - i) = j := by omega
  rw [hidx] at heq
  exact heq.symm

end DerivationTopShift
end StableCoordinate

end OAI
