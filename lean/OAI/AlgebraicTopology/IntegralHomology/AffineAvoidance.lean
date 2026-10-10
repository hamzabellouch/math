import OAI.AlgebraicTopology.IntegralHomology.ProductCover

namespace OAI

noncomputable section

namespace Kaplansky

/-! Affine-avoidance covers and convex product-pair homology. -/

section
open Set
variable {E F J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype J]

/-- The complement of finitely many affine zero sets, including dependent
or zero affine maps. No general-position or nonempty assumption is made. -/
def affineAvoidanceSet (l : J → E →L[ℝ] F) (c : J → F) : Set E := {x | ∀ j, l j x + c j ≠ 0}

/-- A finite chart chooses a nonzero signed real coordinate for each image. -/
def affineAvoidanceChart (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) : Set E :=
  ⋂ j, (fun x => l j x + c j) ⁻¹' signedCoordinateHalfspace (s j)

theorem affineAvoidanceChart_open (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) : IsOpen (affineAvoidanceChart l c s) :=
  isOpen_iInter_of_finite (fun j => (signedCoordinateHalfspace_open (s j)).preimage ((l j).continuous.add continuous_const))

omit [Fintype J] in
theorem affineAvoidanceChart_convex (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) : Convex ℝ (affineAvoidanceChart l c s) :=
  convex_iInter (fun j => ((signedCoordinateHalfspace_convex (s j)).translate_preimage_left (c j)).linear_preimage (l j).toLinearMap)

omit [Fintype J] in
theorem affineAvoidanceCharts_cover (l : J → E →L[ℝ] F) (c : J → F) :
    (⋃ s : J → Fin (Module.finrank ℝ F) × Bool, affineAvoidanceChart l c s) =
      affineAvoidanceSet l c := by
  ext x
  constructor
  · intro hx
    obtain ⟨s,hs⟩ := mem_iUnion.mp hx
    change ∀ j, l j x + c j ≠ 0
    intro j
    have hm : l j x + c j ∈ ⋃ i, signedCoordinateHalfspace i :=
      mem_iUnion.mpr ⟨s j,mem_iInter.mp hs j⟩
    rw [signedCoordinateHalfspaces_cover] at hm
    exact hm
  · intro hx
    have he : ∀ j, ∃ i : Fin (Module.finrank ℝ F) × Bool,
        l j x + c j ∈ signedCoordinateHalfspace i := by
      intro j
      rw [← mem_iUnion, signedCoordinateHalfspaces_cover]
      exact hx j
    choose s hs using he
    exact mem_iUnion.mpr ⟨s,mem_iInter.mpr hs⟩

omit [Fintype J] in
theorem affineAvoidanceChart_subset (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) :
    affineAvoidanceChart l c s ⊆ affineAvoidanceSet l c := by
  rw [← affineAvoidanceCharts_cover]
  exact subset_iUnion _ s

theorem affineAvoidanceSet_open (l : J → E →L[ℝ] F) (c : J → F) : IsOpen (affineAvoidanceSet l c) := by
  rw [← affineAvoidanceCharts_cover]
  exact isOpen_iUnion (affineAvoidanceChart_open l c)

end

section
open CategoryTheory Limits Set
variable {E V J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
/-- A nonempty convex subset remains contractible when viewed inside a
larger base subset, with its actual iterated subspace topology. -/
theorem convexRestrictedBase_contractible (D C : Set E) (hCD : C ⊆ D)
    (hc : Convex ℝ C) (hne : (Subtype.val ⁻¹' C : Set D).Nonempty) :
    ContractibleSpace (Subtype.val ⁻¹' C : Set D) := by
  have : ContractibleSpace C := hc.contractibleSpace ⟨hne.choose.val,hne.choose_spec⟩
  exact (subspaceSubsetHomeomorph C D hCD).contractibleSpace

omit [FiniteDimensional ℝ E] in
/-- Every nonempty intersection of convex base charts has the required
lower relative vanishing. Empty intersections have zero groups as well. -/
theorem convexCover_product_intersection_below_isZero
    (D : Set E) (S : Finset J) (C : J → Set E)
    (hsub : ∀ i ∈ S, C i ⊆ D) (hconv : ∀ i ∈ S, Convex ℝ (C i))
    (T : Finset J) (ht : T.Nonempty) (hts : T ⊆ S)
    (hv : 2 ≤ Module.finrank ℝ V) (q : ℕ) (hq : q < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology
      (subspaceInclusion {z : (⋂ i ∈ T, (Subtype.val ⁻¹' C i : Set D)) × V |
        z.2 ≠ 0}) q) := by
  let W : Set E := ⋂ i ∈ T, C i
  have hW : W ⊆ D := by
    obtain ⟨i,hi⟩ := ht
    intro x hx
    exact hsub i (hts hi) (mem_iInter.mp (mem_iInter.mp hx i) hi)
  have hcv : Convex ℝ W :=
    convex_iInter (fun i => convex_iInter (fun hi => hconv i (hts hi)))
  have heq : (⋂ i ∈ T, (Subtype.val ⁻¹' C i : Set D)) = Subtype.val ⁻¹' W := by
    ext x; simp [W]
  rw [heq]
  by_cases hne : (Subtype.val ⁻¹' W : Set D).Nonempty
  · have := convexRestrictedBase_contractible D W hW hcv hne
    exact (localVectorHomology_isZero V hv q (by omega)).of_iso
      (productPairProjectionIso (B := (Subtype.val ⁻¹' W : Set D)) ({0}ᶜ : Set V) q)
  · have : IsEmpty ((Subtype.val ⁻¹' W : Set D) × V) :=
      ⟨fun z => hne ⟨z.1.val,z.1.property⟩⟩
    exact relativeHomology_isZero_empty _ q

omit [FiniteDimensional ℝ E] in
/-- Relative homology below fiber dimension vanishes over any finite
union of open convex base sets. Neither connectivity nor contractibility
of that union is asserted. -/
theorem convexOpenUnion_product_below_isZero
    (S : Finset J) (C : J → Set E)
    (hopen : ∀ i ∈ S, IsOpen (C i)) (hconv : ∀ i ∈ S, Convex ℝ (C i))
    (hv : 2 ≤ Module.finrank ℝ V) (q : ℕ) (hq : q < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology (subspaceInclusion
      {z : (⋃ i ∈ S, C i) × V | z.2 ≠ 0}) q) := by
  let U : J → Set (E × V) := fun i => {z | z.1 ∈ C i}
  let A : Set (E × V) := {z | z.2 ≠ 0}
  have hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ k < Module.finrank ℝ V,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) k) := by
    intro T _ hts k hk
    have he : (⋂ i ∈ T, U i) = {z : E × V | z.1 ∈ ⋂ i ∈ T, C i} := by
      ext z; simp [U]
    rw [he]
    exact convexBaseProductPair_below_isZero _
      (convex_iInter (fun i => convex_iInter (fun hi => hconv i (hts hi)))) hv k hk
  have hz := finiteRelativeOpenUnion_below_isZero S U A
    (fun i hi => (hopen i hi).preimage continuous_fst) (Module.finrank ℝ V) hinter q hq
  have he : (⋃ i ∈ S, U i) = {z : E × V | z.1 ∈ ⋃ i ∈ S, C i} := by
    ext z; simp [U]
  rw [he] at hz
  exact hz.of_iso (productPairBaseSubsetIso (⋃ i ∈ S, C i) ({0}ᶜ : Set V) q).symm

omit [FiniteDimensional ℝ E] in
/-- Over a path-connected base admitting a finite open convex cover,
the actual fiber projection is an isomorphism in fiber degree. -/
theorem convexOpenCover_product_projection_isIso
    (D : Set E) [PathConnectedSpace D] (S : Finset J) (C : J → Set E)
    (hopen : ∀ i ∈ S, IsOpen (C i)) (hconv : ∀ i ∈ S, Convex ℝ (C i))
    (hcover : (⋃ i ∈ S, C i) = D)
    (hv : 2 ≤ Module.finrank ℝ V) :
    IsIso (productPairProjection (B := D) ({0}ᶜ : Set V) (Module.finrank ℝ V)) := by
  let U : J → Set D := fun i => Subtype.val ⁻¹' C i
  have hsub : ∀ i ∈ S, C i ⊆ D := by
    intro i hi x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩
  have hcov : (⋃ i ∈ S, U i) = Set.univ := by
    ext x
    have hx : x.val ∈ ⋃ i ∈ S, C i := by rw [hcover]; exact x.property
    simpa only [U, mem_iUnion, mem_preimage, mem_univ, iff_true] using hx
  let n := Module.finrank ℝ V - 1
  have hn : n+1 = Module.finrank ℝ V := by dsimp [n]; omega
  have h := productPairProjection_isIso_of_finite_cover S U
    (fun i hi => (hopen i hi).preimage continuous_subtype_val) hcov
    (fun i hi hne => convexRestrictedBase_contractible D (C i) (hsub i hi) (hconv i hi) hne)
    ({0}ᶜ : Set V) n
    (fun T ht hts q hq => convexCover_product_intersection_below_isZero D S C
      hsub hconv T ht hts hv q (by omega))
  rwa [hn] at h

end

open CategoryTheory Limits Set
section
variable {E F V J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Fintype J]

omit [FiniteDimensional ℝ E] in
/-- Lower relative vanishing over a finite affine-zero complement,
proved by the explicit convex cover. All kernels may intersect. -/
theorem affineAvoidance_product_below_isZero (l : J → E →L[ℝ] F) (c : J → F)
    (hv : 2 ≤ Module.finrank ℝ V) (q : ℕ) (hq : q < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology (subspaceInclusion
      {z : affineAvoidanceSet l c × V | z.2 ≠ 0}) q) := by
  classical
  have h := convexOpenUnion_product_below_isZero
    (Finset.univ : Finset (J → Fin (Module.finrank ℝ F) × Bool)) (affineAvoidanceChart l c)
    (fun s _ => affineAvoidanceChart_open l c s)
    (fun s _ => affineAvoidanceChart_convex l c s) hv q hq
  have he : (⋃ i ∈ (Finset.univ : Finset (J → Fin (Module.finrank ℝ F) × Bool)),
      affineAvoidanceChart l c i) = affineAvoidanceSet l c := by
    simpa only [Finset.mem_univ, iUnion_true] using affineAvoidanceCharts_cover l c
  rw [he] at h
  exact h

omit [FiniteDimensional ℝ E] in
/-- In fiber degree, the actual projection over a path-connected
finite affine-zero complement is an isomorphism. -/
theorem affineAvoidance_product_projection_isIso (l : J → E →L[ℝ] F) (c : J → F)
    [PathConnectedSpace (affineAvoidanceSet l c)] (hv : 2 ≤ Module.finrank ℝ V) :
    IsIso (productPairProjection (B := affineAvoidanceSet l c) ({0}ᶜ : Set V)
      (Module.finrank ℝ V)) := by
  classical
  apply convexOpenCover_product_projection_isIso (affineAvoidanceSet l c)
    (Finset.univ : Finset (J → Fin (Module.finrank ℝ F) × Bool)) (affineAvoidanceChart l c)
    (fun s _ => affineAvoidanceChart_open l c s)
    (fun s _ => affineAvoidanceChart_convex l c s) _ hv
  simpa only [Finset.mem_univ, iUnion_true] using affineAvoidanceCharts_cover l c

end

end Kaplansky

end

end OAI
