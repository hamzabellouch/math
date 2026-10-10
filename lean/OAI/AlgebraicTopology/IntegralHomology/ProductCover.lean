import OAI.AlgebraicTopology.IntegralHomology.FiniteCover
import OAI.AlgebraicTopology.IntegralHomology.HyperplaneFiber
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

noncomputable section

namespace Kaplansky

/-! Product-pair fiber normalization, punctured products, and overlap generators. -/

section
open Set
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite signed halfspace cover, using actual continuous linear coordinates. -/
def signedCoordinateHalfspace (i : Fin (Module.finrank ℝ E) × Bool) : Set E :=
  if i.2 then {x | 0 < (Module.finBasis ℝ E).equivFunL x i.1}
  else {x | (Module.finBasis ℝ E).equivFunL x i.1 < 0}

theorem signedCoordinateHalfspace_open (i : Fin (Module.finrank ℝ E) × Bool) :
    IsOpen (signedCoordinateHalfspace i) := by
  have hc := (continuous_apply i.1).comp (Module.finBasis ℝ E).equivFunL.continuous
  cases h : i.2 <;> simp only [signedCoordinateHalfspace, h, Bool.false_eq_true,
    ↓reduceIte] <;> first | exact isOpen_lt hc continuous_const | exact isOpen_lt continuous_const hc

theorem signedCoordinateHalfspace_convex (i : Fin (Module.finrank ℝ E) × Bool) :
    Convex ℝ (signedCoordinateHalfspace i) := by
  let l : E →ₗ[ℝ] ℝ := (LinearMap.proj i.1).comp
    (Module.finBasis ℝ E).equivFunL.toLinearMap
  cases h : i.2
  · simpa [signedCoordinateHalfspace, h, l, Set.preimage, Function.comp_def, Function.eval] using
      (convex_Iio (0 : ℝ)).linear_preimage l
  · simpa [signedCoordinateHalfspace, h, l, Set.preimage, Function.comp_def, Function.eval] using
      (convex_Ioi (0 : ℝ)).linear_preimage l

/-- The signed coordinate halfspaces cover exactly the punctured space. -/
theorem signedCoordinateHalfspaces_cover :
    (⋃ i : Fin (Module.finrank ℝ E) × Bool, signedCoordinateHalfspace i) = ({0}ᶜ : Set E) := by
  ext x
  simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨i,b⟩,hi⟩ rfl
    cases b <;> simp [signedCoordinateHalfspace] at hi
  · intro hx
    have he : ∃ i, (Module.finBasis ℝ E).equivFunL x i ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hx
      apply (Module.finBasis ℝ E).equivFunL.injective
      ext i
      simpa using hn i
    obtain ⟨i,hi⟩ := he
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact ⟨(i,false), hi⟩
    · exact ⟨(i,true), hi⟩

/-- Every finite intersection is genuinely convex, hence contractible
whenever it is nonempty. -/
theorem signedCoordinateIntersection_convex
    (T : Finset (Fin (Module.finrank ℝ E) × Bool)) :
    Convex ℝ (⋂ i ∈ T, signedCoordinateHalfspace (E := E) i) :=
  convex_iInter (fun i => convex_iInter (fun _ => signedCoordinateHalfspace_convex i))

end

section
open CategoryTheory Limits Set
variable {E V : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
/-- A convex base, including the empty case, has no relative bundle
homology below the fiber dimension. -/
theorem convexBaseProductPair_below_isZero (C : Set E) (hC : Convex ℝ C)
    (hd : 2 ≤ Module.finrank ℝ V) (n : ℕ) (hn : n < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' {z : E × V | z.2 ≠ 0} : Set {z : E × V | z.1 ∈ C})) n) := by
  by_cases hc : C.Nonempty
  · let : ContractibleSpace C := hC.contractibleSpace hc
    exact ((localVectorHomology_isZero V hd n (by omega)).of_iso
      (productPairProjectionIso (B := C) ({0}ᶜ : Set V) n)).of_iso
        (relativeHomologyHomeomorphIso (firstCoordinateSubspaceHomeomorph C)
          _ {z : C × V | z.2 ≠ 0} (fun _ => Iff.rfl) n)
  · have : IsEmpty {z : E × V | z.1 ∈ C} :=
      ⟨fun z => hc ⟨z.1.1,z.2⟩⟩
    exact relativeHomology_isZero_empty _ n

/-- Actual relative homology over a punctured vector-space base vanishes
below the fiber dimension. This does NOT identify its top group or assert
that the punctured base is contractible. -/
theorem puncturedBaseProductPair_below_isZero
    (hd : 2 ≤ Module.finrank ℝ V) (n : ℕ) (hn : n < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology (subspaceInclusion
      {z : ({0}ᶜ : Set E) × V | z.2 ≠ 0}) n) := by
  classical
  let J := Fin (Module.finrank ℝ E) × Bool
  let U : J → Set (E × V) := fun i => {z | z.1 ∈ signedCoordinateHalfspace i}
  let A : Set (E × V) := {z | z.2 ≠ 0}
  have hopen : ∀ i ∈ (Finset.univ : Finset J), IsOpen (U i) :=
    fun i _ => (signedCoordinateHalfspace_open i).preimage continuous_fst
  have hinter : ∀ T : Finset J, T.Nonempty → T ⊆ Finset.univ → ∀ q < Module.finrank ℝ V,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q) := by
    intro T _ _ q hq
    have he : (⋂ i ∈ T, U i) = {z : E × V | z.1 ∈ ⋂ i ∈ T, signedCoordinateHalfspace i} := by
      ext z; simp [U]
    rw [he]
    exact convexBaseProductPair_below_isZero _ (signedCoordinateIntersection_convex T) hd q hq
  have hz := finiteRelativeOpenUnion_below_isZero Finset.univ U A hopen
    (Module.finrank ℝ V) hinter n hn
  have he : (⋃ i ∈ (Finset.univ : Finset J), U i) = {z : E × V | z.1 ∈ ({0}ᶜ : Set E)} := by
    ext z
    simp only [mem_iUnion, Finset.mem_univ, exists_true_left, U, mem_ofPred_eq]
    change (∃ i, z.1 ∈ signedCoordinateHalfspace i) ↔ z.1 ∈ ({0}ᶜ : Set E)
    rw [← mem_iUnion, signedCoordinateHalfspaces_cover]
  rw [he] at hz
  exact hz.of_iso (relativeHomologyHomeomorphIso
    (firstCoordinateSubspaceHomeomorph ({0}ᶜ : Set E))
    (Subtype.val ⁻¹' A) {z : ({0}ᶜ : Set E) × V | z.2 ≠ 0}
    (fun _ => Iff.rfl) n).symm

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- The actual canonical overlap has zero homology below its real fiber
rank. In particular this discharges the PRECEDING-overlap vanishing
hypothesis in the preserved normalization-gluing theorem. -/
theorem canonicalBundleOverlap_below_isZero (hp : 0 < ∑ i, K i)
    (n : ℕ) (hn : n < 2*(∑ i, K i)) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle :
        Set ↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K))) n) := by
  apply (puncturedBaseProductPair_below_isZero
    (E := ProjectiveProductModel K) (V := (Σ i, Fin (K i)) → ℂ) ?_ n ?_).of_iso
      (canonicalBundleOverlapRelativeIso K n)
  · rw [canonicalCoordinateSpace_real_finrank]
    omega
  · rwa [canonicalCoordinateSpace_real_finrank]

end

section
open CategoryTheory Limits
variable {B V : Type} [TopologicalSpace B] [TopologicalSpace V]

/-- Relative product coordinates over an arbitrary subset of the base. -/
def productPairBaseSubsetIso (C : Set B) (W : Set V) (n : ℕ) :=
  relativeHomologyHomeomorphIso (firstCoordinateSubspaceHomeomorph C)
    (Subtype.val ⁻¹' {z : B × V | z.2 ∈ W})
    {z : C × V | z.2 ∈ W} (fun _ => Iff.rfl) n

/-- A fiber inside a restricted product chart. -/
def productPairChartFiberMap (C : Set B) (b : C) (W : Set V) (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion W)
    (subspaceInclusion (Subtype.val ⁻¹' {z : B × V | z.2 ∈ W} : Set {z : B × V | z.1 ∈ C}))
    (subspaceMap _ _
      ⟨fun v => ⟨(b.1,v),b.2⟩,(continuous_const.prodMk continuous_id).subtype_mk _⟩
      (fun _ h => h))
    (TopCat.ofHom
      ⟨fun v => ⟨(b.1,v),b.2⟩,(continuous_const.prodMk continuous_id).subtype_mk _⟩) (by rfl) n

theorem productPairChartFiberMap_coordinates (C : Set B) (b : C) (W : Set V) (n : ℕ) :
    productPairChartFiberMap C b W n ≫ (productPairBaseSubsetIso C W n).hom =
      productPairFiberMap b W n := by
  unfold productPairChartFiberMap productPairBaseSubsetIso productPairFiberMap
  erw [relativeHomologyHomeomorphIso_hom]
  erw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

theorem productPairChartFiberMap_isIso (C : Set B) [ContractibleSpace C]
    (b : C) (W : Set V) (n : ℕ) : IsIso (productPairChartFiberMap C b W n) := by
  have : IsIso (productPairFiberMap b W n) := by
    rw [productPairFiberMap_eq_inv]
    infer_instance
  have : IsIso (productPairChartFiberMap C b W n ≫ (productPairBaseSubsetIso C W n).hom) := by
    rw [productPairChartFiberMap_coordinates]
    infer_instance
  exact IsIso.of_isIso_comp_right (productPairChartFiberMap C b W n)
    (productPairBaseSubsetIso C W n).hom

/-- Inclusion of a chart fiber is literally the same global fiber inclusion. -/
theorem productPairChartFiberMap_inclusion (C : Set B) (b : C) (W : Set V) (n : ℕ) :
    productPairChartFiberMap C b W n ≫
      restrictedPairToAmbientHomologyMap {z : B × V | z.1 ∈ C} {z | z.2 ∈ W} n =
    productPairFiberMap b.1 W n := by
  unfold productPairChartFiberMap productPairFiberMap
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n = _
  erw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

end

section
open CategoryTheory Limits Set

section
variable {B V ι : Type} [TopologicalSpace B] [TopologicalSpace V] [PathConnectedSpace B]

/-- A finite cover by contractible base charts proves fiber generation in
the first potentially nonzero relative degree, provided the preceding
intersection groups vanish. All maps are the actual product projection and
fiber inclusion; path connectedness fixes the SAME fiber class on all charts. -/
theorem productPairProjection_fiber_of_finite_cover (S : Finset ι) (U : ι → Set B)
    (hopen : ∀ i ∈ S, IsOpen (U i)) (hcover : (⋃ i ∈ S, U i) = Set.univ)
    (hchart : ∀ i ∈ S, (U i).Nonempty → ContractibleSpace (U i))
    (W : Set V) (n : ℕ)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion {z : (⋂ i ∈ T, U i) × V | z.2 ∈ W}) q))
    (b : B) :
    productPairProjection (B := B) W (n+1) ≫ productPairFiberMap b W (n+1) = 𝟙 _ := by
  let C : ι → Set (B × V) := fun i => {z | z.1 ∈ U i}
  let A : Set (B × V) := {z | z.2 ∈ W}
  have hC : (⋃ i ∈ S, C i) = Set.univ := by
    ext z
    have hb : z.1 ∈ ⋃ i ∈ S, U i := by rw [hcover]; trivial
    simpa only [mem_iUnion, C, mem_ofPred_eq, mem_univ, iff_true] using hb
  refine finiteRelativeOpenCover_hom_ext S C A
    (fun i hi => (hopen i hi).preimage continuous_fst) hC n ?_ _ _ ?_
  · intro T ht hts q hq
    have he : (⋂ i ∈ T, C i) = {z : B × V | z.1 ∈ ⋂ i ∈ T, U i} := by ext z; simp [C]
    rw [he]
    exact (hinter T ht hts q hq).of_iso (productPairBaseSubsetIso (⋂ i ∈ T, U i) W q)
  · intro i hi
    by_cases hne : (U i).Nonempty
    · let : ContractibleSpace (U i) := hchart i hi hne
      let c : U i := ⟨hne.choose,hne.choose_spec⟩
      have := productPairChartFiberMap_isIso (U i) c W (n+1)
      apply (cancel_epi (productPairChartFiberMap (U i) c W (n+1))).mp
      change productPairChartFiberMap (U i) c W (n+1) ≫
          (restrictedPairToAmbientHomologyMap _ _ _ ≫
            (productPairProjection W (n+1) ≫ productPairFiberMap b W (n+1))) =
        productPairChartFiberMap (U i) c W (n+1) ≫
          (restrictedPairToAmbientHomologyMap _ _ _ ≫ 𝟙 _)
      rw [← Category.assoc, productPairChartFiberMap_inclusion, ← Category.assoc,
        productPairFiberMap_projection, Category.id_comp, Category.comp_id,
        productPairChartFiberMap_inclusion]
      exact productPairFiberMap_eq_of_joined (PathConnectedSpace.joined b c.1) W (n+1)
    · have : IsEmpty (C i) := ⟨fun z => hne ⟨z.1.1,z.2⟩⟩
      exact (relativeHomology_isZero_empty (Subtype.val ⁻¹' A : Set (C i)) (n+1)).eq_of_src _ _

/-- In this degree the actual product projection is an isomorphism. -/
theorem productPairProjection_isIso_of_finite_cover (S : Finset ι) (U : ι → Set B)
    (hopen : ∀ i ∈ S, IsOpen (U i)) (hcover : (⋃ i ∈ S, U i) = Set.univ)
    (hchart : ∀ i ∈ S, (U i).Nonempty → ContractibleSpace (U i))
    (W : Set V) (n : ℕ)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion {z : (⋂ i ∈ T, U i) × V | z.2 ∈ W}) q)) :
    IsIso (productPairProjection (B := B) W (n+1)) := by
  let b : B := Classical.choice (inferInstance : Nonempty B)
  exact ⟨⟨productPairFiberMap b W (n+1),
    productPairProjection_fiber_of_finite_cover S U hopen hcover hchart W n hinter b,
    productPairFiberMap_projection b W (n+1)⟩⟩

end

variable {E V : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Signed halfspaces avoid the origin. -/
theorem signedCoordinateHalfspace_subset_punctured
    (i : Fin (Module.finrank ℝ E) × Bool) :
    signedCoordinateHalfspace i ⊆ ({0}ᶜ : Set E) := by
  intro x hx
  rw [← signedCoordinateHalfspaces_cover]
  exact mem_iUnion.mpr ⟨i,hx⟩

/-- In the real fiber dimension, projection from the punctured-base
product pair is an isomorphism. Both base and fiber have dimension at least
two. This is proved by finite convex charts, relative vanishing and path
transport of actual fiber inclusions, not by a Künneth or Thom assumption. -/
theorem puncturedBaseProductPairProjection_isIso
    (he : 2 ≤ Module.finrank ℝ E) (hv : 2 ≤ Module.finrank ℝ V) :
    IsIso (productPairProjection (B := ({0}ᶜ : Set E)) ({0}ᶜ : Set V)
      (Module.finrank ℝ V)) := by
  classical
  let := puncturedVector_pathConnected_of_finrank E he
  let J := Fin (Module.finrank ℝ E) × Bool
  let U : J → Set ({0}ᶜ : Set E) := fun i => Subtype.val ⁻¹' signedCoordinateHalfspace i
  have hopen : ∀ i ∈ (Finset.univ : Finset J), IsOpen (U i) :=
    fun i _ => (signedCoordinateHalfspace_open i).preimage continuous_subtype_val
  have hcover : (⋃ i ∈ (Finset.univ : Finset J), U i) = Set.univ := by
    ext x
    have hx : ∃ i : J, x.val ∈ signedCoordinateHalfspace i := by
      rw [← mem_iUnion, signedCoordinateHalfspaces_cover]
      exact x.property
    simpa [U] using hx
  have hchart : ∀ i ∈ (Finset.univ : Finset J), (U i).Nonempty → ContractibleSpace (U i) := by
    intro i _ hi
    have : ContractibleSpace (signedCoordinateHalfspace (E := E) i) :=
      (signedCoordinateHalfspace_convex i).contractibleSpace ⟨hi.choose.val,hi.choose_spec⟩
    exact (subspaceSubsetHomeomorph (signedCoordinateHalfspace i) ({0}ᶜ : Set E)
      (signedCoordinateHalfspace_subset_punctured i)).contractibleSpace
  let n := Module.finrank ℝ V - 1
  have hn : n+1 = Module.finrank ℝ V := by dsimp [n]; omega
  have hinter : ∀ T : Finset J, T.Nonempty → T ⊆ Finset.univ → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion {z : (⋂ i ∈ T, U i) × V | z.2 ∈ ({0}ᶜ : Set V)}) q) := by
    intro T ht _ q hq
    let D : Set E := ⋂ i ∈ T, signedCoordinateHalfspace i
    have hD : D ⊆ ({0}ᶜ : Set E) := by
      obtain ⟨i,hi⟩ := ht
      intro x hx
      exact signedCoordinateHalfspace_subset_punctured i
        (mem_iInter.mp (mem_iInter.mp hx i) hi)
    have heq : (⋂ i ∈ T, U i) = (Subtype.val ⁻¹' D : Set ({0}ᶜ : Set E)) := by
      ext x; simp [U,D]
    let e : (⋂ i ∈ T, U i) ≃ₜ D :=
      (Homeomorph.setCongr heq).trans (subspaceSubsetHomeomorph D ({0}ᶜ : Set E) hD)
    by_cases hd : D.Nonempty
    · have : ContractibleSpace D := (signedCoordinateIntersection_convex T).contractibleSpace hd
      have : ContractibleSpace (⋂ i ∈ T, U i) := e.contractibleSpace
      exact (localVectorHomology_isZero V hv q (by omega)).of_iso
        (productPairProjectionIso (B := (⋂ i ∈ T, U i)) ({0}ᶜ : Set V) q)
    · have : IsEmpty ((⋂ i ∈ T, U i) × V) :=
        ⟨fun z => hd ⟨(e z.1).val,(e z.1).property⟩⟩
      exact relativeHomology_isZero_empty _ q
  have h := productPairProjection_isIso_of_finite_cover Finset.univ U hopen hcover hchart
    ({0}ᶜ : Set V) n hinter
  rwa [hn] at h

end

open Bundle Topology CategoryTheory Limits
section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- The ACTUAL overlap-to-chart map is an isomorphism in the fiber degree.
This assertion is confined to that degree. -/
theorem canonicalOverlapChartMap_isIso (hp : 0 < ∑ i, K i) :
    IsIso (canonicalOverlapChartMap K (2*(∑ i, K i))) := by
  have hpiso : IsIso (productPairProjection (B := ({0}ᶜ : Set (ProjectiveProductModel K)))
      ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ)) (2*(∑ i, K i))) := by
    have h := puncturedBaseProductPairProjection_isIso
      (E := ProjectiveProductModel K) (V := (Σ i, Fin (K i)) → ℂ)
      (by rw [projectiveProduct_real_finrank]; omega)
      (by rw [canonicalCoordinateSpace_real_finrank]; omega)
    rwa [canonicalCoordinateSpace_real_finrank] at h
  have : IsIso (canonicalOverlapChartMap K (2*(∑ i, K i)) ≫
      (canonicalBundleCoverChartIso K _).inv ≫ (canonicalBundleChartFiberIso K _).hom) := by
    change IsIso (restrictedPairHomologyMap _ _ _ ≫ _ ≫ _)
    rw [canonicalBundleOverlap_fiber_comparison]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (canonicalBundleOverlapRelativeIso K _).isIso_hom hpiso
  exact IsIso.of_isIso_comp_right (canonicalOverlapChartMap K (2*(∑ i, K i)))
    ((canonicalBundleCoverChartIso K _).inv ≫ (canonicalBundleChartFiberIso K _).hom)

/-- The overlap normalization is an actual isomorphism to ℤ, using the
incoming chart generator, not an independently chosen orientation. -/
theorem canonicalOverlapNormalization_isIso (hp : 0 < ∑ i, K i) :
    IsIso (canonicalOverlapNormalization K hp) := by
  have := canonicalOverlapChartMap_isIso K hp
  unfold canonicalOverlapNormalization
  infer_instance

def canonicalOverlapTopIso (hp : 0 < ∑ i, K i) :=
  @asIso _ _ _ _ (canonicalOverlapNormalization K hp) (canonicalOverlapNormalization_isIso K hp)

/-- The unique overlap class with preserved normalization one. -/
def canonicalNormalizedOverlapGenerator (hp : 0 < ∑ i, K i) :=
  (canonicalOverlapTopIso K hp).inv (1 : ℤ)

theorem canonicalNormalizedOverlapGenerator_coordinate (hp : 0 < ∑ i, K i) :
    canonicalOverlapNormalization K hp (canonicalNormalizedOverlapGenerator K hp) = (1 : ℤ) :=
  (canonicalOverlapTopIso K hp).inv_hom_id_apply 1

theorem canonicalNormalizedOverlapGenerator_unique (hp : 0 < ∑ i, K i)
    (w : relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle :
        Set ↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K))) (2*(∑ i, K i))) :
    canonicalOverlapNormalization K hp w = (1 : ℤ) ↔
      w = canonicalNormalizedOverlapGenerator K hp := by
  rw [← canonicalNormalizedOverlapGenerator_coordinate K hp]
  exact (ModuleCat.mono_iff_injective (canonicalOverlapTopIso K hp).hom).mp inferInstance |>.eq_iff

theorem canonicalNormalizedOverlapGenerator_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalNormalizedOverlapGenerator K hp ≠ 0 := by
  intro hz
  have h := canonicalNormalizedOverlapGenerator_coordinate K hp
  rw [hz,map_zero] at h
  exact Int.zero_ne_one h

theorem canonicalNormalizedOverlapGenerator_spans (hp : 0 < ∑ i, K i)
    (w : relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle :
        Set ↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K))) (2*(∑ i, K i))) :
    (canonicalOverlapNormalization K hp w : ℤ) • canonicalNormalizedOverlapGenerator K hp = w := by
  apply (ModuleCat.mono_iff_injective (canonicalOverlapTopIso K hp).hom).mp inferInstance
  change canonicalOverlapNormalization K hp (_ • _) = canonicalOverlapNormalization K hp w
  rw [map_zsmul, canonicalNormalizedOverlapGenerator_coordinate]
  exact mul_one _

/-- The incoming global survival problem reduces to the image of this
ONE proved primitive overlap class. Its image in the punctured bundle is
still a global obligation, not supplied by the overlap isomorphism. -/
theorem canonicalFiberGenerator_zero_iff_overlapGenerator (hp : 0 < ∑ i, K i) :
    canonicalWholeBundleFiberMap K (2*(∑ i, K i)) (canonicalFiberGenerator K hp) = 0 ↔
      canonicalOverlapPuncturedMap K (2*(∑ i, K i))
        (canonicalNormalizedOverlapGenerator K hp) = 0 := by
  rw [canonicalFiberGenerator_zero_iff_normalized_overlap]
  constructor
  · rintro ⟨w,hw,hz⟩
    rw [(canonicalNormalizedOverlapGenerator_unique K hp w).mp hw] at hz
    exact hz
  · intro hz
    exact ⟨canonicalNormalizedOverlapGenerator K hp,
      canonicalNormalizedOverlapGenerator_coordinate K hp,hz⟩

end

end Kaplansky

end

end OAI
