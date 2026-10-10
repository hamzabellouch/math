import OAI.AlgebraicTopology.IntegralHomology.MayerVietoris
import OAI.AlgebraicTopology.IntegralHomology.OpenUnion

namespace OAI

noncomputable section

namespace Kaplansky

/-! Relative maps and vanishing and gluing over finite open covers. -/

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X]

/-- Relative homology of an empty ambient space is zero in every degree. -/
theorem relativeHomology_isZero_empty [IsEmpty X] (A : Set X) (n : ℕ) :
    IsZero (relativeSingularHomology (subspaceInclusion A) n) := by
  have : IsIso (subspaceInclusion A) := by
    exact (TopCat.isoOfHomeo (X := TopCat.of A) (Y := TopCat.of X) (show A ≃ₜ X from
      { toFun := Subtype.val
        invFun := fun x => isEmptyElim x
        left_inv := fun x => isEmptyElim x.val
        right_inv := fun x => isEmptyElim x
        continuous_toFun := continuous_subtype_val
        continuous_invFun := continuous_of_discreteTopology })).isIso_hom
  have : IsIso (integralSingularChains.map (subspaceInclusion A)) := by infer_instance
  exact (homologyFunctor _ _ n).map_isZero
    (isZero_cokernel_of_epi (integralSingularChains.map (subspaceInclusion A)))

/-- The relative two-chart sum is surjective also in degree zero. There
is no spurious degree-minus-one overlap hypothesis. -/
theorem relativeOpenCover_sum_epi_zero (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    Epi (relativeMayerVietorisSumSequence U V A 0).g := by
  have : Epi (relativeCoverChainSequence U V A).g :=
    (relativeCoverChainSequence_shortExact U V A).epi_g
  have hepi : Epi (homologyMap (relativeCoverChainSequence U V A).g 0) :=
    epi_homologyMap_of_epi_of_not_rel _ 0 (by intro j; simp)
  have hiso : IsIso (homologyMap (relativeCoverChainComparison U V A) 0) := by
    change IsIso (relativeOpenCoverHomologyIso U V A hU hV hcover 0).hom
    infer_instance
  have : Epi ((relativeCoverMiddleHomologyIso U V A 0).hom ≫
      (relativeMayerVietorisSumSequence U V A 0).g) := by
    change Epi ((relativeCoverMiddleHomologyIso U V A 0).hom ≫ biprod.desc _ _)
    erw [relativeCoverMiddleHomologyIso_map]
    exact epi_comp' hepi (@IsIso.epi_of_iso _ _ _ _ _ hiso)
  exact epi_of_epi (relativeCoverMiddleHomologyIso U V A 0).hom _

theorem relativeOpenCover_zero_isZero (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hu : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) 0))
    (hv : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) 0)) :
    IsZero (relativeSingularHomology (subspaceInclusion A) 0) := by
  have := relativeOpenCover_sum_epi_zero U V A hU hV hcover
  have hg : (relativeMayerVietorisSumSequence U V A 0).g = 0 := by
    dsimp only [relativeMayerVietorisSumSequence]
    apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc]
    · exact hu.eq_of_src _ _
    · exact hv.eq_of_src _ _
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_epi (relativeMayerVietorisSumSequence U V A 0).g).mp
  erw [hg, zero_comp]

/-- Nested restrictions give the same actual pair, with ambient subspace
topology and the same removed set. -/
def restrictedPairSubsetIso (U W A : Set X) (h : U ⊆ W) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' (Subtype.val ⁻¹' A : Set W) : Set (Subtype.val ⁻¹' U : Set W))) n ≅
    relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n :=
  relativeHomologyHomeomorphIso (subspaceSubsetHomeomorph U W h)
    (Subtype.val ⁻¹' (Subtype.val ⁻¹' A : Set W) : Set (Subtype.val ⁻¹' U : Set W))
    (Subtype.val ⁻¹' A : Set U) (fun _ => Iff.rfl) n

/-- Uniform vanishing below r is preserved by a two-set open union. -/
theorem relativeOpenUnion_below_isZero (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (r : ℕ)
    (hu : ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n))
    (hv : ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) n))
    (hi : ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n)) :
    ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∪ V))) n) := by
  let U' : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let V' : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  have hcov : U' ∪ V' = Set.univ := by ext x; exact iff_true_intro x.property
  have hu' n hn := (hu n hn).of_iso
    (restrictedPairSubsetIso U (U ∪ V) A Set.subset_union_left n)
  have hv' n hn := (hv n hn).of_iso
    (restrictedPairSubsetIso V (U ∪ V) A Set.subset_union_right n)
  have hi' n hn := (hi n hn).of_iso
    (restrictedPairSubsetIso (U ∩ V) (U ∪ V) A
      (fun _ h => Or.inl h.1) n)
  intro n hn
  cases n with
  | zero =>
    exact relativeOpenCover_zero_isZero U' V' _
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
      hcov (hu' 0 hn) (hv' 0 hn)
  | succ n =>
    exact relativeOpenCover_isZero U' V' _
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
      hcov n (hu' (n+1) hn) (hv' (n+1) hn) (hi' n (by omega))

end

section
open CategoryTheory Limits Set
variable {X ι : Type} [TopologicalSpace X]

/-- Uniform relative vanishing below r on all nonempty finite intersections
implies the same bound on their union. The empty union and degree zero are
included, and there is no loss depending on the number of charts. -/
theorem finiteRelativeOpenUnion_below_isZero (S : Finset ι) (U : ι → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i)) (r : ℕ)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ n < r,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) n)) :
    ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U i))) n) := by
  classical
  induction S using Finset.induction_on generalizing U with
  | empty =>
    intro n _
    have he : (⋃ i ∈ (∅ : Finset ι), U i) = ∅ := by simp
    rw [he]
    exact relativeHomology_isZero_empty _ n
  | @insert a S ha ih =>
    by_cases hs : S.Nonempty
    · have hU : ∀ n < r, IsZero (relativeSingularHomology
          (subspaceInclusion (Subtype.val ⁻¹' A : Set (U a))) n) := by
        have he : (⋂ i ∈ ({a} : Finset ι), U i) = U a := by ext x; simp
        have hz := hinter {a} (by simp) (by simp)
        rw [he] at hz
        exact hz
      have hV := ih U (fun i hi => hopen i (Finset.mem_insert_of_mem hi))
        (fun T ht hts n hn => hinter T ht (hts.trans (Finset.subset_insert a S)) n hn)
      have hI : ∀ n < r, IsZero (relativeSingularHomology
          (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U a ∩ U i))) n) := by
        apply ih (fun i => U a ∩ U i)
          (fun i hi => (hopen a (by simp)).inter (hopen i (Finset.mem_insert_of_mem hi)))
        intro T ht hts n hn
        have hb := hinter (insert a T) (by simp) (Finset.insert_subset_insert a hts) n hn
        have he : (⋂ i ∈ T, U a ∩ U i) = ⋂ i ∈ insert a T, U i := by
          ext x
          simp only [mem_iInter, Finset.mem_insert]
          constructor
          · intro hx i hi
            rcases hi with rfl | hi
            · obtain ⟨j,hj⟩ := ht
              exact (hx j hj).1
            · exact (hx i hi).2
          · intro hx i hi
            exact ⟨hx a (Or.inl rfl), hx i (Or.inr hi)⟩
        rw [he]
        exact hb
      have heI : (⋃ i ∈ S, U a ∩ U i) = U a ∩ (⋃ i ∈ S, U i) := by
        ext x
        simp only [mem_iUnion, mem_inter_iff]
        constructor
        · rintro ⟨i,hi,hxa,hxi⟩
          exact ⟨hxa,i,hi,hxi⟩
        · rintro ⟨hxa,i,hi,hxi⟩
          exact ⟨i,hi,hxa,hxi⟩
      rw [heI] at hI
      have heW : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by ext x; simp
      rw [heW]
      exact relativeOpenUnion_below_isZero (U a) (⋃ i ∈ S, U i) A
        (hopen a (by simp))
        (isOpen_iUnion (fun i => isOpen_iUnion (fun hi => hopen i (Finset.mem_insert_of_mem hi))))
        r hU hV hI
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst S
      have hz := hinter {a} (by simp) (by simp)
      have hea : (⋂ i ∈ ({a} : Finset ι), U i) = U a := by ext x; simp
      have heb : (⋃ i ∈ insert a (∅ : Finset ι), U i) = U a := by ext x; simp
      rw [hea] at hz
      rw [heb]
      exact hz

end

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X]

theorem restrictedPairHomologyMap_comp {U V W : Set X}
    (h : U ⊆ V) (k : V ⊆ W) (A : Set X) (n : ℕ) :
    restrictedPairHomologyMap h A n ≫ restrictedPairHomologyMap k A n =
      restrictedPairHomologyMap (h.trans k) A n := by
  unfold restrictedPairHomologyMap
  erw [← homologyMap_comp]
  congr 1
  unfold restrictedPairChainMap
  erw [relativeChainMap_comp]
  rfl

/-- Actual inclusion after eliminating a redundant enclosing subtype. -/
theorem restrictedPairSubsetIso_toAmbient (U W A : Set X) (h : U ⊆ W) (n : ℕ) :
    (restrictedPairSubsetIso U W A h n).hom ≫ restrictedPairHomologyMap h A n =
      restrictedPairToAmbientHomologyMap (Subtype.val ⁻¹' U : Set W) (Subtype.val ⁻¹' A) n := by
  unfold restrictedPairSubsetIso
  erw [relativeHomologyHomeomorphIso_hom]
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n = _
  erw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- Maps out of a restricted open union are determined on its two actual
subsets when the preceding relative overlap group vanishes. -/
theorem relativeOpenUnion_hom_ext (U V A : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (n : ℕ) (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∪ V))) (n+1) ⟶ Z)
    (hu : restrictedPairHomologyMap (Set.subset_union_left : U ⊆ U ∪ V) A (n+1) ≫ f =
      restrictedPairHomologyMap (Set.subset_union_left : U ⊆ U ∪ V) A (n+1) ≫ g)
    (hv : restrictedPairHomologyMap (Set.subset_union_right : V ⊆ U ∪ V) A (n+1) ≫ f =
      restrictedPairHomologyMap (Set.subset_union_right : V ⊆ U ∪ V) A (n+1) ≫ g) : f = g := by
  let U' : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let V' : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  have hcov : U' ∪ V' = Set.univ := by ext x; exact iff_true_intro x.property
  apply relativeOpenCover_hom_ext U' V' (Subtype.val ⁻¹' A)
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val) hcov n
    (hi.of_iso (restrictedPairSubsetIso (U ∩ V) (U ∪ V) A
      (fun _ h => Or.inl h.1) n)) f g
  · rw [← restrictedPairSubsetIso_toAmbient U (U ∪ V) A Set.subset_union_left,
      Category.assoc, Category.assoc, hu]
  · rw [← restrictedPairSubsetIso_toAmbient V (U ∪ V) A Set.subset_union_right,
      Category.assoc, Category.assoc, hv]

end

section
open CategoryTheory Limits Set

section
variable {X ι : Type} [TopologicalSpace X]

/-- The actual chart inclusions jointly detect maps out of a finite open
union in degree n+1 if every intersection vanishes in degrees at most n. -/
theorem finiteRelativeOpenUnion_hom_ext (S : Finset ι) (U : ι → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i)) (n : ℕ)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U i))) (n+1) ⟶ Z)
    (hfg : ∀ i (_ : i ∈ S) (h : U i ⊆ ⋃ j ∈ S, U j),
      restrictedPairHomologyMap h A (n+1) ≫ f =
      restrictedPairHomologyMap h A (n+1) ≫ g) : f = g := by
  classical
  induction S using Finset.induction_on generalizing U with
  | empty =>
    have he : (⋃ i ∈ (∅ : Finset ι), U i) = ∅ := by simp
    have hz : IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ (∅ : Finset ι), U i))) (n+1)) := by
      rw [he]
      exact relativeHomology_isZero_empty _ _
    exact hz.eq_of_src f g
  | @insert a S ha ih =>
    have hI : IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U a ∩ U i))) n) := by
      apply finiteRelativeOpenUnion_below_isZero S (fun i => U a ∩ U i) A
        (fun i hi => (hopen a (by simp)).inter (hopen i (Finset.mem_insert_of_mem hi))) (n+1)
        ?_ n (by omega)
      intro T ht hts q hq
      have hb := hinter (insert a T) (by simp) (Finset.insert_subset_insert a hts) q hq
      have he : (⋂ i ∈ T, U a ∩ U i) = ⋂ i ∈ insert a T, U i := by
        ext x
        simp only [mem_iInter, Finset.mem_insert]
        constructor
        · intro hx i hi
          rcases hi with rfl | hi
          · obtain ⟨j,hj⟩ := ht
            exact (hx j hj).1
          · exact (hx i hi).2
        · intro hx i hi
          exact ⟨hx a (Or.inl rfl), hx i (Or.inr hi)⟩
      rw [he]
      exact hb
    have heI : (⋃ i ∈ S, U a ∩ U i) = U a ∩ (⋃ i ∈ S, U i) := by
      ext x
      simp only [mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨i,hi,hxa,hxi⟩
        exact ⟨hxa,i,hi,hxi⟩
      · rintro ⟨hxa,i,hi,hxi⟩
        exact ⟨i,hi,hxa,hxi⟩
    rw [heI] at hI
    have heW : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by ext x; simp
    revert f g hfg
    rw [heW]
    intro f g hfg
    apply relativeOpenUnion_hom_ext (U a) (⋃ i ∈ S, U i) A (hopen a (by simp))
      (isOpen_iUnion (fun i => isOpen_iUnion (fun hi => hopen i (Finset.mem_insert_of_mem hi)))) n hI f g
    · exact hfg a (by simp) Set.subset_union_left
    · apply ih U (fun i hi => hopen i (Finset.mem_insert_of_mem hi))
        (fun T ht hts q hq => hinter T ht (hts.trans (Finset.subset_insert a S)) q hq)
      intro i hi h
      simp only [← Category.assoc, restrictedPairHomologyMap_comp]
      exact hfg i (Finset.mem_insert_of_mem hi) (h.trans Set.subset_union_right)

end

section
variable {X : Type} [TopologicalSpace X]

theorem restrictedPairSubsetIso_map (U V W A : Set X)
    (hUV : U ⊆ V) (hVW : V ⊆ W) (n : ℕ) :
    (restrictedPairSubsetIso U W A (hUV.trans hVW) n).hom ≫
      restrictedPairHomologyMap hUV A n =
    restrictedPairHomologyMap (preimage_mono hUV :
      (Subtype.val ⁻¹' U : Set W) ⊆ Subtype.val ⁻¹' V) (Subtype.val ⁻¹' A) n ≫
      (restrictedPairSubsetIso V W A hVW n).hom := by
  unfold restrictedPairSubsetIso
  erw [relativeHomologyHomeomorphIso_hom, relativeHomologyHomeomorphIso_hom]
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n =
    relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n
  erw [relativeHomologyMap_comp, relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- Compatible linear maps on two open subspaces glue to a map on
their union when the preceding overlap homology is zero. -/
theorem relativeOpenUnion_exists_glue (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (u : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) (n+1) ⟶ Z)
    (v : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) (n+1) ⟶ Z)
    (hcompat : restrictedPairHomologyMap (inter_subset_left : U ∩ V ⊆ U) A (n+1) ≫ u =
      restrictedPairHomologyMap (inter_subset_right : U ∩ V ⊆ V) A (n+1) ≫ v) :
    ∃ f : relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∪ V))) (n+1) ⟶ Z,
      restrictedPairHomologyMap (subset_union_left : U ⊆ U ∪ V) A (n+1) ≫ f = u ∧
      restrictedPairHomologyMap (subset_union_right : V ⊆ U ∪ V) A (n+1) ≫ f = v := by
  let U' : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let V' : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  let A' : Set ↥(U ∪ V) := Subtype.val ⁻¹' A
  have hcov : U' ∪ V' = univ := by ext x; exact iff_true_intro x.property
  let eu := restrictedPairSubsetIso U (U ∪ V) A subset_union_left (n+1)
  let ev := restrictedPairSubsetIso V (U ∪ V) A subset_union_right (n+1)
  have hi' : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A' : Set ↥(U' ∩ V'))) n) :=
    hi.of_iso (restrictedPairSubsetIso (U ∩ V) (U ∪ V) A
      (fun _ hx => Or.inl hx.1) n)
  have hc : restrictedPairHomologyMap (inter_subset_left : U' ∩ V' ⊆ U') A' (n+1) ≫
        (eu.hom ≫ u) =
      restrictedPairHomologyMap (inter_subset_right : U' ∩ V' ⊆ V') A' (n+1) ≫
        (ev.hom ≫ v) := by
    rw [← Category.assoc, ← Category.assoc]
    change (_ ≫ (restrictedPairSubsetIso U (U ∪ V) A _ _).hom) ≫ u =
      (_ ≫ (restrictedPairSubsetIso V (U ∪ V) A _ _).hom) ≫ v
    erw [← restrictedPairSubsetIso_map (U ∩ V) U (U ∪ V) A inter_subset_left subset_union_left,
      ← restrictedPairSubsetIso_map (U ∩ V) V (U ∪ V) A inter_subset_right subset_union_right]
    erw [Category.assoc, Category.assoc, hcompat]
  let f := relativeOpenCoverGlue U' V' A'
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    hcov n hi' (eu.hom ≫ u) (ev.hom ≫ v) hc
  have hf := relativeOpenCoverGlue_restrictions U' V' A'
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    hcov n hi' (eu.hom ≫ u) (ev.hom ≫ v) hc
  refine ⟨f, ?_, ?_⟩
  · apply (cancel_epi eu.hom).mp
    rw [← Category.assoc]
    change ((restrictedPairSubsetIso U (U ∪ V) A _ _).hom ≫ _) ≫ f = _
    rw [restrictedPairSubsetIso_toAmbient]
    exact hf.1
  · apply (cancel_epi ev.hom).mp
    rw [← Category.assoc]
    change ((restrictedPairSubsetIso V (U ∪ V) A _ _).hom ≫ _) ≫ f = _
    rw [restrictedPairSubsetIso_toAmbient]
    exact hf.2

end

variable {X ι : Type} [TopologicalSpace X]

/-- Restricting a pair to the whole ambient set changes no homology. -/
theorem restrictedPairToAmbient_univ_isIso (A : Set X) (n : ℕ) :
    IsIso (restrictedPairToAmbientHomologyMap Set.univ A n) := by
  let e := relativeHomologyHomeomorphIso (Homeomorph.Set.univ X)
    (Subtype.val ⁻¹' A) A (fun _ => Iff.rfl) n
  have he : restrictedPairToAmbientHomologyMap Set.univ A n = e.hom := by
    erw [relativeHomologyHomeomorphIso_hom]
    apply relativeHomologyMap_congr_ambient
    rfl
  rw [he]
  infer_instance

/-- Finite chart detection for the whole actual pair. -/
theorem finiteRelativeOpenCover_hom_ext (S : Finset ι) (U : ι → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i))
    (hcover : (⋃ i ∈ S, U i) = Set.univ) (n : ℕ)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology (subspaceInclusion A) (n+1) ⟶ Z)
    (hfg : ∀ i ∈ S, restrictedPairToAmbientHomologyMap (U i) A (n+1) ≫ f =
      restrictedPairToAmbientHomologyMap (U i) A (n+1) ≫ g) : f = g := by
  have : IsIso (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1)) := by
    rw [hcover]
    exact restrictedPairToAmbient_univ_isIso A (n+1)
  apply (cancel_epi (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1))).mp
  apply finiteRelativeOpenUnion_hom_ext S U A hopen n hinter
  intro i hi h
  simp only [← Category.assoc, restrictedPairHomologyMap_toAmbient]
  exact hfg i hi

end

open CategoryTheory Limits Set
section
variable {X J : Type} [TopologicalSpace X]

/-- Pairwise compatible normalizations on a finite open cover glue in
the first possibly nonzero relative degree. All inclusions are the actual
restricted-pair maps; no extension of a homomorphism is postulated. -/
theorem finiteRelativeOpenUnion_exists_glue (S : Finset J) (U : J → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i)) (n : ℕ)
    (hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (u : ∀ i, relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set (U i))) (n+1) ⟶ Z)
    (hc : ∀ i ∈ S, ∀ j ∈ S,
      restrictedPairHomologyMap (inter_subset_left : U i ∩ U j ⊆ U i) A (n+1) ≫ u i =
      restrictedPairHomologyMap (inter_subset_right : U i ∩ U j ⊆ U j) A (n+1) ≫ u j) :
    ∃ f : relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U i))) (n+1) ⟶ Z,
      ∀ i (_ : i ∈ S) (h : U i ⊆ ⋃ j ∈ S, U j),
        restrictedPairHomologyMap h A (n+1) ≫ f = u i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,fun i hi => (Finset.notMem_empty i hi).elim⟩
  | @insert a S ha ih =>
    obtain ⟨v,hv⟩ := ih (fun i hi => hopen i (Finset.mem_insert_of_mem hi))
      (fun T ht hts q hq => hinter T ht (hts.trans (Finset.subset_insert a S)) q hq)
      (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    let C : J → Set X := fun i => U a ∩ U i
    have hCopen : ∀ i ∈ S, IsOpen (C i) :=
      fun i hi => (hopen a (by simp)).inter (hopen i (Finset.mem_insert_of_mem hi))
    have hCI : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
        IsZero (relativeSingularHomology
          (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, C i))) q) := by
      intro T ht hts q hq
      have he : (⋂ i ∈ T, C i) = ⋂ i ∈ insert a T, U i := by
        ext x
        simp only [C, mem_iInter, mem_inter_iff, Finset.mem_insert]
        constructor
        · intro hx i hi
          rcases hi with rfl | hi
          · obtain ⟨j,hj⟩ := ht
            exact (hx j hj).1
          · exact (hx i hi).2
        · intro hx i hi
          exact ⟨hx a (Or.inl rfl),hx i (Or.inr hi)⟩
      rw [he]
      exact hinter (insert a T) (by simp) (Finset.insert_subset_insert a hts) q hq
    have heI : (⋃ i ∈ S, C i) = U a ∩ (⋃ i ∈ S, U i) := by
      ext x
      simp only [C, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨i,hi,hxa,hxi⟩; exact ⟨hxa,i,hi,hxi⟩
      · rintro ⟨hxa,i,hi,hxi⟩; exact ⟨i,hi,hxa,hxi⟩
    have hI := finiteRelativeOpenUnion_below_isZero S C A hCopen (n+1) hCI n (by omega)
    rw [heI] at hI
    have hcv : restrictedPairHomologyMap (inter_subset_left :
          U a ∩ (⋃ i ∈ S, U i) ⊆ U a) A (n+1) ≫ u a =
        restrictedPairHomologyMap (inter_subset_right :
          U a ∩ (⋃ i ∈ S, U i) ⊆ ⋃ i ∈ S, U i) A (n+1) ≫ v := by
      have hext := finiteRelativeOpenUnion_hom_ext S C A hCopen n hCI (Z := Z)
      rw [heI] at hext
      apply hext
      intro i hi h
      simp only [← Category.assoc, restrictedPairHomologyMap_comp]
      have hinc : U i ⊆ ⋃ j ∈ S, U j :=
        fun x hx => mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩
      rw [← restrictedPairHomologyMap_comp (inter_subset_right : U a ∩ U i ⊆ U i) hinc,
        Category.assoc, hv i hi hinc]
      exact hc a (by simp) i (Finset.mem_insert_of_mem hi)
    have heW : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by ext x; simp
    rw [heW]
    obtain ⟨f,hfa,hfv⟩ := relativeOpenUnion_exists_glue (U a) (⋃ i ∈ S, U i) A
      (hopen a (by simp))
      (isOpen_iUnion (fun i => isOpen_iUnion (fun hi => hopen i (Finset.mem_insert_of_mem hi))))
      n hI (u a) v hcv
    refine ⟨f,?_⟩
    intro i hi h
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hfa
    · have hinc : U i ⊆ ⋃ j ∈ S, U j :=
        fun x hx => mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩
      rw [← restrictedPairHomologyMap_comp hinc subset_union_right, Category.assoc, hfv]
      exact hv i hi hinc

/-- A finite open cover now gives a genuine map on the whole pair. -/
theorem finiteRelativeOpenCover_exists_glue (S : Finset J) (U : J → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i))
    (hcover : (⋃ i ∈ S, U i) = univ) (n : ℕ)
    (hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (u : ∀ i, relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set (U i))) (n+1) ⟶ Z)
    (hc : ∀ i ∈ S, ∀ j ∈ S,
      restrictedPairHomologyMap (inter_subset_left : U i ∩ U j ⊆ U i) A (n+1) ≫ u i =
      restrictedPairHomologyMap (inter_subset_right : U i ∩ U j ⊆ U j) A (n+1) ≫ u j) :
    ∃ f : relativeSingularHomology (subspaceInclusion A) (n+1) ⟶ Z,
      ∀ i ∈ S, restrictedPairToAmbientHomologyMap (U i) A (n+1) ≫ f = u i := by
  obtain ⟨v,hv⟩ := finiteRelativeOpenUnion_exists_glue S U A hopen n hinter u hc
  have : IsIso (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1)) := by
    rw [hcover]
    exact restrictedPairToAmbient_univ_isIso A (n+1)
  refine ⟨inv (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1)) ≫ v, ?_⟩
  intro i hi
  have hinc : U i ⊆ ⋃ j ∈ S, U j :=
    fun x hx => mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩
  rw [← restrictedPairHomologyMap_toAmbient hinc, Category.assoc,
    IsIso.hom_inv_id_assoc]
  exact hv i hi hinc

end

end Kaplansky

end

end OAI
