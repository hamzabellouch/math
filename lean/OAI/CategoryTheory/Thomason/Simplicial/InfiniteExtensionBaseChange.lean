import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionImageLattice
import OAI.CategoryTheory.Thomason.Simplicial.FiniteSingularRelativeLifting
import OAI.CategoryTheory.Thomason.Simplicial.InfiniteExtensionKan
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionUnions
import OAI.CategoryTheory.Thomason.Simplicial.TopologicalDeformationTransport
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
import Mathlib.Order.Preorder.Finite

namespace OAI

section

/-! # Exact Kan lifting with all extended faces prescribed

Inside the extension of a subdivided simplex, take the union of its
original image and the extensions of any finite collection of faces.
Its inclusion is anodyne. This statement concerns the actual union of
extended faces, and does not identify it with extension of the boundary.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

theorem canonicalExtension_isIso_of_initial {X : SSet.{0}} (hX : IsInitial X) :
    IsIso (canonicalExtension.app X) := by
  let f : X ⟶ (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X
  have : Mono f := hX.mono_from f
  have := canonicalExtension_isIso_of_terminal SSet.stdSimplex.isTerminalObj₀
  exact (canonicalExtension_isPullback f).isIso_snd_of_isIso

theorem canonicalExtension_subdividedFace_anodyne {n : ℕ} (S : Finset (Fin (n+1))) :
    SSet.anodyneExtensions (canonicalExtension.app (subdividedFace S).toSSet) := by
  classical
  have hsd : SSet.anodyneExtensions
      (canonicalExtension.app (SSet.sd.obj (SSet.stdSimplex.face S : SSet.{0}))) := by
    rcases S.eq_empty_or_nonempty with rfl | hs
    · have hi : IsInitial (SSet.stdSimplex.face (∅ : Finset (Fin (n+1))) : SSet.{0}) := by
        simpa only [SSet.stdSimplex.face_empty] using
          (SSet.Subcomplex.isInitialBot (X := (Δ[n] : SSet.{0})))
      have := canonicalExtension_isIso_of_initial (IsInitial.isInitialObj SSet.sd _ hi)
      exact SSet.anodyneExtensions.of_isIso _
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hs)
      let e := SSet.stdSimplex.isoOfRepresentableBy
        (SSet.stdSimplex.faceRepresentableBy S m (monoEquivOfFin S (by simpa using hm)))
      exact canonicalExtension_anodyne_of_iso (SSet.sd.mapIso e).symm
        (canonicalExtension_subdivision_standard_anodyne m)
  have := subdividedFaceMap_mono S
  let e : SSet.sd.obj (SSet.stdSimplex.face S : SSet.{0}) ≅ (subdividedFace S).toSSet :=
    asIso (SSet.Subcomplex.toRange (subdividedFaceMap S)) ≪≫
      SSet.Subcomplex.eqToIso (subdividedFaceMap_range S)
  exact canonicalExtension_anodyne_of_iso e.symm hsd

def extendedSubdividedFace {n : ℕ} (S : Finset (Fin (n+1))) :
    (SSet.ex.obj (SimplexCategory.sd.obj ⦋n⦌)).Subcomplex :=
  extensionImage (subdividedFace S)

theorem extendedSubdividedFace_inter {n : ℕ} (S T : Finset (Fin (n+1))) :
    extendedSubdividedFace S ⊓ extendedSubdividedFace T =
      extendedSubdividedFace (S ∩ T) := by
  change extensionImage (subdividedFace S) ⊓ extensionImage (subdividedFace T) = _
  rw [← extensionImage_inf, subdividedFace_inter]
  rfl

def extendedFaceUnion {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    (SSet.ex.obj (SimplexCategory.sd.obj ⦋n⦌)).Subcomplex :=
  originalImage (SimplexCategory.sd.obj ⦋n⦌) ⊔ F.sup extendedSubdividedFace

theorem original_to_extendedFaceUnion_anodyne {n : ℕ}
    (F : Finset (Finset (Fin (n+1)))) :
    SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
      (show originalImage (SimplexCategory.sd.obj ⦋n⦌) ≤ extendedFaceUnion F from le_sup_left)) := by
  classical
  let C := Set.range (extendedSubdividedFace (n := n))
  have hC : ∀ A ∈ C, ∀ B ∈ C, A ⊓ B ∈ C := by
    rintro A ⟨S, rfl⟩ B ⟨T, rfl⟩
    exact ⟨S ∩ T, (extendedSubdividedFace_inter S T).symm⟩
  have hJ : ∀ A ∈ C, SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
      (show originalImage (SimplexCategory.sd.obj ⦋n⦌) ⊓ A ≤ A from inf_le_right)) := by
    rintro A ⟨S, rfl⟩
    exact originalImage_inter_extensionImage_anodyne (subdividedFace S)
      (canonicalExtension_subdividedFace_anodyne S)
  have h := finite_anodyne_union (F.image extendedSubdividedFace) C
    (originalImage (SimplexCategory.sd.obj ⦋n⦌)) hC hJ (by
      intro A hA
      obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hA
      exact ⟨S, rfl⟩)
  have he : originalImage (SimplexCategory.sd.obj ⦋n⦌) ⊔
      (F.image extendedSubdividedFace).sup id = extendedFaceUnion F := by
    rw [Finset.sup_image]
    rfl
  exact (anodyne_subcomplex_congr rfl he _ _).mp h

/-- The finite union comparison has the left lifting property against
every Kan fibration, preserving all extended faces and the original
subdivided simplex exactly. -/
theorem extendedFaceUnion_anodyne {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    SSet.anodyneExtensions (extendedFaceUnion F).ι := by
  let X : SSet.{0} := SimplexCategory.sd.obj ⦋n⦌
  have hj : SSet.anodyneExtensions (canonicalExtension.app X) :=
    canonicalExtension_anodyne_of_iso (SSet.stdSimplex.sdIso.app ⦋n⦌).symm
      (canonicalExtension_subdivision_standard_anodyne n)
  have := canonicalExtension_mono X
  have hJ : SSet.anodyneExtensions (originalImage X).ι := by
    apply (SSet.anodyneExtensions.cancel_left_of_respectsIso
      (SSet.Subcomplex.toRange (canonicalExtension.app X)) (originalImage X).ι).mp
    simpa only [originalImage, SSet.Subcomplex.toRange_ι] using hj
  apply anodyne_right_cancellation (SSet.Subcomplex.homOfLE
    (show originalImage X ≤ extendedFaceUnion F from le_sup_left))
    (extendedFaceUnion F).ι (original_to_extendedFaceUnion_anodyne F)
  exact hJ

end

end Thomason.Construction

end

section

/-! # Extension preserves covers of poset nerves by sieves

An extension simplex is a map from a subdivided simplex.  The face poset
has a greatest vertex, so its image in a poset lies in every sieve that
contains the image of that vertex.  This gives an actual subcomplex cover,
not a weak-equivalence comparison.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits PartialOrder
open scoped Simplicial

noncomputable section

def fullSubposetComplexIso {P : Type} [PartialOrder P] (A : Set P) :
    nerve A ≅ (fullSubposetComplex A).toSSet :=
  asIso (SSet.Subcomplex.toRange (nerveMap (fullSubposetInclusion A))) ≪≫
    SSet.Subcomplex.eqToIso (fullSubposetComplex_eq_range A).symm

/-- A map from a nerve with a greatest vertex factors through one of any
two covering sieves. -/
theorem nerve_map_factors_of_sieve_cover {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (v : Q) (hv : ∀ q, q ≤ v) (A B : Set P)
    (hA : IsLowerSet A) (hB : IsLowerSet B) (hcover : ∀ p, p ∈ A ∨ p ∈ B)
    (f : nerve Q ⟶ nerve P) :
    (∃ g : nerve Q ⟶ (fullSubposetComplex A).toSSet,
      g ≫ (fullSubposetComplex A).ι = f) ∨
    (∃ g : nerve Q ⟶ (fullSubposetComplex B).toSSet,
      g ≫ (fullSubposetComplex B).ι = f) := by
  let F : Q ⥤ P :=
    (nerveFunctor.preimage (X := Cat.of Q) (Y := Cat.of P) f).toFunctor
  have hF : nerveMap F = f :=
    nerveFunctor.map_preimage (X := Cat.of Q) (Y := Cat.of P) f
  have hfactor (C : Set P) (hC : IsLowerSet C) (hc : F.obj v ∈ C) :
      ∃ g : nerve Q ⟶ (fullSubposetComplex C).toSSet,
        g ≫ (fullSubposetComplex C).ι = f := by
    have hf : SSet.Subcomplex.range f ≤ fullSubposetComplex C := by
      intro d s hs
      obtain ⟨t, rfl⟩ := hs
      rw [← hF]
      intro i
      exact hC (leOfHom (F.map (homOfLE (hv (t.obj i))))) hc
    exact ⟨SSet.Subcomplex.lift f hf, SSet.Subcomplex.lift_ι f hf⟩
  exact (hcover (F.obj v)).imp (hfactor A hA) (hfactor B hB)

/-- Every extension simplex of a poset nerve lies in the extension of
one of two covering full sieves. -/
theorem extension_sieve_simplex_cover {P : Type} [PartialOrder P]
    (A B : Set P) (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hcover : ∀ p, p ∈ A ∨ p ∈ B) (d : SimplexCategoryᵒᵖ)
    (s : (SSet.ex.obj (nerve P)).obj d) :
    s ∈ (extensionImage (fullSubposetComplex A)).obj d ∨
      s ∈ (extensionImage (fullSubposetComplex B)).obj d := by
  let a := (SSet.sdExAdjunction.homEquiv (SSet.stdSimplex.obj d.unop) (nerve P)).symm
    (SSet.yonedaEquiv.symm s)
  let e := subdivisionFaceIso d.unop
  have h := nerve_map_factors_of_sieve_cover (simplexTopFace d.unop.len)
    (fun _ => Finset.subset_univ _) A B hA hB hcover (e.inv ≫ a)
  have hmem (C : Set P)
      (g : nerve (NonemptyFiniteChains (ULift.{0} (Fin (d.unop.len+1)))) ⟶
        (fullSubposetComplex C).toSSet)
      (hg : g ≫ (fullSubposetComplex C).ι = e.inv ≫ a) :
      s ∈ (extensionImage (fullSubposetComplex C)).obj d := by
    let b := e.hom ≫ g
    have hb : b ≫ (fullSubposetComplex C).ι = a := by
      rw [Category.assoc, hg, e.hom_inv_id_assoc]
    have he : SSet.sdExAdjunction.homEquiv _ _ b ≫
        SSet.ex.map (fullSubposetComplex C).ι = SSet.yonedaEquiv.symm s := by
      rw [← SSet.sdExAdjunction.homEquiv_naturality_right, hb]
      exact (SSet.sdExAdjunction.homEquiv _ _).apply_symm_apply _
    refine ⟨SSet.yonedaEquiv (SSet.sdExAdjunction.homEquiv _ _ b), ?_⟩
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv he
  exact h.imp (fun ⟨g, hg⟩ => hmem A g hg) (fun ⟨g, hg⟩ => hmem B g hg)

theorem extension_sieve_cover {P : Type} [PartialOrder P]
    (A B : Set P) (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hcover : ∀ p, p ∈ A ∨ p ∈ B) :
    extensionImage (fullSubposetComplex A) ⊔
      extensionImage (fullSubposetComplex B) = ⊤ := by
  apply top_unique
  intro d s _
  exact extension_sieve_simplex_cover A B hA hB hcover d s

end

end Thomason.Construction

end

section

/-! # Exact extension lifting for finite poset nerves

Remove a maximal element and cover the poset by its complement and its
principal ideal.  The latter has a greatest vertex; the overlap is smaller.
Extension preserves this sieve cover, so cartesian extension squares and
finite anodyne gluing complete the induction.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- Binary gluing for canonical extensions, provided the actual extended
subobjects cover the extended target. -/
theorem canonicalExtension_anodyne_of_extended_cover {X : SSet.{0}}
    (A B : X.Subcomplex)
    (hcover : extensionImage A ⊔ extensionImage B = ⊤)
    (hA : SSet.anodyneExtensions (canonicalExtension.app A.toSSet))
    (hB : SSet.anodyneExtensions (canonicalExtension.app B.toSSet))
    (hAB : SSet.anodyneExtensions (canonicalExtension.app (A ⊓ B).toSSet)) :
    SSet.anodyneExtensions (canonicalExtension.app X) := by
  classical
  let EA := extensionImage A
  let EB := extensionImage B
  let J := originalImage X
  let C : Set (SSet.ex.obj X).Subcomplex := {EA, EB, EA ⊓ EB}
  have hC : ∀ D ∈ C, ∀ E ∈ C, D ⊓ E ∈ C := by
    intro D hD E hE
    simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hD hE ⊢
    rcases hD with rfl | rfl | rfl <;> rcases hE with rfl | rfl | rfl <;>
      simp [inf_comm]
  have hJ : ∀ D ∈ C, SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
      (show J ⊓ D ≤ D from inf_le_right)) := by
    intro D hD
    simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl | rfl
    · exact originalImage_inter_extensionImage_anodyne A hA
    · exact originalImage_inter_extensionImage_anodyne B hB
    · have h := originalImage_inter_extensionImage_anodyne (A ⊓ B) hAB
      have he : extensionImage (A ⊓ B) = EA ⊓ EB := extensionImage_inf A B
      exact (anodyne_subcomplex_congr (congrArg (J ⊓ ·) he) he _ _).mp h
  have h := finite_anodyne_union ({EA, EB} : Finset _) C J hC hJ (by
    intro D hD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl))
  have he : J ⊔ ({EA, EB} : Finset _).sup id = ⊤ := by
    simp only [Finset.sup_insert, Finset.sup_singleton, id_eq]
    change J ⊔ (extensionImage A ⊔ extensionImage B) = ⊤
    rw [hcover, sup_top_eq]
  have ht := (anodyne_subcomplex_congr rfl he _ le_top).mp h
  have hi : SSet.anodyneExtensions (originalImage X).ι := by
    simpa only [SSet.Subcomplex.topIso_hom, SSet.Subcomplex.homOfLE_ι] using
      SSet.anodyneExtensions.comp_mem _ _ ht
        (SSet.anodyneExtensions.of_isIso (SSet.Subcomplex.topIso (SSet.ex.obj X)).hom)
  have := canonicalExtension_mono X
  simpa only [originalImage, SSet.Subcomplex.toRange_ι] using
    SSet.anodyneExtensions.comp_mem _ _
      (SSet.anodyneExtensions.of_isIso
        (SSet.Subcomplex.toRange (canonicalExtension.app X))) hi

theorem canonicalExtension_anodyne_of_sieve_cover {P : Type} [PartialOrder P]
    (A B : Set P) (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hcover : ∀ p, p ∈ A ∨ p ∈ B)
    (hjA : SSet.anodyneExtensions (canonicalExtension.app (nerve A)))
    (hjB : SSet.anodyneExtensions (canonicalExtension.app (nerve B)))
    (hjAB : SSet.anodyneExtensions (canonicalExtension.app (nerve ↥(A ∩ B)))) :
    SSet.anodyneExtensions (canonicalExtension.app (nerve P)) := by
  apply canonicalExtension_anodyne_of_extended_cover
    (fullSubposetComplex A) (fullSubposetComplex B)
    (extension_sieve_cover A B hA hB hcover)
  · exact canonicalExtension_anodyne_of_iso (fullSubposetComplexIso A).symm hjA
  · exact canonicalExtension_anodyne_of_iso (fullSubposetComplexIso B).symm hjB
  · have h := canonicalExtension_anodyne_of_iso (fullSubposetComplexIso (A ∩ B)).symm hjAB
    exact canonicalExtension_anodyne_of_iso
      (SSet.Subcomplex.eqToIso (fullSubposetComplex_inter A B)).symm h

private theorem canonicalExtension_finitePoset_aux (n : ℕ) :
    ∀ (P : Type) [PartialOrder P] [Fintype P], Fintype.card P = n →
      SSet.anodyneExtensions (canonicalExtension.app (nerve P)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P _ _ hcard
    rcases isEmpty_or_nonempty P with hP | hP
    · have hi : IsInitial (nerve P) := SSet.isInitialOfNotNonempty (by
        rintro ⟨s⟩
        exact isEmptyElim (s.obj 0))
      have := canonicalExtension_isIso_of_initial hi
      exact SSet.anodyneExtensions.of_isIso _
    · obtain ⟨m, hm⟩ := (Finset.univ : Finset P).exists_maximal
        (Finset.univ_nonempty : (Finset.univ : Finset P).Nonempty)
      let A : Set P := {p | p ≠ m}
      let B : Set P := Set.Iic m
      have hA : IsLowerSet A := by
        intro y x hxy hy hx
        change y ≠ m at hy
        change x = m at hx
        subst x
        exact hy (le_antisymm (hm.2 (Finset.mem_univ y) hxy) hxy)
      have hB : IsLowerSet B := fun _ _ hxy hy => hxy.trans hy
      have hc : ∀ p, p ∈ A ∨ p ∈ B := by
        intro p
        by_cases hp : p = m
        · exact Or.inr (hp ▸ le_rfl)
        · exact Or.inl hp
      have hsmallA : Fintype.card A < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (x := m) (by simp [A])
      have hsmallAB : Fintype.card ↥(A ∩ B) < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (x := m) (by simp [A])
      apply canonicalExtension_anodyne_of_sieve_cover A B hA hB hc
      · exact ih (Fintype.card A) hsmallA A rfl
      · exact canonicalExtension_anodyne_nerve_greatest (⟨m, le_rfl⟩ : B)
          (fun p => p.property)
      · exact ih (Fintype.card ↥(A ∩ B)) hsmallAB ↥(A ∩ B) rfl

/-- The canonical extension of the nerve of any finite poset is anodyne.
No contractibility of the poset is required. -/
theorem canonicalExtension_finitePoset_anodyne (P : Type) [PartialOrder P] [Finite P] :
    SSet.anodyneExtensions (canonicalExtension.app (nerve P)) := by
  let := Fintype.ofFinite P
  exact canonicalExtension_finitePoset_aux (Fintype.card P) P rfl

end

end Thomason.Construction

end

section

/-! # Exact extension lifting on subdivided finite face unions

The union of any finite family of subdivided faces is the full nerve of
the finite poset of faces supported in that family.  Thus its canonical
extension is anodyne, including the full subdivided boundary.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder
open scoped Simplicial

noncomputable section

def faceFamilyVertices {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    Set (NonemptyFiniteChains (ULift.{0} (Fin (n+1)))) :=
  {q | ∃ S ∈ F, ∀ x ∈ q.finset, x.down ∈ S}

theorem subdividedFaceUnion_eq_full {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    subdividedFaceUnion F = fullSubposetComplex (faceFamilyVertices F) := by
  classical
  ext d s
  have hs : s ∈ (subdividedFaceUnion F).obj d ↔
      ∃ S ∈ F, ∀ i, ∀ x ∈ (s.obj i).finset, x.down ∈ S := by
    simp only [subdividedFaceUnion, Finset.sup_eq_iSup, Subfunctor.iSup_obj,
      Set.mem_iUnion]
    simp [subdividedFace, fullSubposetComplex, chainsSupported]
    rfl
  rw [hs]
  constructor
  · rintro ⟨S, hS, h⟩ i
    exact ⟨S, hS, h i⟩
  · intro h
    obtain ⟨S, hS, htop⟩ := h (Fin.last d.unop.len)
    refine ⟨S, hS, fun i x hx => ?_⟩
    exact htop x (leOfHom (s.map (homOfLE (Fin.le_last i))) hx)

def faceUnionSubdivisionIso {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    SSet.sd.obj (faceUnion F).toSSet ≅ nerve (faceFamilyVertices F) := by
  have := (finiteFaceUnion_mono_range F).1
  exact asIso (SSet.Subcomplex.toRange (subdivisionInclusion (faceUnion F))) ≪≫
    SSet.Subcomplex.eqToIso (finiteFaceUnion_mono_range F).2 ≪≫
    SSet.Subcomplex.eqToIso (subdividedFaceUnion_eq_full F) ≪≫
    (fullSubposetComplexIso (faceFamilyVertices F)).symm

theorem canonicalExtension_subdivision_faceUnion_anodyne {n : ℕ}
    (F : Finset (Finset (Fin (n+1)))) :
    SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj (faceUnion F).toSSet)) := by
  have := finite_nonemptyFiniteChains (ULift.{0} (Fin (n+1)))
  exact canonicalExtension_anodyne_of_iso (faceUnionSubdivisionIso F)
    (canonicalExtension_finitePoset_anodyne (faceFamilyVertices F))

def subcomplexFaceFamily {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    Finset (Finset (Fin (n+1))) := by
  classical
  exact Finset.univ.filter (fun S => SSet.stdSimplex.face S ≤ A)

theorem faceUnion_subcomplexFaceFamily {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    faceUnion (subcomplexFaceFamily A) = A := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  · apply (SSet.Subcomplex.le_iff_contains_nonDegenerate _ _).mpr
    intro m x hx
    let S := (SSet.stdSimplex.nonDegenerateEquiv' x).val
    have he : SSet.stdSimplex.face S = SSet.Subcomplex.ofSimplex x.val :=
      SSet.stdSimplex.face_nonDegenerateEquiv' x
    have hS : S ∈ subcomplexFaceFamily A := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [he]
      exact (SSet.Subcomplex.ofSimplex_le_iff _ _).mpr hx
    have hle : SSet.stdSimplex.face S ≤ faceUnion (subcomplexFaceFamily A) :=
      Finset.le_sup hS
    apply hle _
    rw [he]
    exact SSet.Subcomplex.mem_ofSimplex_obj x.val

theorem canonicalExtension_subdivision_subcomplex_anodyne {n : ℕ}
    (A : (Δ[n] : SSet.{0}).Subcomplex) :
    SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj A.toSSet)) := by
  rw [← faceUnion_subcomplexFaceFamily A]
  exact canonicalExtension_subdivision_faceUnion_anodyne _

/-- The entire subdivided boundary has an anodyne canonical extension;
this includes extensions whose simplices span several original faces. -/
theorem canonicalExtension_subdivision_boundary_anodyne (n : ℕ) :
    SSet.anodyneExtensions
      (canonicalExtension.app (SSet.sd.obj (SSet.boundary.{0} n).toSSet)) :=
  canonicalExtension_subdivision_subcomplex_anodyne _

/-- Exact relative lifting with the whole extended subdivided boundary
and the original subdivided simplex prescribed. -/
theorem relativeCanonicalExtension_subdivision_boundary_anodyne (n : ℕ) :
    SSet.anodyneExtensions
      (relativeCanonicalExtension (SSet.sd.map (SSet.boundary.{0} n).ι)) := by
  have := subdivision_map_mono (SSet.boundary.{0} n).ι
  exact relativeCanonicalExtension_anodyne _
    (canonicalExtension_subdivision_boundary_anodyne n)
    (canonicalExtension_subdivision_standard_anodyne n)

end

end Thomason.Construction

end

section

/-! # Barycentric subdivision on finite simplex subcomplexes

Every subcomplex of a standard simplex is its finite union of faces.
The actual subdivision and the coordinate face union are homeomorphic,
including all lower-dimensional intersections.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity RealizationPrism Topology
open scoped Simplicial

noncomputable section

def faceUnionCoordinates {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    C(SSet.toTop.obj (faceUnion F).toSSet, StdSimplex ℝ (Fin (n+1))) :=
  ((SimplexCategory.mk n).toTopHomeo : C(_, _)).comp
    (SSet.toTop.map (faceUnion F).ι).hom

theorem faceUnionCoordinates_isClosedEmbedding {n : ℕ}
    (F : Finset (Finset (Fin (n+1)))) : IsClosedEmbedding (faceUnionCoordinates F) :=
  (SimplexCategory.mk n).toTopHomeo.isClosedEmbedding.comp
    (inclusion_isClosedEmbedding _ _)

theorem faceUnionCoordinates_range {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    Set.range (faceUnionCoordinates F) =
      {p | ∃ S ∈ F, ∀ i ∉ S, p.weights i = 0} := by
  ext p
  change p ∈ Set.range (faceUnionCoordinates F) ↔ ∃ S ∈ F, ∀ i ∉ S, p.weights i = 0
  rw [← standard_faceUnion_point_iff F p]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, (SimplexCategory.mk n).toTopHomeo.injective ?_⟩
    exact hz.trans ((SimplexCategory.mk n).toTopHomeo.apply_symm_apply p).symm
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change (SimplexCategory.mk n).toTopHomeo
      ((SSet.toTop.map (faceUnion F).ι).hom z) = p
    rw [hz, Homeomorph.apply_symm_apply]

def faceUnionCoordinatesHomeomorph {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    SSet.toTop.obj (faceUnion F).toSSet ≃ₜ
      {p : StdSimplex ℝ (Fin (n+1)) // ∃ S ∈ F, ∀ i ∉ S, p.weights i = 0} :=
  (faceUnionCoordinates_isClosedEmbedding F).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (faceUnionCoordinates_range F))

def faceUnionSubdivisionRangeIso {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    SSet.sd.obj (faceUnion F).toSSet ≅ (subdividedFaceUnion F).toSSet := by
  have := (finiteFaceUnion_mono_range F).1
  exact asIso (SSet.Subcomplex.toRange (subdivisionInclusion (faceUnion F))) ≪≫
    SSet.Subcomplex.eqToIso (finiteFaceUnion_mono_range F).2

theorem faceUnionSubdivisionRangeIso_inclusion {n : ℕ}
    (F : Finset (Finset (Fin (n+1)))) :
    (faceUnionSubdivisionRangeIso F).hom ≫ (subdividedFaceUnion F).ι =
      subdivisionInclusion (faceUnion F) := by
  simp [faceUnionSubdivisionRangeIso]

def faceUnionSubdivisionHomeomorph {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    SSet.toTop.obj (SSet.sd.obj (faceUnion F).toSSet) ≃ₜ
      SSet.toTop.obj (faceUnion F).toSSet :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (faceUnionSubdivisionRangeIso F))).trans
    ((faceUnionHomeomorph F).trans (faceUnionCoordinatesHomeomorph F).symm)

/-- The actual realization of the subdivision of any simplex subcomplex
is homeomorphic to the original realization. -/
def subcomplexSubdivisionHomeomorph {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    SSet.toTop.obj (SSet.sd.obj A.toSSet) ≃ₜ SSet.toTop.obj A.toSSet :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso
    (SSet.sd.mapIso (SSet.Subcomplex.eqToIso (faceUnion_subcomplexFaceFamily A)).symm))).trans
      ((faceUnionSubdivisionHomeomorph (subcomplexFaceFamily A)).trans
        (TopCat.homeoOfIso (SSet.toTop.mapIso
          (SSet.Subcomplex.eqToIso (faceUnion_subcomplexFaceFamily A)))))

/-- The face-union homeomorphism is the restriction of the barycentric
simplex map along the original inclusion. -/
theorem faceUnionSubdivisionHomeomorph_inclusion {n : ℕ}
    (F : Finset (Finset (Fin (n+1))))
    (z : SSet.toTop.obj (SSet.sd.obj (faceUnion F).toSSet)) :
    (SSet.toTop.map (faceUnion F).ι).hom (faceUnionSubdivisionHomeomorph F z) =
      standardSubdivisionHomeomorph n
        ((SSet.toTop.map (SSet.sd.map (faceUnion F).ι)).hom z) := by
  apply (SimplexCategory.mk n).toTopHomeo.injective
  let w := (SSet.toTop.map (faceUnionSubdivisionRangeIso F).hom).hom z
  have hw : (SSet.toTop.map (subdividedFaceUnion F).ι).hom w =
      (SSet.toTop.map (subdivisionInclusion (faceUnion F))).hom z := by
    have hf : SSet.toTop.map (faceUnionSubdivisionRangeIso F).hom ≫
        SSet.toTop.map (subdividedFaceUnion F).ι =
        SSet.toTop.map (subdivisionInclusion (faceUnion F)) := by
      rw [← SSet.toTop.map_comp, faceUnionSubdivisionRangeIso_inclusion]
    exact ConcreteCategory.congr_hom hf z
  have hh : faceUnionCoordinates F (faceUnionSubdivisionHomeomorph F z) =
      point n ((SSet.toTop.map (subdividedFaceUnion F).ι).hom w) := by
    exact congrArg Subtype.val ((faceUnionCoordinatesHomeomorph F).apply_symm_apply
      (faceUnionHomeomorph F w))
  change faceUnionCoordinates F (faceUnionSubdivisionHomeomorph F z) = _
  rw [hh, hw]
  change _ = (SimplexCategory.mk n).toTopHomeo
    ((SimplexCategory.mk n).toTopHomeo.symm _)
  rw [Homeomorph.apply_symm_apply]
  exact congrArg (point n) (ConcreteCategory.congr_hom
    (SSet.toTop.map_comp (SSet.sd.map (faceUnion F).ι)
      (SSet.stdSimplex.sdIso.hom.app (.mk n))) z)

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Closed vertex stars inside an ordered simplex

The closed star is the union of all faces in a subcomplex that contain
the specified vertex.  If that vertex is greatest among the vertices of
the subcomplex, the usual ordered contraction stays in every such face.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

def closedVertexStar {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex)
    (v : Fin (n+1)) : (Δ[n] : SSet.{0}).Subcomplex where
  obj d := {x | ∃ S : Finset (Fin (n+1)), v ∈ S ∧
    SSet.stdSimplex.face S ≤ A ∧ x ∈ (SSet.stdSimplex.face S).obj d}
  map f := by
    rintro x ⟨S, hv, hS, hx⟩
    exact ⟨S, hv, hS, (SSet.stdSimplex.face S).map f hx⟩

theorem closedVertexStar_le {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex)
    (v : Fin (n+1)) : closedVertexStar A v ≤ A := by
  rintro d x ⟨S, _, hS, hx⟩
  exact hS _ hx

theorem face_le_closedVertexStar {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex)
    (v : Fin (n+1)) (S : Finset (Fin (n+1))) (hv : v ∈ S)
    (hS : SSet.stdSimplex.face S ≤ A) :
    SSet.stdSimplex.face S ≤ closedVertexStar A v := by
  intro d x hx
  exact ⟨S, hv, hS, hx⟩

def closedVertexStarVertex {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex)
    (v : Fin (n+1)) (h : ∃ S : Finset (Fin (n+1)),
      v ∈ S ∧ SSet.stdSimplex.face S ≤ A) :
    (closedVertexStar A v).toSSet _⦋0⦌ :=
  ⟨SSet.stdSimplex.obj₀Equiv.symm v, by
    obtain ⟨S, hv, hS⟩ := h
    exact ⟨S, hv, hS, (SSet.stdSimplex.mem_face_iff S _).mpr (fun _ => hv)⟩⟩

def closedVertexStarContraction {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex)
    (v : Fin (n+1)) (h : ∃ S : Finset (Fin (n+1)),
      v ∈ S ∧ SSet.stdSimplex.face S ≤ A)
    (hmax : ∀ (d : SimplexCategoryᵒᵖ) (x : A.toSSet.obj d)
      (i : Fin (d.unop.len+1)), (SSet.stdSimplex.objEquiv x.val).toOrderHom i ≤ v) :
    SSet.Homotopy (𝟙 (closedVertexStar A v).toSSet)
      (SSet.const (closedVertexStarVertex A v h)) where
  h := {
    app d := ↾fun x => ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
      (orderInterpolate (SSet.stdSimplex.objEquiv x.1.val).toOrderHom
        (OrderHom.const _ v)
        (fun i => hmax d ⟨x.1.val, closedVertexStar_le A v d x.1.property⟩ i)
        OrderHom.id (SSet.stdSimplex.objEquiv x.2).toOrderHom)), by
          obtain ⟨S, hv, hS, hx⟩ := x.1.property
          refine ⟨S, hv, hS, (SSet.stdSimplex.mem_face_iff S _).mpr ?_⟩
          intro i
          change (if (SSet.stdSimplex.objEquiv x.2).toOrderHom i = 0 then
            (SSet.stdSimplex.objEquiv x.1.val).toOrderHom i else v) ∈ S
          split_ifs
          · exact (SSet.stdSimplex.mem_face_iff S _).mp hx i
          · exact hv⟩
    naturality d e f := by
      apply ConcreteCategory.hom_ext
      intro x
      apply Subtype.ext
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro i
      rfl }
  h₀ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    rfl
  h₁ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    rfl
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

theorem canonicalExtension_closedVertexStar_anodyne {n : ℕ}
    (A : (Δ[n] : SSet.{0}).Subcomplex) (v : Fin (n+1))
    (hmax : ∀ (d : SimplexCategoryᵒᵖ) (x : A.toSSet.obj d)
      (i : Fin (d.unop.len+1)), (SSet.stdSimplex.objEquiv x.val).toOrderHom i ≤ v) :
    SSet.anodyneExtensions (canonicalExtension.app (closedVertexStar A v).toSSet) := by
  classical
  by_cases h : ∃ S : Finset (Fin (n+1)), v ∈ S ∧ SSet.stdSimplex.face S ≤ A
  · apply canonicalExtension_anodyne_of_contraction _
      (SSet.stdSimplex.isTerminalObj₀.from _)
      (SSet.const (closedVertexStarVertex A v h))
    simpa only [SSet.comp_const] using closedVertexStarContraction A v h hmax
  · have hi : IsInitial (closedVertexStar A v).toSSet :=
      SSet.isInitialOfNotNonempty (by
        rintro ⟨x⟩
        obtain ⟨S, hv, hS, _⟩ := x.property
        exact h ⟨S, hv, hS⟩)
    have := canonicalExtension_isIso_of_initial hi
    exact SSet.anodyneExtensions.of_isIso _

end

end Thomason.Construction

end

section

/-! # Every horn in an extension fills after the next extension -/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- The exact two-subdivision retraction gives a filler for every horn in
`Ex X` after the specified canonical map to `Ex (Ex X)`. -/
theorem extension_horn_filler (X : SSet.{0}) (n : ℕ) (k : Fin (n+2))
    (a : (SSet.horn.{0} (n+1) k : SSet) ⟶ SSet.ex.obj X) :
    ∃ b : (Δ[n+1] : SSet.{0}) ⟶ SSet.ex.obj (SSet.ex.obj X),
      (SSet.horn.{0} (n+1) k).ι ≫ b = a ≫ canonicalExtension.app (SSet.ex.obj X) := by
  let A := (SSet.horn.{0} (n+1) k : SSet)
  let B := (Δ[n+1] : SSet.{0})
  let i : A ⟶ B := (SSet.horn.{0} (n+1) k).ι
  let f := (SSet.sdExAdjunction.homEquiv A X).symm a
  let F := subdivisionHornRetraction n k ≫ f
  let g := SSet.sdExAdjunction.homEquiv (SSet.sd.obj B) X F
  let b := SSet.sdExAdjunction.homEquiv B (SSet.ex.obj X) g
  refine ⟨b, ?_⟩
  change i ≫ b = _
  have hf : SSet.sdExAdjunction.homEquiv A X f = a :=
    (SSet.sdExAdjunction.homEquiv A X).apply_symm_apply a
  have hi : SSet.sd.map (SSet.sd.map i) ≫ F = SSet.sd.map (lastVertex.app A) ≫ f := by
    dsimp [F]
    rw [← Category.assoc, subdivisionHornRetraction_fac]
  calc
    i ≫ b = SSet.sdExAdjunction.homEquiv A (SSet.ex.obj X) (SSet.sd.map i ≫ g) :=
      (SSet.sdExAdjunction.homEquiv_naturality_left i g).symm
    _ = SSet.sdExAdjunction.homEquiv A (SSet.ex.obj X)
        (SSet.sdExAdjunction.homEquiv (SSet.sd.obj A) X
          (SSet.sd.map (SSet.sd.map i) ≫ F)) :=
      congrArg (SSet.sdExAdjunction.homEquiv A (SSet.ex.obj X))
        (SSet.sdExAdjunction.homEquiv_naturality_left (SSet.sd.map i) F).symm
    _ = SSet.sdExAdjunction.homEquiv A (SSet.ex.obj X)
        (SSet.sdExAdjunction.homEquiv (SSet.sd.obj A) X
          (SSet.sd.map (lastVertex.app A) ≫ f)) :=
      congrArg (fun q => SSet.sdExAdjunction.homEquiv A (SSet.ex.obj X)
        (SSet.sdExAdjunction.homEquiv (SSet.sd.obj A) X q)) hi
    _ = SSet.sdExAdjunction.homEquiv A (SSet.ex.obj X) (lastVertex.app A ≫ a) := by
      rw [SSet.sdExAdjunction.homEquiv_naturality_left]
      exact congrArg (fun q => SSet.sdExAdjunction.homEquiv A (SSet.ex.obj X)
        (lastVertex.app A ≫ q)) hf
    _ = a ≫ canonicalExtension.app (SSet.ex.obj X) := canonicalExtension_adjunct a

/-- A horn in an arbitrary simplicial set fills after its two canonical
extension maps; no fibrancy of the starting simplicial set is required. -/
theorem extension_twice_horn_filler (X : SSet.{0}) (n : ℕ) (k : Fin (n+2))
    (a : (SSet.horn.{0} (n+1) k : SSet) ⟶ X) :
    ∃ b : (Δ[n+1] : SSet.{0}) ⟶ SSet.ex.obj (SSet.ex.obj X),
      (SSet.horn.{0} (n+1) k).ι ≫ b =
        a ≫ canonicalExtension.app X ≫ canonicalExtension.app (SSet.ex.obj X) :=
  by simpa only [Category.assoc] using
    extension_horn_filler X n k (a ≫ canonicalExtension.app X)

end

end Thomason.Construction

end

section

/-! # The actual extension colimit is always a Kan complex -/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- A finite horn lies in a stage and fills after two further extensions.
The colimit compatibility retains the prescribed horn exactly. -/
theorem horn_lifting (X : SSet.{0}) (n : ℕ) (k : Fin (n+2)) :
    HasLiftingProperty (SSet.horn (n+1) k).ι (terminal.from (obj X)) := by
  refine ⟨fun {a _} _ => ?_⟩
  obtain ⟨m, a₀, ha₀⟩ := finite_map_factors X a
  obtain ⟨b, hb⟩ := extension_twice_horn_filler (stage X m) n k a₀
  refine ⟨⟨{ l := b ≫ inclusion X (m+2), fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, hb]
    change (a₀ ≫ step X m ≫ step X (m+1)) ≫ inclusion X (m+2) = a
    rw [Category.assoc, Category.assoc, step_inclusion, step_inclusion, ha₀]
  · exact terminalIsTerminal.hom_ext _ _

/-- No fibrancy assumption is needed on the input. -/
instance kan (X : SSet.{0}) : SSet.KanComplex (obj X) := by
  apply (HomotopicalAlgebra.isFibrant_iff (obj X)).mpr
  apply (fibration_iff _).mpr
  intro A B i hi
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  exact horn_lifting _ n k

end

end Thomason.Construction.InfiniteExtension

end

section

/-! # Exact pullback compatibility of the constructed Kan replacement

These comparisons use the actual extension colimit and its canonical
coaugmentation. They preserve the specified projection maps.
-/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The original pullback maps weakly to the pullback of its constructed
Kan replacements, with no properness hypothesis. -/
def pullbackUnit {E B C : SSet.{0}} (p : E ⟶ B) (g : C ⟶ B) :
    pullback p g ⟶ pullback (map p) (map g) :=
  unit (pullback p g) ≫ pullbackComparison functor p g

@[reassoc] theorem pullbackUnit_fst {E B C : SSet.{0}} (p : E ⟶ B) (g : C ⟶ B) :
    pullbackUnit p g ≫ pullback.fst (map p) (map g) =
      pullback.fst p g ≫ unit E := by
  change (coaugmentation.app (pullback p g) ≫ pullbackComparison functor p g) ≫
    pullback.fst (functor.map p) (functor.map g) =
      pullback.fst p g ≫ coaugmentation.app E
  rw [Category.assoc, pullbackComparison_comp_fst]
  exact (coaugmentation.naturality (pullback.fst p g)).symm

@[reassoc] theorem pullbackUnit_snd {E B C : SSet.{0}} (p : E ⟶ B) (g : C ⟶ B) :
    pullbackUnit p g ≫ pullback.snd (map p) (map g) =
      pullback.snd p g ≫ unit C := by
  change (coaugmentation.app (pullback p g) ≫ pullbackComparison functor p g) ≫
    pullback.snd (functor.map p) (functor.map g) =
      pullback.snd p g ≫ coaugmentation.app C
  rw [Category.assoc, pullbackComparison_comp_snd]
  exact (coaugmentation.naturality (pullback.snd p g)).symm

theorem pullbackUnit_weak {E B C : SSet.{0}} (p : E ⟶ B) (g : C ⟶ B) :
    realizationWeakEquivalences (pullbackUnit p g) :=
  realizationWeakEquivalences.comp_mem _ _ (unit_weak _)
    (realizationWeakEquivalences.of_isIso (pullbackComparison functor p g))

/-- The exact base-change projection is weak if and only if the projection
between the actual Kan replacements is weak. This is a compatibility
statement, not an assumption of properness. -/
theorem pullback_fst_weak_iff {E B C : SSet.{0}} (p : E ⟶ B) (g : C ⟶ B) :
    realizationWeakEquivalences (pullback.fst p g) ↔
      realizationWeakEquivalences (pullback.fst (map p) (map g)) := by
  have hu := pullbackUnit_weak p g
  have he := unit_weak E
  constructor
  · intro h
    apply realizationWeakEquivalences.of_precomp (pullbackUnit p g) _ hu
    rw [pullbackUnit_fst]
    exact realizationWeakEquivalences.comp_mem _ _ h he
  · intro h
    apply realizationWeakEquivalences.of_postcomp _ (unit E) he
    rw [← pullbackUnit_fst]
    exact realizationWeakEquivalences.comp_mem _ _ hu h

/-- The second projection has the same exact compatibility. -/
theorem pullback_snd_weak_iff {E B C : SSet.{0}} (p : E ⟶ B) (g : C ⟶ B) :
    realizationWeakEquivalences (pullback.snd p g) ↔
      realizationWeakEquivalences (pullback.snd (map p) (map g)) := by
  have hu := pullbackUnit_weak p g
  have hc := unit_weak C
  constructor
  · intro h
    apply realizationWeakEquivalences.of_precomp (pullbackUnit p g) _ hu
    rw [pullbackUnit_snd]
    exact realizationWeakEquivalences.comp_mem _ _ h hc
  · intro h
    apply realizationWeakEquivalences.of_postcomp _ (unit C) hc
    rw [← pullbackUnit_snd]
    exact realizationWeakEquivalences.comp_mem _ _ hu h

end

end Thomason.Construction.InfiniteExtension

end

end OAI
