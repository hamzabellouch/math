import OAI.CategoryTheory.Thomason.Simplicial.BarycentricSortedCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.ConstructedExtensionLocalizer
import OAI.CategoryTheory.Thomason.Simplicial.ExhaustionWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.FiniteKanBaseChangeApproximation
import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.FiniteSingularRelativeLifting
import OAI.CategoryTheory.Thomason.Simplicial.LastVertexWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.RealizationSubcomplexSemantics
import OAI.CategoryTheory.Thomason.Strict.StreetWhitehead
import OAI.CategoryTheory.Thomason.Transfer.NonsingularFaceGluing
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

namespace OAI

section

/-! # A common flag for points with sorted barycentric coordinates

The positive faces of a point are prefixes of any ordering which sorts
its affine coordinates. Grouping their masses gives an exact flag
representative in the actual geometric realization.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity PartialOrder RealizationPrism

noncomputable section

theorem mem_permuted_prefix (n : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (k i : Fin (n+1)) :
    ULift.up (σ i) ∈ (permutationFaceMap n σ (prefixFace n k)).finset ↔ i ≤ k := by
  classical
  have hf : (permutationFaceMap n σ (prefixFace n k)).finset =
      (prefixFace n k).finset.image (fun a => ULift.up (σ a.down)) := by
    change ((prefixFace n k).finset.image (fun a => ULift.up (σ a.down))) = _
    congr
  rw [hf, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    have ha' : a = ULift.up i :=
      ULift.ext _ _ (σ.injective (congrArg ULift.down he))
    subst a
    simpa [prefixFace] using ha
  · intro hi
    exact ⟨ULift.up i, by simpa [prefixFace] using hi, rfl⟩

theorem positive_face_mem_permuted_prefix (n : ℕ)
    (z : SSet.toTop.obj (nerve (Faces n))) (A : Faces n)
    (hA : 0 < (PosetGeometry.coordinates (Faces n) z).weights A)
    (σ : Equiv.Perm (Fin (n+1)))
    (hσ : Antitone (fun i => (point n z).weights (σ i))) :
    ∃ k : Fin (n+1), permutationFaceMap n σ (prefixFace n k) = A := by
  obtain ⟨k, hk⟩ := positive_face_sorted_prefix n z A hA σ hσ
  refine ⟨k, ?_⟩
  apply NonemptyFiniteChains.ext
  ext a
  have ha : ULift.up (σ (σ.symm a.down)) = a := by simp
  rw [← ha, mem_permuted_prefix, hk]

/-- Sorting the affine image determines one common flag which contains
the original realization point, even on all intersections of chambers. -/
theorem exists_permuted_prefix_representation (n : ℕ)
    (z : SSet.toTop.obj (nerve (Faces n)))
    (σ : Equiv.Perm (Fin (n+1)))
    (hσ : Antitone (fun i => (point n z).weights (σ i))) :
    ∃ p : StdSimplex ℝ (Fin (n+1)), z =
      simplexPoint (nerve (Faces n))
        (prefixSimplex n ⋙ (permutationFaceMap n σ).monotone.functor) p := by
  classical
  let q := PosetGeometry.coordinates (Faces n) z
  let g : Fin (n+1) → Faces n := fun k => permutationFaceMap n σ (prefixFace n k)
  have hg (A : Faces n) (hA : q.weights A ≠ 0) : ∃ k, g k = A :=
    positive_face_mem_permuted_prefix n z A
      (lt_of_le_of_ne (q.nonneg A) (Ne.symm hA)) σ hσ
  let f : Faces n → Fin (n+1) := fun A =>
    if hA : q.weights A ≠ 0 then (hg A hA).choose else 0
  let p := StdSimplex.map f q
  have hp : StdSimplex.map g p = q := by
    apply StdSimplex.ext
    change (q.weights.mapDomain f).mapDomain g = q.weights
    rw [← Finsupp.mapDomain_comp]
    have he : q.weights.mapDomain (g ∘ f) = q.weights.mapDomain id := by
      apply Finsupp.mapDomain_congr
      intro A hA
      have hne := Finsupp.mem_support_iff.mp hA
      change g (if h : q.weights A ≠ 0 then (hg A h).choose else 0) = A
      rw [dite_eq_left hne]
      exact (hg A hne).choose_spec
    exact he.trans Finsupp.mapDomain_id
  refine ⟨p, PosetGeometry.coordinates_injective (Faces n) ?_⟩
  exact hp.symm.trans (PosetGeometry.coordinates_simplexPoint (Faces n)
    (prefixSimplex n ⋙ (permutationFaceMap n σ).monotone.functor) p).symm

/-- The barycentric affine map distinguishes points of the actual
face-nerve realization. -/
theorem point_injective (n : ℕ) : Function.Injective (point n) := by
  intro z w hzw
  obtain ⟨σ, hσ⟩ := exists_antitone_permutation n (point n z).weights
  obtain ⟨p, rfl⟩ := exists_permuted_prefix_representation n z σ hσ
  have hw : Antitone (fun i => (point n w).weights (σ i)) := by
    simpa only [hzw] using hσ
  obtain ⟨q, rfl⟩ := exists_permuted_prefix_representation n w σ hw
  exact congrArg _ (permuted_prefix_point_injective n σ hzw)

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # The actual barycentric subdivision homeomorphism

Exact flag reconstruction and uniqueness identify the realization of
the nonempty-face nerve with the whole standard simplex. The map and
its inverse retain complete faces.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity PartialOrder RealizationPrism

noncomputable section

/-- The affine barycentric map, as a homeomorphism of actual spaces. -/
def homeomorph (n : ℕ) :
    SSet.toTop.obj (nerve (Faces n)) ≃ₜ StdSimplex ℝ (Fin (n+1)) := by
  let : (nerve (Faces n)).Finite := PosetGeometry.nerve_finite (Faces n)
  let : CompactSpace (SSet.toTop.obj (nerve (Faces n))) := compactSpace_of_finite _
  let : T2Space (StdSimplex ℝ (Fin (n+1))) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).t2Space
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (point n) ⟨point_injective n, point_surjective n⟩)
    (map n).continuous

theorem homeomorph_apply (n : ℕ) (z : SSet.toTop.obj (nerve (Faces n))) :
    homeomorph n z = point n z := rfl

theorem homeomorph_face_naturality {m n : ℕ} (f : Fin (m+1) ↪o Fin (n+1))
    (z : SSet.toTop.obj (nerve (Faces m))) :
    homeomorph n ((SSet.toTop.map (nerveMap (faceMap f).monotone.functor)).hom z) =
      StdSimplex.map f (homeomorph m z) := point_face_naturality f z

/-- The inverse also commutes with every injective ordinal face map. -/
theorem homeomorph_symm_face_naturality {m n : ℕ} (f : Fin (m+1) ↪o Fin (n+1))
    (p : StdSimplex ℝ (Fin (m+1))) :
    (homeomorph n).symm (StdSimplex.map f p) =
      (SSet.toTop.map (nerveMap (faceMap f).monotone.functor)).hom
        ((homeomorph m).symm p) := by
  apply (homeomorph n).injective
  rw [Homeomorph.apply_symm_apply, homeomorph_face_naturality,
    Homeomorph.apply_symm_apply]

/-- A complete coordinate face has precisely its expected subdivided
face as inverse image, including every intersection of faces. -/
theorem homeomorph_symm_face_carrier (n : ℕ) (V : Set (Fin (n+1)))
    (p : StdSimplex ℝ (Fin (n+1))) :
    carrier (nerve (Faces n)) ((homeomorph n).symm p) ≤
      fullSubposetComplex (permittedFaces n V) ↔ ∀ i ∉ V, p.weights i = 0 := by
  rw [← point_face_preimage]
  change (∀ i ∉ V, (homeomorph n ((homeomorph n).symm p)).weights i = 0) ↔ _
  rw [Homeomorph.apply_symm_apply]

/-- The restriction identifies the actual subdivided face realization
with its full coordinate face, not merely their interiors. -/
def faceHomeomorph (n : ℕ) (V : Set (Fin (n+1))) :
    SSet.toTop.obj (fullSubposetComplex (permittedFaces n V)).toSSet ≃ₜ
      {p : StdSimplex ℝ (Fin (n+1)) // ∀ i ∉ V, p.weights i = 0} :=
  (carrierHomeomorph (nerve (Faces n)) (fullSubposetComplex (permittedFaces n V))).trans
    ((homeomorph n).subtype (fun z => (point_face_preimage n V z).symm))

theorem faceHomeomorph_inclusion (n : ℕ) (V : Set (Fin (n+1)))
    (z : SSet.toTop.obj (fullSubposetComplex (permittedFaces n V)).toSSet) :
    (faceHomeomorph n V z).val = point n
      ((SSet.toTop.map (fullSubposetComplex (permittedFaces n V)).ι).hom z) := rfl

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # The barycentric homeomorphism on full boundary unions

The preimage statement keeps a whole union of coordinate faces, which is
the relative parameter space in higher boundary lifting.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity PartialOrder RealizationPrism
open scoped Simplicial

noncomputable section

theorem subdividedFace_eq_permitted {n : ℕ} (S : Finset (Fin (n+1))) :
    subdividedFace S = fullSubposetComplex (permittedFaces n (S : Set (Fin (n+1)))) := by
  ext d s
  constructor
  · intro h i j hj
    exact h i (ULift.up j) hj
  · intro h i j hj
    exact h i j.down hj

theorem carrier_subdividedFaceUnion_iff {n : ℕ}
    (F : Finset (Finset (Fin (n+1)))) (z : SSet.toTop.obj (nerve (Faces n))) :
    carrier (nerve (Faces n)) z ≤ subdividedFaceUnion F ↔
      ∃ S ∈ F, carrier (nerve (Faces n)) z ≤ subdividedFace S := by
  let s := (normalization (nerve (Faces n)) z).1
  let p := (normalization (nerve (Faces n)) z).2
  have hp : p ∈ fullSupport s.dim := normalization_fullSupport _ z
  have he : simplexPoint (nerve (Faces n)) s.simplex p = z :=
    denormalize_normalization _ z
  rw [← he, carrier_interior (nerve (Faces n)) s.simplex p hp]
  have hm : s.simplex ∈ (subdividedFaceUnion F).obj _ ↔
      ∃ S ∈ F, s.simplex ∈ (subdividedFace S).obj _ := by
    rw [subdividedFaceUnion, Finset.sup_eq_iSup, Subfunctor.iSup_obj]
    constructor
    · intro h
      obtain ⟨S, hS⟩ := Set.mem_iUnion.mp h
      rw [Subfunctor.iSup_obj] at hS
      obtain ⟨hSF, hs⟩ := Set.mem_iUnion.mp hS
      exact ⟨S, hSF, hs⟩
    · rintro ⟨S, hSF, hs⟩
      apply Set.mem_iUnion.mpr
      refine ⟨S, ?_⟩
      rw [Subfunctor.iSup_obj]
      exact Set.mem_iUnion.mpr ⟨hSF, hs⟩
  constructor
  · intro h
    obtain ⟨S, hS, hs⟩ := hm.mp ((SSet.Subcomplex.ofSimplex_le_iff
      s.simplex (subdividedFaceUnion F)).mp h)
    exact ⟨S, hS, (SSet.Subcomplex.ofSimplex_le_iff s.simplex (subdividedFace S)).mpr hs⟩
  · rintro ⟨S, hS, hs⟩
    exact (SSet.Subcomplex.ofSimplex_le_iff s.simplex (subdividedFaceUnion F)).mpr
      (hm.mpr ⟨S, hS, (SSet.Subcomplex.ofSimplex_le_iff s.simplex (subdividedFace S)).mp hs⟩)

theorem point_faceUnion_preimage {n : ℕ} (F : Finset (Finset (Fin (n+1))))
    (z : SSet.toTop.obj (nerve (Faces n))) :
    (∃ S ∈ F, ∀ i ∉ S, (point n z).weights i = 0) ↔
      carrier (nerve (Faces n)) z ≤ subdividedFaceUnion F := by
  rw [carrier_subdividedFaceUnion_iff]
  apply exists_congr
  intro S
  apply and_congr_right
  intro _
  rw [subdividedFace_eq_permitted]
  exact point_face_preimage n (S : Set (Fin (n+1))) z

/-- Restriction to an arbitrary finite union of coordinate faces. -/
def faceUnionHomeomorph {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    SSet.toTop.obj (subdividedFaceUnion F).toSSet ≃ₜ
      {p : StdSimplex ℝ (Fin (n+1)) // ∃ S ∈ F, ∀ i ∉ S, p.weights i = 0} :=
  (carrierHomeomorph (nerve (Faces n)) (subdividedFaceUnion F)).trans
    ((homeomorph n).subtype (fun z => (point_faceUnion_preimage F z).symm))

theorem point_boundary_preimage (n : ℕ) (z : SSet.toTop.obj (nerve (Faces n))) :
    (∃ i, (point n z).weights i = 0) ↔
      carrier (nerve (Faces n)) z ≤ subdividedFaceUnion (boundaryFaces n) := by
  rw [← point_faceUnion_preimage]
  classical
  simp only [boundaryFaces, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨{i}ᶜ, ⟨i, rfl⟩, ?_⟩
    intro j hj
    have hj' : j = i := by simpa using hj
    simpa only [hj'] using hi
  · rintro ⟨S, ⟨i, rfl⟩, h⟩
    exact ⟨i, h i (by simp)⟩

/-- The full subdivided boundary realizes to the entire geometric boundary. -/
def boundaryHomeomorph (n : ℕ) :
    SSet.toTop.obj (subdividedFaceUnion (boundaryFaces n)).toSSet ≃ₜ
      {p : StdSimplex ℝ (Fin (n+1)) // ∃ i, p.weights i = 0} :=
  (carrierHomeomorph (nerve (Faces n)) (subdividedFaceUnion (boundaryFaces n))).trans
    ((homeomorph n).subtype (fun z => (point_boundary_preimage n z).symm))

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Barycentric homeomorphisms of the actual subdivided boundary pair

These maps use the left Kan extension subdivision functor and its proved
face images. The square with the entire boundary inclusion commutes.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity PartialOrder RealizationPrism
open scoped Simplicial

noncomputable section

def standardSubdivisionHomeomorph (n : ℕ) :
    SSet.toTop.obj (SSet.sd.obj (Δ[n] : SSet.{0})) ≃ₜ
      SSet.toTop.obj (Δ[n] : SSet.{0}) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.sdIso.app (.mk n)))).trans
    ((homeomorph n).trans (SimplexCategory.mk n).toTopHomeo.symm)

def boundarySubdivisionIso (n : ℕ) :
    SSet.sd.obj (SSet.boundary.{0} n).toSSet ≅
      (subdividedFaceUnion (boundaryFaces n)).toSSet := by
  have := subdivision_boundary_mono n
  have : Mono (subdivisionInclusion (SSet.boundary.{0} n)) := by
    dsimp only [subdivisionInclusion]
    infer_instance
  exact asIso (SSet.Subcomplex.toRange (subdivisionInclusion (SSet.boundary n))) ≪≫
    SSet.Subcomplex.eqToIso (subdivision_boundary_range n)

def boundarySubdivisionHomeomorph (n : ℕ) :
    SSet.toTop.obj (SSet.sd.obj (SSet.boundary.{0} n).toSSet) ≃ₜ
      SSet.toTop.obj (SSet.boundary.{0} n).toSSet :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (boundarySubdivisionIso n))).trans
    ((boundaryHomeomorph n).trans (RealizationPrism.boundaryHomeomorph n).symm)

theorem boundarySubdivisionIso_inclusion (n : ℕ) :
    (boundarySubdivisionIso n).hom ≫ (subdividedFaceUnion (boundaryFaces n)).ι =
      subdivisionInclusion (SSet.boundary.{0} n) := by
  simp [boundarySubdivisionIso]

/-- Both homeomorphisms are compatible with the actual boundary arrow. -/
theorem standardSubdivisionHomeomorph_boundary (n : ℕ)
    (z : SSet.toTop.obj (SSet.sd.obj (SSet.boundary.{0} n).toSSet)) :
    standardSubdivisionHomeomorph n
      ((SSet.toTop.map (SSet.sd.map (SSet.boundary.{0} n).ι)).hom z) =
      (SSet.toTop.map (SSet.boundary.{0} n).ι).hom
        (boundarySubdivisionHomeomorph n z) := by
  apply (SimplexCategory.mk n).toTopHomeo.injective
  let w := (SSet.toTop.map (boundarySubdivisionIso n).hom).hom z
  have hw : (SSet.toTop.map (subdividedFaceUnion (boundaryFaces n)).ι).hom w =
      (SSet.toTop.map (subdivisionInclusion (SSet.boundary.{0} n))).hom z := by
    have hf : SSet.toTop.map (boundarySubdivisionIso n).hom ≫
        SSet.toTop.map (subdividedFaceUnion (boundaryFaces n)).ι =
        SSet.toTop.map (subdivisionInclusion (SSet.boundary.{0} n)) := by
      rw [← SSet.toTop.map_comp, boundarySubdivisionIso_inclusion]
    exact ConcreteCategory.congr_hom hf z
  have hb := RealizationPrism.boundaryHomeomorph_inclusion n
    (boundarySubdivisionHomeomorph n z)
  have hh : (RealizationPrism.boundaryHomeomorph n
      (boundarySubdivisionHomeomorph n z)).val =
      point n ((SSet.toTop.map (subdividedFaceUnion (boundaryFaces n)).ι).hom w) := by
    change ((RealizationPrism.boundaryHomeomorph n)
      ((RealizationPrism.boundaryHomeomorph n).symm (boundaryHomeomorph n w))).val = _
    exact congrArg Subtype.val ((RealizationPrism.boundaryHomeomorph n).apply_symm_apply
      (show boundaryLocus n from boundaryHomeomorph n w))
  rw [← hb, hh, hw]
  change (SimplexCategory.mk n).toTopHomeo
      ((SimplexCategory.mk n).toTopHomeo.symm _) = _
  rw [Homeomorph.apply_symm_apply]
  exact congrArg (point n) (ConcreteCategory.congr_hom
    (SSet.toTop.map_comp (SSet.sd.map (SSet.boundary.{0} n).ι)
      (SSet.stdSimplex.sdIso.hom.app (.mk n))) z).symm

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # The actual sequential colimit of canonical extensions

Only the concrete tower, its finite support and the actual realization
weak equivalence are constructed here. Fibrancy is a separate obligation.
-/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The actual `n`-fold extension of the original simplicial set. -/
abbrev stage (X : SSet.{0}) (n : ℕ) : SSet.{0} :=
  Nat.rec X (fun _ Y => SSet.ex.obj Y) n

abbrev step (X : SSet.{0}) (n : ℕ) : stage X n ⟶ stage X (n+1) :=
  canonicalExtension.app (stage X n)

abbrev diagram (X : SSet.{0}) : ℕ ⥤ SSet.{0} where
  obj := stage X
  map {i j} f := Functor.OfSequence.map (step X) i j (leOfHom f)
  map_id i := Functor.OfSequence.map_id (step X) i
  map_comp f g := Functor.OfSequence.map_comp (step X) _ _ _ (leOfHom f) (leOfHom g)

theorem diagram_map_succ (X : SSet.{0}) (n : ℕ) :
    (diagram X).map (homOfLE (Nat.le_succ n)) = step X n :=
  Functor.OfSequence.map_le_succ (step X) n

/-- The chosen colimit of the canonical-extension tower. -/
abbrev obj (X : SSet.{0}) : SSet.{0} := colimit (diagram X)

abbrev inclusion (X : SSet.{0}) (n : ℕ) : stage X n ⟶ obj X :=
  colimit.ι (diagram X) n

abbrev unit (X : SSet.{0}) : X ⟶ obj X := inclusion X 0

@[reassoc]
theorem step_inclusion (X : SSet.{0}) (n : ℕ) :
    step X n ≫ inclusion X (n+1) = inclusion X n := by
  have h := colimit.w (diagram X) (homOfLE (Nat.le_succ n))
  simpa only [Functor.OfSequence.map_le_succ] using h

theorem map_mono_weak (X : SSet.{0}) (n m : ℕ) (h : n ≤ m) :
    Mono ((diagram X).map (homOfLE h)) ∧
      realizationWeakEquivalences ((diagram X).map (homOfLE h)) := by
  induction m, h using Nat.le_induction with
  | base =>
    have he : (diagram X).map (homOfLE (Nat.le_refl n)) = 𝟙 (stage X n) :=
      Functor.OfSequence.map_id (step X) n
    exact (congrArg (fun f : stage X n ⟶ stage X n =>
      Mono f ∧ realizationWeakEquivalences f) he).mpr
        ⟨inferInstance, realizationWeakEquivalences.id_mem _⟩
  | succ m h ih =>
    have he : (diagram X).map (homOfLE (h.trans (Nat.le_succ m))) =
        (diagram X).map (homOfLE h) ≫ step X m := by
      rw [show homOfLE (h.trans (Nat.le_succ m)) =
        homOfLE h ≫ homOfLE (Nat.le_succ m) from rfl, Functor.map_comp]
      rw [diagram_map_succ]
    rw [he]
    have := ih.1
    have : Mono (step X m) := canonicalExtension_mono _
    exact ⟨inferInstance, realizationWeakEquivalences.comp_mem _ _ ih.2
      (canonicalExtension_weak _)⟩

instance inclusion_mono (X : SSet.{0}) (n : ℕ) : Mono (inclusion X n) :=
  simplicial_sequence_leg_mono (diagram X) (colimit.isColimit (diagram X))
    (fun i j h => (map_mono_weak X i j h).1) n

/-- Stage images in the actual colimit, used only to control finite
families and to apply the proved realization exhaustion theorem. -/
abbrev range (X : SSet.{0}) (n : ℕ) : (obj X).Subcomplex :=
  SSet.Subcomplex.range (inclusion X n)

theorem range_monotone (X : SSet.{0}) : Monotone (range X) := by
  intro n m h
  change SSet.Subcomplex.range (inclusion X n) ≤
    SSet.Subcomplex.range (inclusion X m)
  have hf : (diagram X).map (homOfLE h) ≫ inclusion X m = inclusion X n :=
    colimit.w (diagram X) (homOfLE h)
  rw [← hf]
  exact Subfunctor.range_comp_le _ _

theorem range_iSup (X : SSet.{0}) : iSup (range X) = ⊤ := by
  apply top_unique
  intro d x _
  obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (SSet.evaluation.obj d) (colimit.isColimit (diagram X))) x
  rw [Subfunctor.iSup_obj, Set.mem_iUnion]
  exact ⟨n, y, hy⟩

def rangeIso (X : SSet.{0}) (n : ℕ) : stage X n ≅ (range X n).toSSet := by
  let f := SSet.Subcomplex.toRange (inclusion X n)
  have : Mono f := mono_of_mono_fac (SSet.Subcomplex.toRange_ι (inclusion X n))
  have : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

@[reassoc]
theorem rangeIso_hom_inclusion (X : SSet.{0}) (n : ℕ) :
    (rangeIso X n).hom ≫ (range X n).ι = inclusion X n := rfl

theorem range_initial_map_weak (X : SSet.{0}) (n : ℕ) :
    realizationWeakEquivalences
      (SSet.Subcomplex.homOfLE (range_monotone X (Nat.zero_le n))) := by
  have h : (diagram X).map (homOfLE (Nat.zero_le n)) ≫ (rangeIso X n).hom =
      (rangeIso X 0).hom ≫
        SSet.Subcomplex.homOfLE (range_monotone X (Nat.zero_le n)) := by
    apply (cancel_mono (range X n).ι).mp
    rw [Category.assoc, rangeIso_hom_inclusion]
    change (diagram X).map (homOfLE (Nat.zero_le n)) ≫ inclusion X n =
      (rangeIso X 0).hom ≫ (range X 0).ι
    rw [rangeIso_hom_inclusion]
    exact colimit.w (diagram X) (homOfLE (Nat.zero_le n))
  apply realizationWeakEquivalences.of_precomp (rangeIso X 0).hom _
    (realizationWeakEquivalences.of_isIso _)
  rw [← h]
  exact realizationWeakEquivalences.comp_mem _ _ (map_mono_weak X 0 n (Nat.zero_le n)).2
    (realizationWeakEquivalences.of_isIso _)

/-- The original simplicial set maps weakly into the actual sequential
colimit. Compact cubes and based homotopies give the finite-stage witnesses. -/
theorem unit_weak (X : SSet.{0}) : realizationWeakEquivalences (unit X) := by
  have h := RealizationPrism.exhaustion_initial_weak (obj X) (range X)
    (range_monotone X) (range_iSup X) (range_initial_map_weak X)
  change realizationWeakEquivalences (inclusion X 0)
  rw [← rangeIso_hom_inclusion X 0]
  exact realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso _) h

/-- Every finite simplicial family in the infinite extension is already
an exact family in a single finite iterate. -/
theorem finite_map_factors {A : SSet.{0}} [A.Finite] (X : SSet.{0})
    (f : A ⟶ obj X) :
    ∃ (n : ℕ) (g : A ⟶ stage X n), g ≫ inclusion X n = f := by
  let e : (iSup (range X)).toSSet ≅ obj X :=
    SSet.Subcomplex.eqToIso (range_iSup X) ≪≫ SSet.Subcomplex.topIso (obj X)
  obtain ⟨n, g, hg⟩ := finite_map_iSup_factors (range X) (range_monotone X) (f ≫ e.inv)
  refine ⟨n, g ≫ (rangeIso X n).inv, ?_⟩
  rw [Category.assoc, ← rangeIso_hom_inclusion X n, Iso.inv_hom_id_assoc]
  have he : e.hom = (iSup (range X)).ι := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [← he] at hg
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hg

/-- Factoring a finite family through a stage preserves its complete
prescribed boundary from the original simplicial set. -/
theorem finite_relative_map_factors {A K : SSet.{0}} [K.Finite]
    (X : SSet.{0}) (i : A ⟶ K) (a : A ⟶ X) (f : K ⟶ obj X)
    (hf : i ≫ f = a ≫ unit X) :
    ∃ (n : ℕ) (g : K ⟶ stage X n),
      g ≫ inclusion X n = f ∧
      i ≫ g = a ≫ (diagram X).map (homOfLE (Nat.zero_le n)) := by
  obtain ⟨n, g, hg⟩ := finite_map_factors X f
  refine ⟨n, g, hg, ?_⟩
  apply (cancel_mono (inclusion X n)).mp
  rw [Category.assoc, hg, hf, Category.assoc]
  exact congrArg (fun k => a ≫ k) (colimit.w (diagram X) (homOfLE (Nat.zero_le n))).symm

/-- Compact continuous families also occur at one finite extension stage.
The factorization is exact on every point of the parameter space. -/
theorem compact_map_factors {Z : Type} [TopologicalSpace Z] [CompactSpace Z]
    (X : SSet.{0}) (f : C(Z, SSet.toTop.obj (obj X))) :
    ∃ (n : ℕ) (g : C(Z, SSet.toTop.obj (stage X n))),
      (SSet.toTop.map (inclusion X n)).hom.comp g = f := by
  obtain ⟨S, hS, c, hc⟩ := RealizationPrism.compact_map_factors (obj X) f
  let := hS
  obtain ⟨n, g, hg⟩ := finite_map_factors X S.ι
  refine ⟨n, (SSet.toTop.map g).hom.comp c, ?_⟩
  calc
    _ = (SSet.toTop.map (g ≫ inclusion X n)).hom.comp c := by
      rw [SSet.toTop.map_comp]
      rfl
    _ = f := by rw [hg]; exact hc

end

end Thomason.Construction.InfiniteExtension

end

section

/-! # Functoriality and weak equivalences of the extension colimit -/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits

noncomputable section

def stageMap {X Y : SSet.{0}} (f : X ⟶ Y) : ∀ n, stage X n ⟶ stage Y n
  | 0 => f
  | n+1 => SSet.ex.map (stageMap f n)

@[simp] theorem stageMap_id (X : SSet.{0}) (n : ℕ) :
    stageMap (𝟙 X) n = 𝟙 (stage X n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change SSet.ex.map (stageMap (𝟙 X) n) = 𝟙 (SSet.ex.obj (stage X n))
    rw [ih]
    exact SSet.ex.map_id _

@[simp] theorem stageMap_comp {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    stageMap (f ≫ g) n = stageMap f n ≫ stageMap g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change SSet.ex.map (stageMap (f ≫ g) n) =
      SSet.ex.map (stageMap f n) ≫ SSet.ex.map (stageMap g n)
    rw [ih, SSet.ex.map_comp]

def diagramMap {X Y : SSet.{0}} (f : X ⟶ Y) : diagram X ⟶ diagram Y :=
  NatTrans.ofSequence (stageMap f) (by
    intro n
    rw [diagram_map_succ, diagram_map_succ]
    exact (canonicalExtension.naturality (stageMap f n)).symm)

def map {X Y : SSet.{0}} (f : X ⟶ Y) : obj X ⟶ obj Y := colimMap (diagramMap f)

@[reassoc] theorem inclusion_map {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ) :
    inclusion X n ≫ map f = stageMap f n ≫ inclusion Y n :=
  ι_colimMap (diagramMap f) n

theorem map_id (X : SSet.{0}) : map (𝟙 X) = 𝟙 (obj X) := by
  apply colimit.hom_ext
  intro n
  change inclusion X n ≫ map (𝟙 X) = inclusion X n ≫ 𝟙 _
  rw [inclusion_map, stageMap_id, Category.id_comp, Category.comp_id]

theorem map_comp {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ map g := by
  apply colimit.hom_ext
  intro n
  change inclusion X n ≫ map (f ≫ g) = inclusion X n ≫ map f ≫ map g
  rw [inclusion_map, stageMap_comp, Category.assoc,
    ← inclusion_map, ← Category.assoc]
  exact congrArg (fun h => h ≫ map g) (inclusion_map f n).symm

/-- The actual colimit construction, as an endofunctor on simplicial sets. -/
def functor : SSet.{0} ⥤ SSet.{0} where
  obj := obj
  map := map
  map_id := map_id
  map_comp := map_comp

/-- Its canonical coaugmentation is the inclusion of the original stage. -/
def coaugmentation : 𝟭 SSet.{0} ⟶ functor where
  app := unit
  naturality _ _ f := (inclusion_map f 0).symm

/-- The sequential extension construction preserves and reflects actual
realization weak equivalences, without any fibrancy assertion. -/
theorem map_weak_iff {X Y : SSet.{0}} (f : X ⟶ Y) :
    realizationWeakEquivalences (map f) ↔ realizationWeakEquivalences f :=
  map_iff_of_weak_coaugmentation realizationWeakEquivalences functor coaugmentation unit_weak f

end

end Thomason.Construction.InfiniteExtension

end

section

/-! # The infinite extension creates no new original subobject preimages -/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits

noncomputable section

abbrev stageUnit (X : SSet.{0}) (n : ℕ) : X ⟶ stage X n :=
  (diagram X).map (homOfLE (Nat.zero_le n))

theorem stageUnit_zero (X : SSet.{0}) : stageUnit X 0 = 𝟙 X :=
  Functor.OfSequence.map_id (step X) 0

theorem stageUnit_succ (X : SSet.{0}) (n : ℕ) :
    stageUnit X (n+1) = stageUnit X n ≫ canonicalExtension.app (stage X n) := by
  change (diagram X).map (homOfLE (Nat.zero_le (n+1))) = _
  rw [show homOfLE (Nat.zero_le (n+1)) =
    homOfLE (Nat.zero_le n) ≫ homOfLE (Nat.le_succ n) from rfl, Functor.map_comp]
  rw [diagram_map_succ]

private theorem stageMap_isMono {A B : SSet.{0}} (i : A ⟶ B) [Mono i]
    (n : ℕ) : Mono (stageMap i n) := by
  induction n with
  | zero => exact inferInstanceAs (Mono i)
  | succ n ih =>
    have := ih
    change Mono (SSet.ex.map (stageMap i n))
    infer_instance

/-- The cartesian property persists through every finite extension stage. -/
theorem stageUnit_simplex_lift {A B : SSet.{0}} (i : A ⟶ B) [Mono i]
    (n : ℕ) (d : SimplexCategory) (x : SSet.stdSimplex.obj d ⟶ B)
    (a : SSet.stdSimplex.obj d ⟶ stage A n)
    (h : x ≫ stageUnit B n = a ≫ stageMap i n) :
    ∃ b : SSet.stdSimplex.obj d ⟶ A, b ≫ i = x ∧ b ≫ stageUnit A n = a := by
  induction n with
  | zero =>
    refine ⟨a, ?_, ?_⟩
    · change x ≫ stageUnit B 0 = a ≫ i at h
      rw [stageUnit_zero, Category.comp_id] at h
      exact h.symm
    · rw [stageUnit_zero, Category.comp_id]
  | succ n ih =>
    have := stageMap_isMono i n
    have hh : (x ≫ stageUnit B n) ≫ canonicalExtension.app (stage B n) =
        a ≫ SSet.ex.map (stageMap i n) := by
      change x ≫ stageUnit B (n+1) = a ≫ SSet.ex.map (stageMap i n) at h
      simpa only [stageUnit_succ, Category.assoc] using h
    obtain ⟨c, hc, ha⟩ := canonicalExtension_simplex_lift (stageMap i n) d _ a hh
    obtain ⟨b, hb, hc'⟩ := ih c hc.symm
    refine ⟨b, hb, ?_⟩
    rw [stageUnit_succ, ← Category.assoc, hc', ha]

/-- Every simplex in the infinite extension over an original simplex of
`B` already comes from the corresponding original subobject. -/
theorem unit_simplex_lift {A B : SSet.{0}} (i : A ⟶ B) [Mono i]
    (d : SimplexCategory) (x : SSet.stdSimplex.obj d ⟶ B)
    (a : SSet.stdSimplex.obj d ⟶ obj A)
    (h : x ≫ unit B = a ≫ map i) :
    ∃ b : SSet.stdSimplex.obj d ⟶ A, b ≫ i = x ∧ b ≫ unit A = a := by
  obtain ⟨n, g, hg⟩ := finite_map_factors A a
  have hn : x ≫ stageUnit B n = g ≫ stageMap i n := by
    apply (cancel_mono (inclusion B n)).mp
    calc
      _ = x ≫ unit B := by rw [Category.assoc, colimit.w]
      _ = a ≫ map i := h
      _ = (g ≫ inclusion A n) ≫ map i := congrArg (· ≫ map i) hg.symm
      _ = _ := by rw [Category.assoc, inclusion_map, Category.assoc]
  obtain ⟨b, hb, hb'⟩ := stageUnit_simplex_lift i n d x g hn
  refine ⟨b, hb, ?_⟩
  calc
    _ = b ≫ (stageUnit A n ≫ inclusion A n) :=
      congrArg (b ≫ ·) (colimit.w (diagram A) (homOfLE (Nat.zero_le n))).symm
    _ = g ≫ inclusion A n := by rw [← Category.assoc, hb']
    _ = a := hg

/-- The coaugmentation into the constructed Kan replacement is cartesian
along every monomorphism. -/
theorem unit_isPullback {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    IsPullback i (unit A) (unit B) (map i) := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  rw [Types.isPullback_iff]
  refine ⟨NatTrans.congr_app (coaugmentation.naturality i) n, ?_, ?_⟩
  · intro x y h
    exact (injective_of_mono (i.app n)) h.1
  · intro x a h
    have he : (SSet.yonedaEquiv.symm x : SSet.stdSimplex.obj n.unop ⟶ B) ≫
        unit B = SSet.yonedaEquiv.symm a ≫ map i := by
      simpa only [SSet.yonedaEquiv_symm_comp] using congrArg SSet.yonedaEquiv.symm h
    obtain ⟨b, hb, ha⟩ := unit_simplex_lift i n.unop _ _ he
    refine ⟨SSet.yonedaEquiv b, ?_, ?_⟩
    · simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
        congrArg SSet.yonedaEquiv hb
    · simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
        congrArg SSet.yonedaEquiv ha

/-- No new preimages of an original subobject appear in the Kan
replacement, even at the sequential colimit. -/
theorem unit_preimage_range {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    (SSet.Subcomplex.range (map i)).preimage (unit B) = SSet.Subcomplex.range i :=
  preimage_range_of_isPullback (unit_isPullback i)

end

end Thomason.Construction.InfiniteExtension

end

section

/-! # Finite limits of the actual extension tower

The stage functors are right adjoints, and the tower is a filtered colimit
in simplicial sets. The canonical finite-limit comparisons are therefore
isomorphisms, for the same colimit used in the weak-equivalence theorem.
-/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- Iterated extension, with precisely the maps used in the colimit tower. -/
def stageFunctor (n : ℕ) : SSet.{0} ⥤ SSet.{0} where
  obj X := stage X n
  map f := stageMap f n
  map_id X := stageMap_id X n
  map_comp f g := stageMap_comp f g n

instance stageFunctor_preservesLimits (n : ℕ) : PreservesLimits (stageFunctor n) := by
  induction n with
  | zero => exact inferInstanceAs (PreservesLimits (𝟭 SSet.{0}))
  | succ n ih =>
    change PreservesLimits (stageFunctor n ⋙ SSet.ex)
    have := ih
    infer_instance

/-- The whole sequence, before taking its colimit. -/
def towerFunctor : SSet.{0} ⥤ ℕ ⥤ SSet.{0} where
  obj := diagram
  map := diagramMap
  map_id X := by
    apply NatTrans.ext
    funext n
    exact stageMap_id X n
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact stageMap_comp f g n

def towerEvaluationIso (n : ℕ) :
    towerFunctor ⋙ (evaluation ℕ SSet.{0}).obj n ≅ stageFunctor n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; rfl)

instance towerFunctor_preservesLimits : PreservesLimits towerFunctor := by
  apply preservesLimits_of_evaluation
  intro n
  exact preservesLimits_of_natIso (towerEvaluationIso n).symm

instance simplicialSequenceColimit_preservesFiniteLimits :
    PreservesFiniteLimits (colim : (ℕ ⥤ SSet.{0}) ⥤ SSet.{0}) := by
  apply preservesFiniteLimits_of_evaluation
  intro d
  exact preservesFiniteLimits_of_natIso
    (preservesColimitNatIso (SSet.evaluation.obj d)).symm

def colimitFunctorIso : towerFunctor ⋙ colim ≅ functor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; rfl)

/-- Extension to infinity commutes with finite limits, including the
pullbacks used for Kan fibres and base change. -/
instance functor_preservesFiniteLimits : PreservesFiniteLimits functor :=
  preservesFiniteLimits_of_natIso colimitFunctorIso

end

end Thomason.Construction.InfiniteExtension

end

section

/-! # Extension to infinity preserves filtered colimits

Each actual stage is a finite iterate of extension. Its filtered-colimit
preservation passes to the tower and then to the same sequential colimit
used in the constructed fibrant replacement.
-/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Category.{0} J] [IsFiltered J]

instance stageFunctor_preservesFilteredColimitsOfShape (n : ℕ) :
    PreservesColimitsOfShape J (stageFunctor n) := by
  induction n with
  | zero => exact inferInstanceAs (PreservesColimitsOfShape J (𝟭 SSet.{0}))
  | succ n ih =>
    change PreservesColimitsOfShape J (stageFunctor n ⋙ SSet.ex)
    have := ih
    infer_instance

instance towerFunctor_preservesFilteredColimitsOfShape :
    PreservesColimitsOfShape J towerFunctor := by
  apply preservesColimitsOfShape_of_evaluation
  intro n
  exact preservesColimitsOfShape_of_natIso (towerEvaluationIso n).symm

instance functor_preservesFilteredColimitsOfShape :
    PreservesColimitsOfShape J functor :=
  preservesColimitsOfShape_of_natIso colimitFunctorIso

instance functor_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{0,0} functor where
  preserves_filtered_colimits _J := inferInstance

end Thomason.Construction.InfiniteExtension

end

section

/-! # Kan lifting retained through the actual extension tower -/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

theorem stageMap_fibration {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] (n : ℕ) :
    HomotopicalAlgebra.Fibration (stageMap p n) := by
  induction n with
  | zero => exact inferInstanceAs (HomotopicalAlgebra.Fibration p)
  | succ n ih =>
    change HomotopicalAlgebra.Fibration (SSet.ex.map (stageMap p n))
    have := ih
    infer_instance

/-- A Kan lifting square in the colimit lies in a common finite stage.
Its exact commutativity there follows from the monic stage inclusion. -/
theorem map_horn_lifting {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] (n : ℕ) (k : Fin (n+2)) :
    HasLiftingProperty (SSet.horn (n+1) k).ι (map p) := by
  refine ⟨fun {a b} sq => ?_⟩
  obtain ⟨r, a₀, ha₀⟩ := finite_map_factors X a
  obtain ⟨s, b₀, hb₀⟩ := finite_map_factors Y b
  let m := max r s
  let a₁ := a₀ ≫ (diagram X).map (homOfLE (Nat.le_max_left r s))
  let b₁ := b₀ ≫ (diagram Y).map (homOfLE (Nat.le_max_right r s))
  have ha₁ : a₁ ≫ inclusion X m = a := by
    dsimp only [a₁, m]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => a₀ ≫ f)
        (colimit.w (diagram X) (homOfLE (Nat.le_max_left r s)))).trans ha₀)
  have hb₁ : b₁ ≫ inclusion Y m = b := by
    dsimp only [b₁, m]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => b₀ ≫ f)
        (colimit.w (diagram Y) (homOfLE (Nat.le_max_right r s)))).trans hb₀)
  have hh : a₁ ≫ stageMap p m = (SSet.horn (n+1) k).ι ≫ b₁ := by
    apply (cancel_mono (inclusion Y m)).mp
    calc
      (a₁ ≫ stageMap p m) ≫ inclusion Y m =
          (a₁ ≫ inclusion X m) ≫ map p := by
        rw [Category.assoc, ← inclusion_map, ← Category.assoc]
      _ = a ≫ map p := by rw [ha₁]
      _ = (SSet.horn (n+1) k).ι ≫ b := sq.w
      _ = ((SSet.horn (n+1) k).ι ≫ b₁) ≫ inclusion Y m := by
        rw [Category.assoc, hb₁]
  have : HomotopicalAlgebra.Fibration (stageMap p m) := stageMap_fibration p m
  have : HasLiftingProperty (SSet.horn (n+1) k).ι (stageMap p m) :=
    ((fibration_iff _).mp inferInstance) _ (horn_ι_mem_J _ _)
  let t : CommSq a₁ (SSet.horn (n+1) k).ι (stageMap p m) b₁ := ⟨hh⟩
  refine ⟨⟨{ l := t.lift ≫ inclusion X m, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, t.fac_left, ha₁]
  · rw [Category.assoc, inclusion_map, ← Category.assoc, t.fac_right, hb₁]

/-- The extension colimit preserves Kan fibrations. -/
theorem map_fibration {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] : HomotopicalAlgebra.Fibration (map p) := by
  apply (fibration_iff _).mpr
  intro A B i hi
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  exact map_horn_lifting _ n k

theorem stage_kan (X : SSet.{0}) [SSet.KanComplex X] (n : ℕ) :
    SSet.KanComplex (stage X n) := by
  induction n with
  | zero => exact inferInstanceAs (SSet.KanComplex X)
  | succ n ih =>
    change SSet.KanComplex (SSet.ex.obj (stage X n))
    have := ih
    infer_instance

/-- For an already Kan complex, the extension colimit remains Kan. The
arbitrary-source fibrancy theorem requires a further explicit horn filler. -/
theorem horn_filling_of_kan (X : SSet.{0}) [SSet.KanComplex X]
    (n : ℕ) (k : Fin (n+2)) :
    HasLiftingProperty (SSet.horn (n+1) k).ι (terminal.from (obj X)) := by
  refine ⟨fun {a _} _ => ?_⟩
  obtain ⟨m, a₀, ha₀⟩ := finite_map_factors X a
  have : SSet.KanComplex (stage X m) := stage_kan X m
  obtain ⟨d, hd⟩ := SSet.KanComplex.hornFilling a₀
  refine ⟨⟨{ l := d ≫ inclusion X m, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, ← hd, ha₀]
  · exact terminalIsTerminal.hom_ext _ _

/-- A Kan source remains Kan after the sequential extension construction. -/
theorem kan_of_kan (X : SSet.{0}) [SSet.KanComplex X] : SSet.KanComplex (obj X) := by
  apply (HomotopicalAlgebra.isFibrant_iff (obj X)).mpr
  apply (fibration_iff _).mpr
  intro A B i hi
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  exact horn_filling_of_kan _ n k

end

end Thomason.Construction.InfiniteExtension

end

end OAI
