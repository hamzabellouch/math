import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Simplicial.FiniteRelativeRealizationLifting
import OAI.CategoryTheory.Thomason.Simplicial.KanBaseChangeExhaustion
import OAI.CategoryTheory.Thomason.Simplicial.SimplexCubeRetract
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Simplicial.SkeletalWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionUnions
import OAI.CategoryTheory.Thomason.Transfer.NonsingularFaceGluing
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.SetTheory.Cardinal.NatCard

namespace OAI

section

/-! # Last-vertex weak equivalences on finite unions of simplex faces -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

theorem lastVertex_initial_weak {K : SSet.{0}} (hi : IsInitial K) :
    realizationWeakEquivalences (lastVertex.app K) := by
  have hj := IsInitial.isInitialObj SSet.sd _ hi
  let e : SSet.sd.obj K ≅ K := hj.uniqueUpToIso hi
  have he : e.hom = lastVertex.app K := hj.hom_ext _ _
  rw [← he]
  exact realizationWeakEquivalences.of_isIso _

/-- The original last-vertex component is weak on any individual face. -/
theorem lastVertex_face_weak {n : ℕ} (S : Finset (Fin (n+1))) :
    realizationWeakEquivalences (lastVertex.app (SSet.stdSimplex.face S : SSet.{0})) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hs
  · apply lastVertex_initial_weak
    simpa only [SSet.stdSimplex.face_empty] using
      (SSet.Subcomplex.isInitialBot (X := (Δ[n] : SSet.{0})))
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hs)
    let e := SSet.stdSimplex.isoOfRepresentableBy
      (SSet.stdSimplex.faceRepresentableBy S m (monoEquivOfFin S (by simpa using hm)))
    apply realizationWeakEquivalences.of_precomp (SSet.sd.map e.hom) _
      (realizationWeakEquivalences.of_isIso _)
    rw [lastVertex.naturality e.hom]
    exact realizationWeakEquivalences.comp_mem _ _
      (lastVertex_standard_weak ⦋m⦌) (realizationWeakEquivalences.of_isIso _)

/-- Actual last-vertex comparison is compatible with geometric gluing. -/
theorem lastVertex_union_weak {n : ℕ} (A B : (Δ[n] : SSet.{0}).Subcomplex)
    (hi : Mono (subdivisionInclusion (A ⊓ B)))
    (hI : realizationWeakEquivalences (lastVertex.app ((A ⊓ B).toSSet)))
    (hA : realizationWeakEquivalences (lastVertex.app (A : SSet)))
    (hB : realizationWeakEquivalences (lastVertex.app (B : SSet))) :
    realizationWeakEquivalences (lastVertex.app ((A ⊔ B).toSSet)) := by
  have sq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  have hm : Mono (SSet.sd.map (SSet.Subcomplex.homOfLE sq.le₁₂)) := by
    have hcomp : Mono (SSet.sd.map (SSet.Subcomplex.homOfLE sq.le₁₂) ≫
        subdivisionInclusion A) := by rw [subdivisionInclusion_fac]; exact hi
    exact mono_of_mono _ (subdivisionInclusion A)
  exact constructedSimplicialGluingUnconditional.glue (sq.isPushout.map SSet.sd) sq.isPushout
    (lastVertex.app _) (lastVertex.app _) (lastVertex.app _) (lastVertex.app _)
    (lastVertex.naturality _) (lastVertex.naturality _)
    (lastVertex.naturality _) (lastVertex.naturality _) hI hA hB

private theorem lastVertex_faceUnion_weak_aux {n : ℕ} (k : ℕ) :
    ∀ F : Finset (Finset (Fin (n+1))), F.card = k →
      realizationWeakEquivalences (lastVertex.app (faceUnion F : SSet)) := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro F hF
    rcases F.eq_empty_or_nonempty with rfl | hne
    · apply lastVertex_initial_weak
      exact SSet.Subcomplex.isInitialBot
    · obtain ⟨S, hS⟩ := hne
      let G := F.erase S
      have hk : G.card < k := by
        rw [← hF]
        exact Finset.card_erase_lt_of_mem hS
      have hG := ih G.card hk G rfl
      let H := G.image (fun T => T ∩ S)
      have hH := ih H.card
        (lt_of_le_of_lt (Finset.card_image_le) hk) H rfl
      have hI : realizationWeakEquivalences
          (lastVertex.app ((faceUnion G ⊓ SSet.stdSimplex.face S).toSSet)) := by
        rw [faceUnion_inter_face]
        exact hH
      have hm : Mono (subdivisionInclusion (faceUnion G ⊓ SSet.stdSimplex.face S)) := by
        rw [faceUnion_inter_face]
        exact (finiteFaceUnion_mono_range H).1
      have hfg : F = insert S G := (Finset.insert_erase hS).symm
      have hf : faceUnion F = faceUnion G ⊔ SSet.stdSimplex.face S := by
        rw [hfg]
        simp only [faceUnion, Finset.sup_insert, sup_comm]
      rw [hf]
      exact lastVertex_union_weak _ _ hm hI hG (lastVertex_face_weak S)

/-- No last-vertex or Kan–Quillen hypothesis: this uses the explicit chain
contractions and the proved weak-equivalence gluing theorem. -/
theorem lastVertex_faceUnion_weak {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    realizationWeakEquivalences (lastVertex.app (faceUnion F : SSet)) :=
  lastVertex_faceUnion_weak_aux F.card F rfl

end

end Thomason.Construction

end

section

/-! # The finite nonsingular face-poset comparison is weak

Delete a maximal face and glue back its principal ideal. The original
simplicial target is retained throughout the induction.
-/

namespace Thomason.Construction.NonsingularLastVertex

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

variable {X : SSet.{0}} [X.Nonsingular]

omit [X.Nonsingular] in
private theorem proper_subset_card_lt {S D : Set X.N} [Finite S]
    (hDS : D ⊆ S) (m : S) (hm : m.val ∉ D) : Nat.card D < Nat.card S := by
  let f : D → S := fun d => ⟨d.val, hDS d.property⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (show a.val = b.val from congrArg (fun y : S => y.val) h)
  have hn : ¬Function.Surjective f := by
    intro hs
    obtain ⟨d, hd⟩ := hs m
    exact hm ((congrArg Subtype.val hd) ▸ d.property)
  apply lt_of_le_of_ne (Nat.card_le_card_of_injective f hf)
  intro he
  exact hn ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, he⟩).2

/-- The actual comparison on any finite lower set of nondegenerate faces
is a realization weak equivalence. -/
theorem restrictedMap_weak_finite (S : Set X.N) (hS : IsLowerSet S) [Finite S] :
    realizationWeakEquivalences (restrictedMap S) := by
  classical
  have main : ∀ k : ℕ, ∀ (S : Set X.N), IsLowerSet S → ∀ [Finite S],
      Nat.card S ≤ k → realizationWeakEquivalences (restrictedMap S) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro S hS _ hcard
      rcases isEmpty_or_nonempty S with he | hn
      · exact restrictedMap_weak_of_empty S
      · let := Fintype.ofFinite S
        obtain ⟨m, hm⟩ := (Finset.univ : Finset S).exists_maximal
          (Finset.univ_nonempty : (Finset.univ : Finset S).Nonempty)
        let A : Set X.N := {x | x ∈ S ∧ x ≠ m.val}
        let B : Set X.N := {x | x ∈ S ∧ x ≤ m.val}
        have hAS : A ⊆ S := fun _ h => h.1
        have hBS : B ⊆ S := fun _ h => h.1
        have hA : IsLowerSet A := by
          intro y x hxy hy
          refine ⟨hS hxy hy.1, ?_⟩
          intro hx
          have hmy : m ≤ (⟨y, hy.1⟩ : S) := by
            change m.val ≤ y
            exact hx ▸ hxy
          have hym := hm.2 (Finset.mem_univ (⟨y, hy.1⟩ : S)) hmy
          exact hy.2 (congrArg Subtype.val (le_antisymm hym hmy))
        have hB : IsLowerSet B := by
          intro y x hxy hy
          exact ⟨hS hxy hy.1, hxy.trans hy.2⟩
        have hcover : A ∪ B = S := by
          ext x
          constructor
          · rintro (h | h)
            · exact h.1
            · exact h.1
          · intro hx
            by_cases he : x = m.val
            · exact Or.inr ⟨hx, he ▸ le_rfl⟩
            · exact Or.inl ⟨hx, he⟩
        have small (D : Set X.N) (hDS : D ⊆ S) (hD : IsLowerSet D)
            (hmD : m.val ∉ D) : realizationWeakEquivalences (restrictedMap D) := by
          have : Finite D := Finite.of_injective
            (fun d : D => (⟨d.val, hDS d.property⟩ : S))
            (fun a b h => Subtype.ext (show a.val = b.val from congrArg (fun y : S => y.val) h))
          exact ih (Nat.card D) ((proper_subset_card_lt hDS m hmD).trans_le hcard)
            D hD le_rfl
        have wA := small A hAS hA (by simp [A])
        have wI := small (A ∩ B) (Set.inter_subset_left.trans hAS) (hA.inter hB)
          (by simp [A])
        have wB : realizationWeakEquivalences (restrictedMap B) :=
          restrictedMap_weak_of_greatest B ⟨m.val, m.property, le_rfl⟩ (fun b => b.property.2)
        rw [← hcover]
        exact restrictedMap_weak_union A B hA hB wA wB wI
  exact main (Nat.card S) S hS le_rfl

omit [X.Nonsingular] in
private theorem univ_nerveMap_isIso :
    IsIso (nerveMap (faceInclusion (Set.univ : Set X.N)).monotone.functor) := by
  let r : X.N →o (Set.univ : Set X.N) :=
    ⟨fun x => ⟨x, Set.mem_univ x⟩, fun _ _ h => h⟩
  refine ⟨⟨nerveMap r.monotone.functor, ?_, ?_⟩⟩
  · rw [← orderNerveMap_comp]
    have he : r.comp (faceInclusion (Set.univ : Set X.N)) =
        (OrderHom.id : (Set.univ : Set X.N) →o (Set.univ : Set X.N)) := by
      ext x
      rfl
    rw [he, orderNerveMap_id]
  · rw [← orderNerveMap_comp]
    have he : (faceInclusion (Set.univ : Set X.N)).comp r =
        (OrderHom.id : X.N →o X.N) := by
      ext x
      rfl
    rw [he, orderNerveMap_id]

/-- Every finite nonsingular simplicial set has its actual finite face
poset as a weakly equivalent simplicial model. -/
theorem map_weak (X : SSet.{0}) [X.Nonsingular] [X.Finite] :
    realizationWeakEquivalences (map X) := by
  have w := restrictedMap_weak_finite (X := X) Set.univ
    (fun _ _ _ _ => Set.mem_univ _)
  have : IsIso (faceUnion (X := X) Set.univ).ι := by
    rw [faceUnion_univ]
    infer_instance
  have wn : IsIso (nerveMap (faceInclusion (Set.univ : Set X.N)).monotone.functor) :=
    univ_nerveMap_isIso
  apply realizationWeakEquivalences.of_precomp
    (nerveMap (faceInclusion (Set.univ : Set X.N)).monotone.functor) _
    (realizationWeakEquivalences.of_isIso _)
  rw [← restrictedMap_ι]
  exact realizationWeakEquivalences.comp_mem _ _ w
    (realizationWeakEquivalences.of_isIso _)

end

end Thomason.Construction.NonsingularLastVertex

end

section

/-! # Actual subdivided boundaries and their last-vertex weak equivalences -/

namespace Thomason.Construction

open CategoryTheory PartialOrder
open scoped Simplicial

noncomputable section

def boundaryFaces (n : ℕ) : Finset (Finset (Fin (n+1))) :=
  Finset.univ.image (fun i => {i}ᶜ)

theorem faceUnion_boundaryFaces (n : ℕ) :
    faceUnion (boundaryFaces n) = SSet.boundary.{0} n := by
  classical
  unfold faceUnion boundaryFaces
  rw [Finset.sup_image, Finset.sup_eq_iSup]
  simpa only [Finset.mem_univ, iSup_pos, Function.comp_def] using
    (SSet.boundary_eq_iSup n).symm

/-- No identifications are introduced in subdividing the entire boundary. -/
theorem subdivision_boundary_mono (n : ℕ) :
    Mono (SSet.sd.map (SSet.boundary.{0} n).ι) := by
  have hm : Mono (subdivisionInclusion (SSet.boundary.{0} n)) := by
    rw [← faceUnion_boundaryFaces]
    exact (finiteFaceUnion_mono_range (boundaryFaces n)).1
  have : Mono (SSet.sd.map (SSet.boundary.{0} n).ι ≫
      SSet.stdSimplex.sdIso.hom.app ⦋n⦌) := hm
  exact mono_of_mono _ (SSet.stdSimplex.sdIso.hom.app ⦋n⦌)

/-- Exact finite-chain image of the subdivided whole boundary. -/
theorem subdivision_boundary_range (n : ℕ) :
    SSet.Subcomplex.range (subdivisionInclusion (SSet.boundary.{0} n)) =
      subdividedFaceUnion (boundaryFaces n) := by
  rw [← faceUnion_boundaryFaces]
  exact (finiteFaceUnion_mono_range (boundaryFaces n)).2

/-- The last-vertex map on every boundary is an actual realization weak
 equivalence, derived by finite face gluing. -/
theorem lastVertex_boundary_weak (n : ℕ) :
    realizationWeakEquivalences (lastVertex.app (SSet.boundary.{0} n : SSet)) := by
  rw [← faceUnion_boundaryFaces]
  exact lastVertex_faceUnion_weak (boundaryFaces n)

end

end Thomason.Construction

end

section

/-! # Subdivision preserves monomorphisms

The boundary case was proved by explicit finite-chain gluing. The algebraic
boundary lifting class and subdivision–extension adjunction give the result
for arbitrary simplicial monomorphisms.
-/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

/-- Extension preserves the algebraic boundary right lifting class. -/
theorem extension_boundary_rlp {X Y : SSet.{0}} (p : X ⟶ Y) (hp : I.rlp p) :
    I.rlp (SSet.ex.map p) := by
  have hr : (MorphismProperty.monomorphisms SSet.{0}).rlp p := by
    rwa [SSet.rlp_monomorphisms]
  intro A B i hi
  obtain ⟨n⟩ := hi
  apply (SSet.sdExAdjunction.hasLiftingProperty_iff _ _).mp
  exact hr _ (subdivision_boundary_mono n)

/-- The actual left-Kan-extension subdivision functor preserves every
simplicial monomorphism, with no semantic model-category assumption. -/
theorem subdivision_map_mono {X Y : SSet.{0}} (f : X ⟶ Y) [Mono f] :
    Mono (SSet.sd.map f) := by
  have hf : I.rlp.llp f := by
    rw [boundary_left_class]
    infer_instance
  have ht : I.rlp.llp (SSet.sd.map f) := by
    intro A B p hp
    apply (SSet.sdExAdjunction.hasLiftingProperty_iff _ _).mpr
    exact hf _ (extension_boundary_rlp p hp)
  rw [boundary_left_class] at ht
  exact ht

end Thomason.Construction

end

section

/-! # Cellular stages of the last-vertex weak equivalence -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

/-- Last vertex commutes with arbitrary simultaneous cell families. -/
theorem lastVertex_coproduct_weak {α : Type} (K : α → SSet.{0})
    (hK : ∀ a, realizationWeakEquivalences (lastVertex.app (K a))) :
    realizationWeakEquivalences (lastVertex.app (∐ K)) := by
  have hw := realization_coproduct_weak (fun a => lastVertex.app (K a)) hK
  apply realizationWeakEquivalences.of_precomp (sigmaComparison SSet.sd K) _
    (realizationWeakEquivalences.of_isIso _)
  have he : sigmaComparison SSet.sd K ≫ lastVertex.app (∐ K) =
      CategoryTheory.Limits.Sigma.map (fun a => lastVertex.app (K a)) := by
    apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, ι_comp_sigmaComparison, lastVertex.naturality, Sigma.ι_map]
    rfl
  rwa [he]

/-- Every finite-dimensional stage of the actual relative skeletal filtration
has a weak last-vertex component. No finiteness of the cell set is required. -/
theorem lastVertex_skeletonOfEmpty_weak (K : SSet.{0}) (n : ℕ) :
    realizationWeakEquivalences (lastVertex.app
      ((SSet.skeletonOfMono (⊥ : K.Subcomplex).ι n).toSSet)) := by
  let i := (⊥ : K.Subcomplex).ι
  change realizationWeakEquivalences (lastVertex.app ((SSet.skeletonOfMono i n).toSSet))
  induction n with
  | zero =>
    rw [SSet.skeletonOfMono_zero]
    have hr : SSet.Subcomplex.range i = ⊥ := Subfunctor.range_ι _
    rw [hr]
    exact lastVertex_initial_weak SSet.Subcomplex.isInitialBot
  | succ n ih =>
    let hp := (SSet.relativeCellComplexOfMono.isPushout i n).flip
    have hm : Mono (SSet.sd.map (SSet.relativeCellComplexOfMono.l i n)) :=
      subdivision_map_mono _
    exact constructedSimplicialGluingUnconditional.glue (hp.map SSet.sd) hp
      (lastVertex.app _) (lastVertex.app _) (lastVertex.app _) (lastVertex.app _)
      (lastVertex.naturality _) (lastVertex.naturality _)
      (lastVertex.naturality _) (lastVertex.naturality _)
      (lastVertex_coproduct_weak _ (fun _ => lastVertex_boundary_weak n))
      (lastVertex_coproduct_weak _ (fun _ => lastVertex_standard_weak ⦋n⦌)) ih

end

end Thomason.Construction

end

section

/-! # Subdivision and increasing simplicial exhaustions -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

noncomputable section

attribute [local instance] subdivision_map_mono

variable {K : SSet.{0}} (A : ℕ → K.Subcomplex) (hA : Monotone A)

def subcomplexExhaustionCocone : Cocone (hA.functor ⋙ SSet.Subcomplex.toSSetFunctor) where
  pt := K
  ι := { app n := (A n).ι }

def subcomplexExhaustionIsColimit (hc : iSup A = ⊤) :
    IsColimit (subcomplexExhaustionCocone A hA) :=
  IsColimit.ofIsoColimit (isColimitOfPreserves SSet.Subcomplex.toSSetFunctor
    (CompleteLattice.colimitCocone hA.functor).isColimit)
    (Cocone.ext (SSet.Subcomplex.eqToIso hc ≪≫ SSet.Subcomplex.topIso K))

def subdivisionExhaustion (n : ℕ) : (SSet.sd.obj K).Subcomplex :=
  SSet.Subcomplex.range (SSet.sd.map (A n).ι)

include hA in
theorem subdivisionExhaustion_monotone : Monotone (subdivisionExhaustion A) := by
  intro m n hmn
  have he : SSet.sd.map (SSet.Subcomplex.homOfLE (hA hmn)) ≫ SSet.sd.map (A n).ι =
      SSet.sd.map (A m).ι := by
    rw [← SSet.sd.map_comp]
    rfl
  change SSet.Subcomplex.range _ ≤ SSet.Subcomplex.range _
  rw [← he]
  exact Subfunctor.range_comp_le _ _

include hA in
theorem iSup_subdivisionExhaustion (hc : iSup A = ⊤) :
    iSup (subdivisionExhaustion A) = ⊤ := by
  apply top_unique
  intro d x _
  have hsd := isColimitOfPreserves SSet.sd (subcomplexExhaustionIsColimit A hA hc)
  have hev := isColimitOfPreserves (SSet.evaluation.obj d) hsd
  obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit hev x
  rw [Subfunctor.iSup_obj, Set.mem_iUnion]
  exact ⟨n, y, hy⟩


def subdivisionRangeIso (n : ℕ) : SSet.sd.obj (A n).toSSet ≅
    (subdivisionExhaustion A n).toSSet := by
  letI : Mono (SSet.sd.map (A n).ι) := subdivision_map_mono _
  let f := SSet.sd.map (A n).ι
  let t := SSet.Subcomplex.toRange f
  haveI : Mono t := mono_of_mono_fac (SSet.Subcomplex.toRange_ι f)
  haveI : Epi t := inferInstance
  have ht : IsIso t := isIso_of_mono_of_epi t
  exact @asIso SSet _ _ _ t ht

theorem subdivisionRangeIso_hom_ι (n : ℕ) :
    (subdivisionRangeIso A n).hom ≫ (subdivisionExhaustion A n).ι =
      SSet.sd.map (A n).ι := rfl

/-- The last-vertex map restricted to each actual subdivision image stage. -/
def lastVertexExhaustionMap (n : ℕ) :
    (subdivisionExhaustion A n).toSSet ⟶ (A n).toSSet :=
  (subdivisionRangeIso A n).inv ≫ lastVertex.app (A n).toSSet

theorem lastVertexExhaustionMap_fac (n : ℕ) :
    lastVertexExhaustionMap A n ≫ (A n).ι =
      (subdivisionExhaustion A n).ι ≫ lastVertex.app K := by
  apply (cancel_epi (subdivisionRangeIso A n).hom).mp
  calc
    _ = lastVertex.app (A n).toSSet ≫ (A n).ι := by
      simp only [lastVertexExhaustionMap, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = SSet.sd.map (A n).ι ≫ lastVertex.app K := (lastVertex.naturality _).symm
    _ = _ := by rw [← Category.assoc, subdivisionRangeIso_hom_ι]

include hA in
/-- Stagewise last-vertex weak equivalences pass to the exhausted simplicial
set, using exact compact factorization of cubes and their based homotopies. -/
theorem lastVertex_weak_of_exhaustion (hc : iSup A = ⊤)
    (hw : ∀ n, realizationWeakEquivalences (lastVertex.app (A n).toSSet)) :
    realizationWeakEquivalences (lastVertex.app K) := by
  apply RealizationPrism.exhaustion_map_weak (lastVertex.app K)
    (subdivisionExhaustion A) A (subdivisionExhaustion_monotone A hA) hA
    (lastVertexExhaustionMap A) (lastVertexExhaustionMap_fac A)
    (iSup_subdivisionExhaustion A hA hc) hc
  intro n
  have := subdivision_map_mono (A n).ι
  exact realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso _) (hw n)

end

end Thomason.Construction

end

section

/-! # The face-simplex augmentation is a weak equivalence

Explicit contractions on simplices extend over boundaries, cell
attachments and the skeletal exhaustion of the original simplicial set.
-/

namespace Thomason.Construction.FaceSimplexResolution

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

theorem augmentation_initial_weak {K : SSet.{0}} (hi : IsInitial K) :
    realizationWeakEquivalences (augmentation K) := by
  have hj := IsInitial.isInitialObj functor _ hi
  let e : functor.obj K ≅ K := hj.uniqueUpToIso hi
  have he : e.hom = augmentation K := hj.hom_ext _ _
  rw [← he]
  exact realizationWeakEquivalences.of_isIso _

theorem augmentation_face_weak {n : ℕ} (S : Finset (Fin (n+1))) :
    realizationWeakEquivalences (augmentation (SSet.stdSimplex.face S : SSet.{0})) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hs
  · apply augmentation_initial_weak
    simpa only [SSet.stdSimplex.face_empty] using
      (SSet.Subcomplex.isInitialBot (X := (Δ[n] : SSet.{0})))
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hs)
    let e := SSet.stdSimplex.isoOfRepresentableBy
      (SSet.stdSimplex.faceRepresentableBy S m (monoEquivOfFin S (by simpa using hm)))
    apply realizationWeakEquivalences.of_precomp (functor.map e.hom) _
      (realizationWeakEquivalences.of_isIso _)
    rw [augmentation_naturality e.hom]
    exact realizationWeakEquivalences.comp_mem _ _
      (augmentation_standard_weak ⦋m⦌) (realizationWeakEquivalences.of_isIso _)

theorem augmentation_union_weak {K : SSet.{0}} (A B : K.Subcomplex)
    (hI : realizationWeakEquivalences (augmentation (A ⊓ B).toSSet))
    (hA : realizationWeakEquivalences (augmentation A.toSSet))
    (hB : realizationWeakEquivalences (augmentation B.toSSet)) :
    realizationWeakEquivalences (augmentation (A ⊔ B).toSSet) := by
  have sq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  exact constructedSimplicialGluingUnconditional.glue (sq.isPushout.map functor) sq.isPushout
    (augmentation _) (augmentation _) (augmentation _) (augmentation _)
    (augmentation_naturality _) (augmentation_naturality _)
    (augmentation_naturality _) (augmentation_naturality _) hI hA hB

private theorem augmentation_faceUnion_weak_aux {n : ℕ} (k : ℕ) :
    ∀ F : Finset (Finset (Fin (n+1))), F.card = k →
      realizationWeakEquivalences (augmentation (faceUnion F : SSet)) := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro F hF
    rcases F.eq_empty_or_nonempty with rfl | hne
    · exact augmentation_initial_weak SSet.Subcomplex.isInitialBot
    · obtain ⟨S, hS⟩ := hne
      let G := F.erase S
      have hk : G.card < k := by
        rw [← hF]
        exact Finset.card_erase_lt_of_mem hS
      have hG := ih G.card hk G rfl
      let H := G.image (fun T => T ∩ S)
      have hH := ih H.card (lt_of_le_of_lt Finset.card_image_le hk) H rfl
      have hI : realizationWeakEquivalences
          (augmentation (faceUnion G ⊓ SSet.stdSimplex.face S).toSSet) := by
        rw [faceUnion_inter_face]
        exact hH
      have hfg : F = insert S G := (Finset.insert_erase hS).symm
      have hf : faceUnion F = faceUnion G ⊔ SSet.stdSimplex.face S := by
        rw [hfg]
        simp only [faceUnion, Finset.sup_insert, sup_comm]
      rw [hf]
      exact augmentation_union_weak _ _ hI hG (augmentation_face_weak S)

theorem augmentation_boundary_weak (n : ℕ) :
    realizationWeakEquivalences (augmentation (SSet.boundary.{0} n : SSet)) := by
  rw [← faceUnion_boundaryFaces]
  exact augmentation_faceUnion_weak_aux _ _ rfl

theorem augmentation_coproduct_weak {α : Type} (K : α → SSet.{0})
    (hK : ∀ a, realizationWeakEquivalences (augmentation (K a))) :
    realizationWeakEquivalences (augmentation (∐ K)) := by
  have hw := realization_coproduct_weak (fun a => augmentation (K a)) hK
  apply realizationWeakEquivalences.of_precomp (sigmaComparison functor K) _
    (realizationWeakEquivalences.of_isIso _)
  have he : sigmaComparison functor K ≫ augmentation (∐ K) =
      CategoryTheory.Limits.Sigma.map (fun a => augmentation (K a)) := by
    apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, ι_comp_sigmaComparison, augmentation_naturality, Sigma.ι_map]
  rwa [he]

theorem augmentation_skeleton_weak (K : SSet.{0}) (n : ℕ) :
    realizationWeakEquivalences (augmentation
      (SSet.skeletonOfMono (⊥ : K.Subcomplex).ι n).toSSet) := by
  let i := (⊥ : K.Subcomplex).ι
  change realizationWeakEquivalences (augmentation (SSet.skeletonOfMono i n).toSSet)
  induction n with
  | zero =>
    rw [SSet.skeletonOfMono_zero]
    have hr : SSet.Subcomplex.range i = ⊥ := Subfunctor.range_ι _
    rw [hr]
    exact augmentation_initial_weak SSet.Subcomplex.isInitialBot
  | succ n ih =>
    let hp := (SSet.relativeCellComplexOfMono.isPushout i n).flip
    exact constructedSimplicialGluingUnconditional.glue (hp.map functor) hp
      (augmentation _) (augmentation _) (augmentation _) (augmentation _)
      (augmentation_naturality _) (augmentation_naturality _)
      (augmentation_naturality _) (augmentation_naturality _)
      (augmentation_coproduct_weak _ (fun _ => augmentation_boundary_weak n))
      (augmentation_coproduct_weak _ (fun _ => augmentation_standard_weak ⦋n⦌)) ih

variable {K : SSet.{0}} (A : ℕ → K.Subcomplex) (hA : Monotone A)

def exhaustion (n : ℕ) : (functor.obj K).Subcomplex :=
  SSet.Subcomplex.range (functor.map (A n).ι)

include hA in
theorem exhaustion_monotone : Monotone (exhaustion A) := by
  intro m n hmn
  have he : functor.map (SSet.Subcomplex.homOfLE (hA hmn)) ≫ functor.map (A n).ι =
      functor.map (A m).ι := by
    rw [← functor.map_comp]
    rfl
  change SSet.Subcomplex.range _ ≤ SSet.Subcomplex.range _
  rw [← he]
  exact Subfunctor.range_comp_le _ _

include hA in
theorem iSup_exhaustion (hc : iSup A = ⊤) : iSup (exhaustion A) = ⊤ := by
  apply top_unique
  intro d x _
  have hR := isColimitOfPreserves functor (subcomplexExhaustionIsColimit A hA hc)
  have hev := isColimitOfPreserves (SSet.evaluation.obj d) hR
  obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit hev x
  rw [Subfunctor.iSup_obj, Set.mem_iUnion]
  exact ⟨n, y, hy⟩

def rangeIso (n : ℕ) : functor.obj (A n).toSSet ≅ (exhaustion A n).toSSet := by
  let f := functor.map (A n).ι
  let t := SSet.Subcomplex.toRange f
  haveI : Mono t := mono_of_mono_fac (SSet.Subcomplex.toRange_ι f)
  haveI : Epi t := inferInstance
  have ht : IsIso t := isIso_of_mono_of_epi t
  exact @asIso SSet _ _ _ t ht

theorem rangeIso_hom_ι (n : ℕ) :
    (rangeIso A n).hom ≫ (exhaustion A n).ι = functor.map (A n).ι := rfl

def exhaustionMap (n : ℕ) : (exhaustion A n).toSSet ⟶ (A n).toSSet :=
  (rangeIso A n).inv ≫ augmentation (A n).toSSet

theorem exhaustionMap_fac (n : ℕ) :
    exhaustionMap A n ≫ (A n).ι = (exhaustion A n).ι ≫ augmentation K := by
  apply (cancel_epi (rangeIso A n).hom).mp
  calc
    _ = augmentation (A n).toSSet ≫ (A n).ι := by
      simp only [exhaustionMap, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = functor.map (A n).ι ≫ augmentation K := (augmentation_naturality _).symm
    _ = _ := by rw [← Category.assoc, rangeIso_hom_ι]

include hA in
theorem augmentation_weak_of_exhaustion (hc : iSup A = ⊤)
    (hw : ∀ n, realizationWeakEquivalences (augmentation (A n).toSSet)) :
    realizationWeakEquivalences (augmentation K) := by
  apply RealizationPrism.exhaustion_map_weak (augmentation K)
    (exhaustion A) A (exhaustion_monotone A hA) hA
    (exhaustionMap A) (exhaustionMap_fac A) (iSup_exhaustion A hA hc) hc
  intro n
  exact realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso _) (hw n)

/-- An unconditional comparison for every small simplicial set,
including arbitrary singular simplicial sets. -/
theorem augmentation_weak (K : SSet.{0}) :
    realizationWeakEquivalences (augmentation K) := by
  let i := (⊥ : K.Subcomplex).ι
  exact augmentation_weak_of_exhaustion (SSet.skeletonOfMono i)
    (SSet.skeletonOfMono i).monotone (SSet.iSup_skeletonOfMono i)
    (fun n => augmentation_skeleton_weak K n)

end

end Thomason.Construction.FaceSimplexResolution

end

section

/-! # Finite relative lifts into the nonsingular resolution

The original boundary map has a specified lift through the face poset.
Weak relative realization lifting then keeps that boundary literally
fixed inside one finite nonsingular target subcomplex.
-/

namespace Thomason.Construction.FaceSimplexResolution

open CategoryTheory

noncomputable section

theorem finite_relative_resolved_lift {A B X : SSet.{0}}
    [A.Nonsingular] [B.Finite] (i : nerve A.N ⟶ B) [Mono i] (a : A ⟶ X)
    (b : SSet.toTop.obj B ⟶ SSet.toTop.obj X)
    (h : SSet.toTop.map (NonsingularLastVertex.map A ≫ a) = SSet.toTop.map i ≫ b) :
    ∃ S : (functor.obj X).Subcomplex, SSet.Finite S.toSSet ∧
      ∃ (a' : nerve A.N ⟶ S.toSSet)
        (c : SSet.toTop.obj B ⟶ SSet.toTop.obj S.toSSet),
        a' ≫ S.ι = resolvedMap a ∧
        a' ≫ S.ι ≫ augmentation X = NonsingularLastVertex.map A ≫ a ∧
        SSet.toTop.map i ≫ c = SSet.toTop.map a' ∧
        Nonempty ((c ≫ SSet.toTop.map S.ι ≫ SSet.toTop.map (augmentation X)).hom.HomotopyRel
          b.hom (Set.range (SSet.toTop.map i).hom)) := by
  have hs : SSet.toTop.map (resolvedMap a) ≫ SSet.toTop.map (augmentation X) =
      SSet.toTop.map i ≫ b := by
    rw [← SSet.toTop.map_comp, resolvedMap_augmentation]
    exact h
  obtain ⟨S, hS, a', c, ha', hc, H⟩ := finite_relative_realization_lift i
    (SSet.toTop.map (augmentation X)) (augmentation_weak X) (resolvedMap a) b hs
  refine ⟨S, hS, a', c, ha', ?_, hc, H⟩
  rw [← Category.assoc, ha', resolvedMap_augmentation]

end

end Thomason.Construction.FaceSimplexResolution

end

section

/-! # Relative passage to finite face posets

The continuous relative extension into the nonsingular resolution can be
lifted once more to an actual finite poset nerve. Naturality retains the
specified boundary as an order map, rather than only up to homotopy.
-/

namespace Thomason.Construction.NonsingularLastVertex

open CategoryTheory

noncomputable section

theorem faceMap_injective {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    Function.Injective (faceMap i (preservesNondegenerate_of_mono i)) := by
  intro x y h
  obtain ⟨n, x, rfl⟩ := x.mk_surjective
  obtain ⟨m, y, rfl⟩ := y.mk_surjective
  have hn : n = m := congrArg (fun z : B.N => z.dim) h
  subst m
  have he : i.app _ x.val = i.app _ y.val := by
    have hs := (SSet.N.ext_iff _ _).mp h
    change SSet.S.mk (i.app _ x.val) = SSet.S.mk (i.app _ y.val) at hs
    exact (SSet.S.ext_iff _ _).mp hs
  have hx : x.val = y.val := (CategoryTheory.mono_iff_injective (i.app _)).mp
    inferInstance he
  apply (SSet.N.ext_iff _ _).mpr
  change SSet.S.mk x.val = SSet.S.mk y.val
  exact (SSet.S.ext_iff _ _).mpr hx

instance faceMap_nerve_mono {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    Mono (nerveMap (faceMap i (preservesNondegenerate_of_mono i)).monotone.functor) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro s t h
  apply nerve.ext_of_isThin
  funext k
  apply faceMap_injective i
  exact congrArg (fun z => z.obj k) h

/-- Lifting through the finite face-poset comparison makes the boundary
an exact order map. Only the projection to the old target is homotopic. -/
theorem relative_facePoset_lift {A B K : SSet.{0}}
    [A.Nonsingular] [B.Nonsingular] [K.Nonsingular] [K.Finite]
    (i : A ⟶ B) [Mono i] (a : A ⟶ K) (ha : PreservesNondegenerate a)
    (b : SSet.toTop.obj B ⟶ SSet.toTop.obj K)
    (h : SSet.toTop.map i ≫ b = SSet.toTop.map a) :
    ∃ c : SSet.toTop.obj (nerve B.N) ⟶ SSet.toTop.obj (nerve K.N),
      SSet.toTop.map (nerveMap (faceMap i (preservesNondegenerate_of_mono i)).monotone.functor)
        ≫ c = SSet.toTop.map (nerveMap (faceMap a ha).monotone.functor) ∧
      Nonempty ((c ≫ SSet.toTop.map (map K)).hom.HomotopyRel
        (SSet.toTop.map (map B) ≫ b).hom
        (Set.range (SSet.toTop.map
          (nerveMap (faceMap i (preservesNondegenerate_of_mono i)).monotone.functor)).hom)) := by
  apply weak_relative_realization_lift (SSet.toTop.map (map K)) (map_weak K)
    (nerveMap (faceMap i (preservesNondegenerate_of_mono i)).monotone.functor)
    (SSet.toTop.map (nerveMap (faceMap a ha).monotone.functor))
    (SSet.toTop.map (map B) ≫ b)
  have hi := congrArg SSet.toTop.map
    (map_naturality i (preservesNondegenerate_of_mono i))
  have ha' := congrArg SSet.toTop.map (map_naturality a ha)
  simp only [SSet.toTop.map_comp] at hi ha'
  rw [ha', ← h, ← Category.assoc, ← hi, Category.assoc]

end

end Thomason.Construction.NonsingularLastVertex

namespace Thomason.Construction.FaceSimplexResolution

open CategoryTheory

noncomputable section

/-- An arbitrary original boundary map admits a continuous relative
extension into a finite poset nerve after the two specified face-poset
comparisons. The equation back in the original target is literal. -/
theorem finite_relative_order_lift {A B X : SSet.{0}}
    [A.Nonsingular] [B.Nonsingular] [B.Finite]
    (i : nerve A.N ⟶ B) [Mono i] (a : A ⟶ X)
    (b : SSet.toTop.obj B ⟶ SSet.toTop.obj X)
    (h : SSet.toTop.map (NonsingularLastVertex.map A ≫ a) = SSet.toTop.map i ≫ b) :
    ∃ (S : (functor.obj X).Subcomplex) (_ : SSet.Finite S.toSSet)
      (a' : nerve A.N ⟶ S.toSSet)
      (ha' : NonsingularLastVertex.PreservesNondegenerate a')
      (c : SSet.toTop.obj (nerve B.N) ⟶ SSet.toTop.obj (nerve S.toSSet.N)),
      a' ≫ S.ι = resolvedMap a ∧
      SSet.toTop.map (nerveMap (NonsingularLastVertex.faceMap i
        (NonsingularLastVertex.preservesNondegenerate_of_mono i)).monotone.functor) ≫ c =
        SSet.toTop.map (nerveMap (NonsingularLastVertex.faceMap a' ha').monotone.functor) ∧
      nerveMap (NonsingularLastVertex.faceMap a' ha').monotone.functor ≫
          NonsingularLastVertex.map S.toSSet ≫ S.ι ≫ augmentation X =
        NonsingularLastVertex.map (nerve A.N) ≫ NonsingularLastVertex.map A ≫ a := by
  obtain ⟨S, hS, a', c, ha', _, hc, _⟩ := finite_relative_resolved_lift i a b h
  let : SSet.Finite S.toSSet := hS
  have hnd := resolvedMap_factor_preservesNondegenerate a a' S.ι ha'
  obtain ⟨d, hd, _⟩ := NonsingularLastVertex.relative_facePoset_lift i a' hnd c hc
  refine ⟨S, hS, a', hnd, d, ha', hd, ?_⟩
  rw [← Category.assoc, ← Category.assoc, NonsingularLastVertex.map_naturality,
    Category.assoc, Category.assoc, ← Category.assoc a', ha', resolvedMap_augmentation]

end

end Thomason.Construction.FaceSimplexResolution

end

section

/-! # The relative comparison retained by finite face-poset resolution

The two relative realization lifts used by the finite order resolution
come with actual homotopies. Their composite remains stationary on the
original resolved boundary.
-/

namespace Thomason.Construction.FaceSimplexResolution

open CategoryTheory

noncomputable section

theorem finite_relative_order_lift_with_comparison {A B X : SSet.{0}}
    [A.Nonsingular] [B.Nonsingular] [B.Finite]
    (i : nerve A.N ⟶ B) [Mono i] (a : A ⟶ X)
    (b : SSet.toTop.obj B ⟶ SSet.toTop.obj X)
    (h : SSet.toTop.map (NonsingularLastVertex.map A ≫ a) = SSet.toTop.map i ≫ b) :
    ∃ (S : (functor.obj X).Subcomplex) (_ : SSet.Finite S.toSSet)
      (a' : nerve A.N ⟶ S.toSSet)
      (ha' : NonsingularLastVertex.PreservesNondegenerate a')
      (c : SSet.toTop.obj (nerve B.N) ⟶ SSet.toTop.obj (nerve S.toSSet.N)),
      a' ≫ S.ι = resolvedMap a ∧
      SSet.toTop.map (nerveMap (NonsingularLastVertex.faceMap i
        (NonsingularLastVertex.preservesNondegenerate_of_mono i)).monotone.functor) ≫ c =
        SSet.toTop.map (nerveMap (NonsingularLastVertex.faceMap a' ha').monotone.functor) ∧
      nerveMap (NonsingularLastVertex.faceMap a' ha').monotone.functor ≫
          NonsingularLastVertex.map S.toSSet ≫ S.ι ≫ augmentation X =
        NonsingularLastVertex.map (nerve A.N) ≫ NonsingularLastVertex.map A ≫ a ∧
      Nonempty ((c ≫ SSet.toTop.map (NonsingularLastVertex.map S.toSSet) ≫
          SSet.toTop.map S.ι ≫ SSet.toTop.map (augmentation X)).hom.HomotopyRel
        (SSet.toTop.map (NonsingularLastVertex.map B) ≫ b).hom
        (Set.range (SSet.toTop.map
          (nerveMap (NonsingularLastVertex.faceMap i
            (NonsingularLastVertex.preservesNondegenerate_of_mono i)).monotone.functor)).hom)) := by
  obtain ⟨S, hS, a', c, ha', _, hc, ⟨H⟩⟩ := finite_relative_resolved_lift i a b h
  let : SSet.Finite S.toSSet := hS
  have hnd := resolvedMap_factor_preservesNondegenerate a a' S.ι ha'
  obtain ⟨d, hd, ⟨G⟩⟩ := NonsingularLastVertex.relative_facePoset_lift i a' hnd c hc
  let j := nerveMap (NonsingularLastVertex.faceMap i
    (NonsingularLastVertex.preservesNondegenerate_of_mono i)).monotone.functor
  let L := SSet.toTop.map (NonsingularLastVertex.map B)
  let u := SSet.toTop.map S.ι ≫ SSet.toTop.map (augmentation X)
  have hj : j ≫ NonsingularLastVertex.map B =
      NonsingularLastVertex.map (nerve A.N) ≫ i :=
    NonsingularLastVertex.map_naturality i
      (NonsingularLastVertex.preservesNondegenerate_of_mono i)
  have himage (x : SSet.toTop.obj (nerve B.N))
      (hx : x ∈ Set.range (SSet.toTop.map j).hom) :
      L.hom x ∈ Set.range (SSet.toTop.map i).hom := by
    obtain ⟨z, rfl⟩ := hx
    refine ⟨(SSet.toTop.map (NonsingularLastVertex.map (nerve A.N))).hom z, ?_⟩
    have he := congrArg (fun q => (SSet.toTop.map q).hom z) hj
    simp only [SSet.toTop.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply] at he
    exact he.symm
  let H' : (L ≫ c ≫ u).hom.HomotopyRel (L ≫ b).hom
      (Set.range (SSet.toTop.map j).hom) := {
    toHomotopy := H.toHomotopy.comp (ContinuousMap.Homotopy.refl L.hom)
    prop' := by
      intro t x hx
      exact H.prop t _ (himage x hx) }
  let G' := G.compContinuousMap u.hom
  have hG : Nonempty ((d ≫ SSet.toTop.map (NonsingularLastVertex.map S.toSSet) ≫ u).hom.HomotopyRel
      (L ≫ c ≫ u).hom (Set.range (SSet.toTop.map j).hom)) :=
    ⟨G'.cast rfl rfl⟩
  refine ⟨S, hS, a', hnd, d, ha', hd, ?_, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, NonsingularLastVertex.map_naturality,
      Category.assoc, Category.assoc, ← Category.assoc a', ha', resolvedMap_augmentation]
  · obtain ⟨G'⟩ := hG
    exact ⟨G'.trans H'⟩

end

end Thomason.Construction.FaceSimplexResolution

end

section

/-! # Every simplicial set is the filtered union of finite subcomplexes

A stage is the union of the subcomplexes generated by a finite set of
simplices. The chosen cocone has the original simplicial set as its point.
-/

namespace Thomason.Construction.FiniteSimplicialExhaustion

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

variable (X : SSet.{0})

def support (F : Finset X.S) : X.Subcomplex :=
  ⨆ (s : F), s.val.subcomplex

instance support_finite (F : Finset X.S) : (support X F).toSSet.Finite := by
  apply (SSet.finite_iSup_iff _).mpr
  intro s
  exact inferInstanceAs (SSet.Finite (SSet.Subcomplex.ofSimplex s.val.simplex))

theorem support_monotone : Monotone (support X) := by
  intro F G hFG
  apply iSup_le
  intro s
  exact le_iSup_of_le (⟨s.val, hFG s.property⟩ : G) le_rfl

theorem iSup_support : iSup (support X) = ⊤ := by
  classical
  apply top_unique
  intro d x _
  obtain ⟨⟨n⟩⟩ := d
  let s : X.S := SSet.S.mk x
  have hs : s.subcomplex ≤ support X {s} :=
    le_iSup_of_le (⟨s, Finset.mem_singleton_self s⟩ : ({s} : Finset X.S)) le_rfl
  exact (hs.trans (le_iSup (support X) {s})) _ (SSet.Subcomplex.mem_ofSimplex_obj x)

abbrev diagram : Finset X.S ⥤ SSet.{0} :=
  (support_monotone X).functor ⋙ SSet.Subcomplex.toSSetFunctor

def cocone : Cocone (diagram X) where
  pt := X
  ι := { app F := (support X F).ι }

def isColimit : IsColimit (cocone X) :=
  IsColimit.ofIsoColimit (isColimitOfPreserves SSet.Subcomplex.toSSetFunctor
    (CompleteLattice.colimitCocone (support_monotone X).functor).isColimit)
    (Cocone.ext (SSet.Subcomplex.eqToIso (iSup_support X) ≪≫ SSet.Subcomplex.topIso X))

end

end Thomason.Construction.FiniteSimplicialExhaustion

end

section

/-! # Unconditional weak equivalence of the actual last-vertex map

The finite-chain boundary calculation, simultaneous cell attachments and
compact based-homotopy passage through the skeletal exhaustion prove the
result for every simplicial set without a weak-equivalence hypothesis.
-/

namespace Thomason.Construction

open CategoryTheory

/-- Last vertex on the actual left-Kan-extension subdivision is an actual
geometric-realization weak equivalence for every small simplicial set. -/
theorem lastVertex_weak (K : SSet.{0}) :
    realizationWeakEquivalences (lastVertex.app K) := by
  let i := (⊥ : K.Subcomplex).ι
  exact lastVertex_weak_of_exhaustion (SSet.skeletonOfMono i)
    (SSet.skeletonOfMono i).monotone (SSet.iSup_skeletonOfMono i)
    (fun n => lastVertex_skeletonOfEmpty_weak K n)

/-- Subdivision preserves and reflects the actual weak-equivalence class. -/
theorem subdivision_weak_iff {K L : SSet.{0}} (f : K ⟶ L) :
    realizationWeakEquivalences (SSet.sd.map f) ↔ realizationWeakEquivalences f :=
  sd_map_iff realizationWeakEquivalences lastVertex lastVertex_weak f

/-- The same compatibility for the double subdivision in the Thomason
adjunction. -/
theorem subdivision_twice_weak_iff {K L : SSet.{0}} (f : K ⟶ L) :
    realizationWeakEquivalences ((SSet.sd ⋙ SSet.sd).map f) ↔
      realizationWeakEquivalences f :=
  sd_twice_map_iff realizationWeakEquivalences lastVertex lastVertex_weak f

/-- Applied to an actual nerve, double subdivision detects precisely the
original weak equivalences. -/
theorem nerve_subdivision_weak_equivalences_eq {C : Type*} [Category* C]
    (N : C ⥤ SSet.{0}) :
    realizationWeakEquivalences.inverseImage (N ⋙ SSet.sd ⋙ SSet.sd) =
      realizationWeakEquivalences.inverseImage N := by
  apply MorphismProperty.ext
  intro X Y f
  exact subdivision_twice_weak_iff (N.map f)

end Thomason.Construction

end

end OAI
