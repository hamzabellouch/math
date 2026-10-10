import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.Data.Finset.Image
import Mathlib.Order.UpperLower.Basic

namespace OAI

section

/-! # Naturality of the nondegenerate face-poset comparison

A simplicial map preserving nondegenerate simplices induces a
dimension-preserving map of face posets. Uniqueness of face inclusions
makes the comparison to the original simplicial set strictly natural.
-/

namespace Thomason.Construction.NonsingularLastVertex

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

variable {X Y : SSet.{0}}

/-- The hypothesis records preservation of dimension, rather than choosing
new nondegenerate representatives of possibly degenerate images. -/
def PreservesNondegenerate (f : X ⟶ Y) : Prop :=
  ∀ (n : ℕ) (x : X _⦋n⦌), x ∈ X.nonDegenerate n →
    f.app _ x ∈ Y.nonDegenerate n

theorem preservesNondegenerate_of_mono (f : X ⟶ Y) [Mono f] :
    PreservesNondegenerate f := fun _ x hx => (SSet.nonDegenerate_iff_of_mono f x).mpr hx

def faceMap (f : X ⟶ Y) (hf : PreservesNondegenerate f) : X.N →o Y.N where
  toFun x := SSet.N.mk (f.app _ x.simplex) (hf _ _ x.nonDegenerate)
  monotone' x y h := by
    obtain ⟨u, hu, he⟩ := SSet.N.le_iff_exists_mono.mp h
    apply SSet.N.le_iff_exists_mono.mpr
    refine ⟨u, hu, ?_⟩
    change Y.map u.op (f.app _ y.simplex) = f.app _ x.simplex
    exact (f.naturality_apply u.op y.simplex).symm.trans (congrArg (f.app _) he)

@[simp]
theorem faceMap_dim (f : X ⟶ Y) (hf : PreservesNondegenerate f) (x : X.N) :
    (faceMap f hf x).dim = x.dim := rfl

@[simp]
theorem faceMap_simplex (f : X ⟶ Y) (hf : PreservesNondegenerate f) (x : X.N) :
    (faceMap f hf x).simplex = f.app _ x.simplex := rfl

variable [X.Nonsingular] [Y.Nonsingular]

/-- The same ordinal inclusion represents a face before and after the map. -/
theorem faceMap_monoOfLE (f : X ⟶ Y) (hf : PreservesNondegenerate f)
    {x y : X.N} (h : x ≤ y) :
    SSet.N.monoOfLE ((faceMap f hf).monotone h) = SSet.N.monoOfLE (X := X) h := by
  let : Mono (show SimplexCategory.mk (faceMap f hf x).dim ⟶
      SimplexCategory.mk (faceMap f hf y).dim from SSet.N.monoOfLE (X := X) h) :=
    inferInstanceAs (Mono (SSet.N.monoOfLE (X := X) h))
  apply (SSet.N.monoOfLE_eq_iff (X := Y) _ _).mpr
  change Y.map (SSet.N.monoOfLE (X := X) h).op (f.app _ y.simplex) = f.app _ x.simplex
  exact (f.naturality_apply (SSet.N.monoOfLE (X := X) h).op y.simplex).symm.trans
    (congrArg (f.app _) (SSet.N.map_monoOfLE h))

theorem faceMap_ordinal (f : X ⟶ Y) (hf : PreservesNondegenerate f)
    {n : SimplexCategory} (s : (nerve X.N).obj (.op n)) :
    ordinal (s ⋙ (faceMap f hf).monotone.functor) = ordinal s := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change (SSet.N.monoOfLE ((faceMap f hf).monotone
    (s.monotone (Fin.le_last i)))).toOrderHom (Fin.last (s.obj i).dim) = _
  rw [faceMap_monoOfLE]
  rfl

/-- Naturality has the original simplicial maps on the bottom edge. -/
@[reassoc]
theorem map_naturality (f : X ⟶ Y) (hf : PreservesNondegenerate f) :
    nerveMap (faceMap f hf).monotone.functor ≫ map Y = map X ≫ f := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  change Y.map (ordinal (s ⋙ (faceMap f hf).monotone.functor)).op
      (f.app _ (s.obj (Fin.last d.unop.len)).simplex) =
    f.app _ (X.map (ordinal s).op (s.obj (Fin.last d.unop.len)).simplex)
  rw [faceMap_ordinal]
  exact (f.naturality_apply (ordinal s).op _).symm

end

end Thomason.Construction.NonsingularLastVertex

end

section

/-! # Face resolutions preserve dimension of nondegenerate flags

A nerve flag is nondegenerate exactly when its object dimensions strictly
increase. The resolution functor leaves these dimensions unchanged,
including when the original simplicial map makes its simplices degenerate.
-/

namespace Thomason.Construction.FaceSimplexResolution

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

/-- Strictly increasing dimensions exclude every actual simplicial
 degeneracy, without assuming the face category is thin. -/
theorem nondegenerate_of_dimension_strictMono {X : SSet.{0}} {n : ℕ}
    (s : (nerve (Face X)) _⦋n⦌)
    (hs : StrictMono (fun i => dimension (s.obj i))) :
    s ∈ (nerve (Face X)).nonDegenerate n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [SSet.mem_nonDegenerate_iff_notMem_degenerate]
      intro hd
      rw [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion] at hd
      obtain ⟨i, t, rfl⟩ := hd
      have hh := hs i.castSucc_lt_succ
      change dimension (t.obj (i.predAbove i.castSucc)) <
        dimension (t.obj (i.predAbove i.succ)) at hh
      simp at hh

theorem nondegenerate_iff_dimension_strictMono {X : SSet.{0}} {n : ℕ}
    (s : (nerve (Face X)) _⦋n⦌) :
    s ∈ (nerve (Face X)).nonDegenerate n ↔
      StrictMono (fun i => dimension (s.obj i)) :=
  ⟨nondegenerate_dimension_strictMono s, nondegenerate_of_dimension_strictMono s⟩

/-- Every map of face resolutions preserves nondegenerate simplices,
even when the underlying simplicial map does not. -/
theorem map_preservesNondegenerate {X Y : SSet.{0}} (f : X ⟶ Y) :
    NonsingularLastVertex.PreservesNondegenerate (functor.map f) := by
  intro n s hs
  apply nondegenerate_of_dimension_strictMono
  exact nondegenerate_dimension_strictMono s hs

/-- The lift of nondegenerate face flags also preserves their dimensions. -/
theorem nondegenerateLift_preservesNondegenerate (X : SSet.{0}) [X.Nonsingular] :
    NonsingularLastVertex.PreservesNondegenerate (nondegenerateLift X) := by
  intro n s hs
  apply nondegenerate_of_dimension_strictMono
  have h := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mp hs
  intro i j hij
  exact SSet.N.dim_lt_of_lt (h hij)

/-- Resolving any map out of a nonsingular source retains the dimension
of every nondegenerate source flag. -/
theorem resolvedMap_preservesNondegenerate {A X : SSet.{0}} [A.Nonsingular]
    (a : A ⟶ X) : NonsingularLastVertex.PreservesNondegenerate (resolvedMap a) := by
  intro n s hs
  exact map_preservesNondegenerate a n _ (nondegenerateLift_preservesNondegenerate A n s hs)

/-- A factorization of the resolved boundary still preserves nondegenerate
simplices, independently of which finite target contains it. -/
theorem resolvedMap_factor_preservesNondegenerate {A X S : SSet.{0}} [A.Nonsingular]
    (a : A ⟶ X) (a' : nerve A.N ⟶ S) (j : S ⟶ functor.obj X)
    (h : a' ≫ j = resolvedMap a) : NonsingularLastVertex.PreservesNondegenerate a' := by
  intro n s hs
  apply SSet.nonDegenerate_of_app_apply j
  change (a' ≫ j).app _ s ∈ (functor.obj X).nonDegenerate n
  rw [h]
  exact resolvedMap_preservesNondegenerate a n s hs

/-- The actual map of face-simplex categories underlying the resolution. -/
def mapFaceFunctor {X Y : SSet.{0}} (f : X ⟶ Y) : Face X ⥤ Face Y :=
  (restriction.map f).mapElements.op

theorem mapFaceFunctor_nerveMap {X Y : SSet.{0}} (f : X ⟶ Y) :
    nerveMap (mapFaceFunctor f) = functor.map f := rfl

/-- The chosen nondegenerate face lift is natural on every map preserving
nondegenerate simplices; the bottom map is the actual face resolution. -/
theorem nondegenerateFaceFunctor_naturality {X Y : SSet.{0}}
    [X.Nonsingular] [Y.Nonsingular] (f : X ⟶ Y)
    (hf : NonsingularLastVertex.PreservesNondegenerate f) :
    (NonsingularLastVertex.faceMap f hf).monotone.functor ⋙ nondegenerateFaceFunctor Y =
      nondegenerateFaceFunctor X ⋙ mapFaceFunctor f := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun x y u => ?_)
  apply (semiProjection Y).map_injective
  apply SemiSimplexCategory.toSimplexCategory.map_injective
  change (projection Y).map (simplexMorphism
      (NonsingularLastVertex.faceMap f hf x).simplex
      (NonsingularLastVertex.faceMap f hf y).simplex
      (SSet.N.monoOfLE ((NonsingularLastVertex.faceMap f hf).monotone (leOfHom u)))
      (SSet.N.map_monoOfLE _)) =
    (𝟙 _) ≫ (projection X).map (simplexMorphism x.simplex y.simplex
      (SSet.N.monoOfLE (X := X) (leOfHom u)) (SSet.N.map_monoOfLE _)) ≫ (𝟙 _)
  rw [simplexMorphism_projection, simplexMorphism_projection]
  change SSet.N.monoOfLE ((NonsingularLastVertex.faceMap f hf).monotone (leOfHom u)) =
    (𝟙 (SimplexCategory.mk x.dim)) ≫ SSet.N.monoOfLE (X := X) (leOfHom u) ≫
      (𝟙 (SimplexCategory.mk y.dim))
  simpa only [Category.id_comp, Category.comp_id] using
    NonsingularLastVertex.faceMap_monoOfLE f hf (leOfHom u)

@[reassoc]
theorem nondegenerateLift_naturality {X Y : SSet.{0}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) (hf : NonsingularLastVertex.PreservesNondegenerate f) :
    nerveMap (NonsingularLastVertex.faceMap f hf).monotone.functor ≫
        nondegenerateLift Y = nondegenerateLift X ≫ functor.map f := by
  change nerveMap (NonsingularLastVertex.faceMap f hf).monotone.functor ≫
      nerveMap (nondegenerateFaceFunctor Y) =
    nerveMap (nondegenerateFaceFunctor X) ≫ nerveMap (mapFaceFunctor f)
  have he := congrArg nerveMap (nondegenerateFaceFunctor_naturality f hf)
  exact he

end

end Thomason.Construction.FaceSimplexResolution

end

section

/-!
# Sieve retractions and the local contraction in the Thomason argument

The order-theoretic construction of Section 5, Lemma `greatest-new`, of
*Thomason Model Structures in Every Strict Higher Dimension* supplies finite
retraction-stable supports for the passage from finite to arbitrary posets.
-/

namespace Thomason.Construction

universe u

variable {E : Type u} [PartialOrder E]

/-- A downward-closed full subposet whose inclusion has a right adjoint. -/
structure SieveRetraction (A : Set E) where
  lower : IsLowerSet A
  rightAdjoint : E →o A
  adjunction : ∀ (a : A) (e : E), (a : E) ≤ e ↔ a ≤ rightAdjoint e

namespace SieveRetraction

variable {A : Set E} (R : SieveRetraction A)

theorem rightAdjoint_le (e : E) : (R.rightAdjoint e : E) ≤ e :=
  (R.adjunction (R.rightAdjoint e) e).mpr le_rfl

@[simp]
theorem rightAdjoint_coe (a : A) : R.rightAdjoint a = a := by
  apply le_antisymm
  · exact R.rightAdjoint_le a
  · exact (R.adjunction a a).mp le_rfl

/-- The associated idempotent endomorphism of the ambient poset. -/
def projection : E →o E :=
  { toFun := fun e => R.rightAdjoint e
    monotone' := fun _ _ h => R.rightAdjoint.monotone h }

@[simp]
theorem projection_apply (e : E) : R.projection e = (R.rightAdjoint e : E) := rfl

theorem projection_mem (e : E) : R.projection e ∈ A := (R.rightAdjoint e).property

@[simp]
theorem projection_of_mem {e : E} (he : e ∈ A) : R.projection e = e :=
  congrArg Subtype.val (R.rightAdjoint_coe ⟨e, he⟩)

@[simp]
theorem projection_idempotent (e : E) : R.projection (R.projection e) = R.projection e :=
  R.projection_of_mem (R.projection_mem e)

/-- A greatest element of the new part of the poset. It need not be greatest
in the whole poset: old objects can lie above neither it nor the new part. -/
structure GreatestNew (x : E) : Prop where
  not_mem : x ∉ A
  greatest : ∀ e, e ∉ A → e ≤ x

variable {x : E} (hx : GreatestNew (A := A) x)

include hx in
theorem old_le_retracted_greatest {a e : E}
    (ha : a ∈ A) (he : e ∉ A) (hae : a ≤ e) :
    a ≤ R.projection x :=
  (R.adjunction ⟨a, ha⟩ x).mp (hae.trans (hx.greatest e he))

/-- Fix the old subposet and send every new element to a fixed value. -/
noncomputable def replaceNew (c : E)
    (hc : ∀ a e, a ∈ A → e ∉ A → a ≤ e → a ≤ c) : E →o E := by
  classical
  refine ⟨fun e => if e ∈ A then e else c, ?_⟩
  intro a b hab
  by_cases ha : a ∈ A
  · by_cases hb : b ∈ A
    · simpa only [ite_eq_left ha, ite_eq_left hb] using hab
    · simpa only [ite_eq_left ha, ite_eq_right hb] using hc a b ha hb hab
  · have hb : b ∉ A := fun hb => ha (R.lower hab hb)
    simp only [ite_eq_right ha, ite_eq_right hb, le_refl]

@[simp]
theorem replaceNew_old (c : E) (hc) {a : E} (ha : a ∈ A) :
    R.replaceNew c hc a = a := by
  classical
  change (if a ∈ A then a else c) = a
  simp only [ite_eq_left ha]

@[simp]
theorem replaceNew_new (c : E) (hc) {e : E} (he : e ∉ A) :
    R.replaceNew c hc e = c := by
  classical
  change (if e ∈ A then e else c) = c
  simp only [ite_eq_right he]

/-- The common upper endpoint `g` in the local zigzag. -/
noncomputable def upperCollapse : E →o E :=
  R.replaceNew x (fun _ e _ he hae => hae.trans (hx.greatest e he))

/-- The old-valued endpoint `k` in the local zigzag. -/
noncomputable def oldCollapse : E →o E :=
  R.replaceNew (R.projection x)
    (fun _ _ ha he hae => R.old_le_retracted_greatest hx ha he hae)

theorem identity_le_upperCollapse (e : E) : e ≤ R.upperCollapse hx e := by
  classical
  by_cases he : e ∈ A
  · simp [upperCollapse, he]
  · simpa [upperCollapse, he] using hx.greatest e he

theorem oldCollapse_le_upperCollapse (e : E) :
    R.oldCollapse hx e ≤ R.upperCollapse hx e := by
  classical
  by_cases he : e ∈ A
  · simp [oldCollapse, upperCollapse, he]
  · simpa [oldCollapse, upperCollapse, he] using R.rightAdjoint_le x

theorem upperCollapse_old {a : E} (ha : a ∈ A) : R.upperCollapse hx a = a :=
  R.replaceNew_old _ _ ha

theorem oldCollapse_old {a : E} (ha : a ∈ A) : R.oldCollapse hx a = a :=
  R.replaceNew_old _ _ ha

theorem upperCollapse_new {e : E} (he : e ∉ A) : R.upperCollapse hx e = x :=
  R.replaceNew_new _ _ he

theorem oldCollapse_mem (e : E) : R.oldCollapse hx e ∈ A := by
  classical
  by_cases he : e ∈ A
  · simp [oldCollapse, he]
  · simp [oldCollapse, he]

/-- The endpoint `k` factors through the old subposet as a retraction. -/
noncomputable def oldCollapseRetraction : E →o A :=
  { toFun := fun e => ⟨R.oldCollapse hx e, R.oldCollapse_mem hx e⟩
    monotone' := fun _ _ h => (R.oldCollapse hx).monotone h }

@[simp]
theorem oldCollapseRetraction_coe (a : A) : R.oldCollapseRetraction hx a = a := by
  apply Subtype.ext
  exact R.oldCollapse_old hx a.property

/-- The exact order-theoretic hypotheses of the two relative prisms in
Lemma `greatest-new`: `id ≤ g ≥ k`, fixed on the old part, with `g`
constant on the new part and `k` factoring through a retraction to the old part. -/
theorem local_zigzag :
    (∀ e, e ≤ R.upperCollapse hx e) ∧
    (∀ e, R.oldCollapse hx e ≤ R.upperCollapse hx e) ∧
    (∀ a, a ∈ A → R.upperCollapse hx a = a ∧ R.oldCollapse hx a = a) ∧
    (∀ e, e ∉ A → R.upperCollapse hx e = x) ∧
    (∀ a : A, R.oldCollapseRetraction hx a = a) :=
  ⟨R.identity_le_upperCollapse hx, R.oldCollapse_le_upperCollapse hx,
    fun _ ha => ⟨R.upperCollapse_old hx ha, R.oldCollapse_old hx ha⟩,
    fun _ he => R.upperCollapse_new hx he, R.oldCollapseRetraction_coe hx⟩

section FiniteSupports

variable [DecidableEq E]

/-- Add retraction images once; idempotence makes this stable already. -/
def stableClosure (s : Finset E) : Finset E := s ∪ s.image R.projection

theorem subset_stableClosure (s : Finset E) : s ⊆ R.stableClosure s :=
  Finset.subset_union_left

theorem stableClosure_stable (s : Finset E) {e : E} (he : e ∈ R.stableClosure s) :
    R.projection e ∈ R.stableClosure s := by
  rcases Finset.mem_union.mp he with he | he
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    rw [R.projection_idempotent]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

def Stable (s : Finset E) : Prop := ∀ e ∈ s, R.projection e ∈ s

theorem stable_union {s t : Finset E} (hs : R.Stable s) (ht : R.Stable t) :
    R.Stable (s ∪ t) := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact Finset.mem_union_left _ (hs e he)
  · exact Finset.mem_union_right _ (ht e he)

/-- Every finite subset lies in a finite retraction-stable full subposet. -/
theorem finite_stable_superset (s : Finset E) :
    ∃ t : Finset E, s ⊆ t ∧ R.Stable t :=
  ⟨R.stableClosure s, R.subset_stableClosure s,
    fun _ he => R.stableClosure_stable s he⟩

/-- The stable finite supports form a directed system under inclusion. -/
theorem stable_directed (s t : Finset E) (hs : R.Stable s) (ht : R.Stable t) :
    ∃ q : Finset E, R.Stable q ∧ s ⊆ q ∧ t ⊆ q :=
  ⟨s ∪ t, R.stable_union hs ht, Finset.subset_union_left, Finset.subset_union_right⟩

/-- Restrict to a stable finite full subposet. It need not be a sieve in `E`. -/
def restrictToStable (s : Finset E) (hs : R.Stable s) :
    SieveRetraction {e : {e : E // e ∈ s} | (e : E) ∈ A} where
  lower := by
    intro a b hab hb
    exact R.lower hab hb
  rightAdjoint :=
    { toFun := fun e =>
        ⟨⟨R.projection e, hs e e.property⟩, R.projection_mem e⟩
      monotone' := fun _ _ h => R.projection.monotone h }
  adjunction a e := R.adjunction ⟨a.val.val, a.property⟩ e

end FiniteSupports

end SieveRetraction
end Thomason.Construction

end

section

/-! # Descending compatible simplicial prisms from standard simplices -/

namespace Thomason.Construction.SimplicialHomotopyDescent

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

noncomputable section

variable (F : SSet.{0} ⥤ SSet.{0}) [hF : F.IsLeftAdjoint] (K : SSet.{0})

abbrev diagram := CostructuredArrow.proj SSet.stdSimplex K ⋙ SSet.stdSimplex ⋙ F

abbrev cocone : Cocone (diagram F K) :=
  F.mapCocone (Presheaf.tautologicalCocone' K)

def isColimit : IsColimit (cocone F K) := by
  let hP : PreservesColimit
      (CostructuredArrow.proj (uliftYoneda.{0}) K ⋙ uliftYoneda.{0}) F :=
    (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
  exact (hP.preserves (Presheaf.isColimitTautologicalCocone' K)).some

def prismCocone (Y : SSet.{0})
    (P : ∀ j : CostructuredArrow SSet.stdSimplex K, F.obj (SSet.stdSimplex.obj j.left) ⊗ Δ[1] ⟶ Y)
    (hp : ∀ {i j : CostructuredArrow SSet.stdSimplex K} (a : i ⟶ j),
      F.map (SSet.stdSimplex.map a.left) ▷ Δ[1] ≫ P j = P i) :
    Cocone (diagram F K ⋙ tensorRight (Δ[1] : SSet.{0})) where
  pt := Y
  ι := {
    app := P
    naturality := fun i j a => by
      exact (hp a).trans (Category.comp_id _).symm }

def assemble (Y : SSet.{0})
    (P : ∀ j : CostructuredArrow SSet.stdSimplex K, F.obj (SSet.stdSimplex.obj j.left) ⊗ Δ[1] ⟶ Y)
    (hp : ∀ {i j : CostructuredArrow SSet.stdSimplex K} (a : i ⟶ j),
      F.map (SSet.stdSimplex.map a.left) ▷ Δ[1] ≫ P j = P i) :
    F.obj K ⊗ Δ[1] ⟶ Y :=
  (isColimitOfPreserves (tensorRight (Δ[1] : SSet.{0})) (isColimit F K)).desc
    (prismCocone F K Y P hp)

@[reassoc]
theorem assemble_fac (Y : SSet.{0})
    (P : ∀ j : CostructuredArrow SSet.stdSimplex K, F.obj (SSet.stdSimplex.obj j.left) ⊗ Δ[1] ⟶ Y)
    (hp : ∀ {i j : CostructuredArrow SSet.stdSimplex K} (a : i ⟶ j),
      F.map (SSet.stdSimplex.map a.left) ▷ Δ[1] ≫ P j = P i)
    (j : CostructuredArrow SSet.stdSimplex K) :
    F.map j.hom ▷ Δ[1] ≫ assemble F K Y P hp = P j :=
  (isColimitOfPreserves (tensorRight (Δ[1] : SSet.{0})) (isColimit F K)).fac
    (prismCocone F K Y P hp) j

def homotopy (Y : SSet.{0})
    (P : ∀ j : CostructuredArrow SSet.stdSimplex K, F.obj (SSet.stdSimplex.obj j.left) ⊗ Δ[1] ⟶ Y)
    (hp : ∀ {i j : CostructuredArrow SSet.stdSimplex K} (a : i ⟶ j),
      F.map (SSet.stdSimplex.map a.left) ▷ Δ[1] ≫ P j = P i)
    (f g : F.obj K ⟶ Y)
    (h₀ : ∀ j, SSet.ι₀ ≫ P j = F.map j.hom ≫ f)
    (h₁ : ∀ j, SSet.ι₁ ≫ P j = F.map j.hom ≫ g) : SSet.Homotopy f g where
  h := assemble F K Y P hp
  h₀ := by
    change SSet.ι₀ ≫ assemble F K Y P hp = f
    apply (isColimit F K).hom_ext
    intro j
    change F.map j.hom ≫ (SSet.ι₀ ≫ assemble F K Y P hp) = F.map j.hom ≫ f
    rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, assemble_fac, h₀]
  h₁ := by
    change SSet.ι₁ ≫ assemble F K Y P hp = g
    apply (isColimit F K).hom_ext
    intro j
    change F.map j.hom ≫ (SSet.ι₁ ≫ assemble F K Y P hp) = F.map j.hom ≫ g
    rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, assemble_fac, h₁]
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end

end Thomason.Construction.SimplicialHomotopyDescent

end

section

/-!
# Weak equivalences and twice extended nerves

The two-out-of-three argument is from the beginning of Section 7 of
*Thomason Model Structures in Every Strict Higher Dimension*.
The simplicial subdivision and extension functors are Mathlib's actual functors.

The published input for extension is the natural weak equivalence
`j : 𝟭 SSet ⟶ SSet.ex` (Goerss--Jardine, *Simplicial Homotopy Theory*,
Theorem III.4.6). The corresponding input for subdivision is the last-vertex
natural weak equivalence `SSet.sd ⟶ 𝟭 SSet` (Ara--Maltsiniotis, *Vers une
structure de catégorie de modèles à la Thomason sur la catégorie des
n-catégories strictes*, Theorem 4.5, arXiv:1305.5086v3).

These are explicit hypotheses on the simplicial morphism property.
-/

open CategoryTheory

namespace Thomason.Construction

universe v u

section Transport

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasTwoOutOfThreeProperty]
variable (F : C ⥤ C)

/-- Naturality of an objectwise weak equivalence from the identity proves
that its target endofunctor preserves and reflects weak equivalences. -/
theorem map_iff_of_weak_coaugmentation (j : 𝟭 C ⟶ F)
    (hj : ∀ X, W (j.app X)) {X Y : C} (f : X ⟶ Y) :
    W (F.map f) ↔ W f := by
  have hnat : f ≫ j.app Y = j.app X ≫ F.map f := j.naturality f
  constructor
  · intro hf
    apply W.of_postcomp f (j.app Y) (hj Y)
    rw [hnat]
    exact W.comp_mem _ _ (hj X) hf
  · intro hf
    apply W.of_precomp (j.app X) (F.map f) (hj X)
    rw [← hnat]
    exact W.comp_mem _ _ hf (hj Y)

/-- The analogous argument for a weak equivalence to the identity. -/
theorem map_iff_of_weak_augmentation (e : F ⟶ 𝟭 C)
    (he : ∀ X, W (e.app X)) {X Y : C} (f : X ⟶ Y) :
    W (F.map f) ↔ W f := by
  have hnat : F.map f ≫ e.app Y = e.app X ≫ f := e.naturality f
  constructor
  · intro hf
    apply W.of_precomp (e.app X) f (he X)
    rw [← hnat]
    exact W.comp_mem _ _ hf (he Y)
  · intro hf
    apply W.of_postcomp (F.map f) (e.app Y) (he Y)
    rw [hnat]
    exact W.comp_mem _ _ (he X) hf

end Transport

section Simplicial

variable (W : MorphismProperty SSet.{u}) [W.HasTwoOutOfThreeProperty]

/-- The mate of a last-vertex transformation under the actual subdivision
adjunction. Its components are the canonical maps to extension; their being
weak equivalences remains a separate published input. -/
noncomputable def extensionCoaugmentation
    (e : SSet.sd.{u} ⟶ 𝟭 SSet.{u}) : 𝟭 SSet.{u} ⟶ SSet.ex where
  app X := SSet.sdExAdjunction.homEquiv X X (e.app X)
  naturality X Y f := by
    exact SSet.sdExAdjunction.homEquiv_naturality_left_square
      f (e.app Y) (e.app X) f (e.naturality f)

/-- The canonical extension map, obtained from the actual last-vertex map. -/
noncomputable def canonicalExtension : 𝟭 SSet.{u} ⟶ SSet.ex :=
  extensionCoaugmentation lastVertex

/-- Taking mates identifies the two canonical extension transformations. -/
theorem canonicalExtension_eq :
    canonicalExtension.{u} = Thomason.Subdivision.exComparison := by
  apply NatTrans.ext
  funext X
  change SSet.sdExAdjunction.homEquiv X X (lastVertex.app X) =
    SSet.sdExAdjunction.homEquiv X X (Thomason.Subdivision.lastVertex.app X)
  rw [lastVertex_eq]

/-- Goerss--Jardine III.4.6 implies that `Ex` preserves and reflects `W`. -/
theorem ex_map_iff (j : 𝟭 SSet.{u} ⟶ SSet.ex) (hj : ∀ X, W (j.app X))
    {X Y : SSet.{u}} (f : X ⟶ Y) : W (SSet.ex.map f) ↔ W f :=
  map_iff_of_weak_coaugmentation W SSet.ex j hj f

/-- The last-vertex weak equivalence implies the analogous statement for `Sd`. -/
theorem sd_map_iff (e : SSet.sd.{u} ⟶ 𝟭 SSet.{u}) (he : ∀ X, W (e.app X))
    {X Y : SSet.{u}} (f : X ⟶ Y) : W (SSet.sd.map f) ↔ W f :=
  map_iff_of_weak_augmentation W SSet.sd e he f

/-- In particular two extensions do not change the detected weak equivalences. -/
theorem ex_twice_map_iff (j : 𝟭 SSet.{u} ⟶ SSet.ex) (hj : ∀ X, W (j.app X))
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    W ((SSet.ex ⋙ SSet.ex).map f) ↔ W f :=
  (ex_map_iff W j hj (SSet.ex.map f)).trans (ex_map_iff W j hj f)

/-- Likewise two subdivisions preserve and reflect weak equivalences. -/
theorem sd_twice_map_iff (e : SSet.sd.{u} ⟶ 𝟭 SSet.{u}) (he : ∀ X, W (e.app X))
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    W ((SSet.sd ⋙ SSet.sd).map f) ↔ W f :=
  (sd_map_iff W e he (SSet.sd.map f)).trans (sd_map_iff W e he f)

variable {D : Type*} [Category* D]

/-- The equality `N⁻¹ W = (Ex² N)⁻¹ W` used to prescribe the Thomason
weak equivalences. This applies to any actual nerve functor `N`. -/
theorem nerve_weak_equivalences_eq (N : D ⥤ SSet.{u})
    (j : 𝟭 SSet.{u} ⟶ SSet.ex) (hj : ∀ X, W (j.app X)) :
    W.inverseImage N = W.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) := by
  apply MorphismProperty.ext
  intro X Y f
  exact (ex_twice_map_iff W j hj (N.map f)).symm

/-- The same weak-equivalence identification with the extension map explicitly
constructed as the mate of the last-vertex map. -/
theorem nerve_weak_equivalences_eq_of_last_vertex (N : D ⥤ SSet.{u})
    (e : SSet.sd.{u} ⟶ 𝟭 SSet.{u})
    (hj : ∀ X, W ((extensionCoaugmentation e).app X)) :
    W.inverseImage N = W.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) :=
  nerve_weak_equivalences_eq W N (extensionCoaugmentation e) hj

/-- The precise specialization used for the Thomason model classes. The only
subdivision/extension input is the published weak-equivalence property of the
canonical map to `Ex`. -/
theorem canonical_nerve_weak_equivalences_eq (N : D ⥤ SSet.{u})
    (hj : ∀ X, W (canonicalExtension.app X)) :
    W.inverseImage N = W.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) :=
  nerve_weak_equivalences_eq W N canonicalExtension hj

/-- The mate identity used in the Quillen-equivalence argument. -/
theorem canonicalExtension_fac (X : SSet.{u}) :
    canonicalExtension.app X = SSet.sdExAdjunction.unit.app X ≫
      SSet.ex.map (lastVertex.app X) :=
  SSet.sdExAdjunction.homEquiv_unit X X (lastVertex.app X)

/-- The published weak-equivalence properties of last vertex and extension
imply that the unit of subdivision-extension is a weak equivalence. -/
theorem subdivision_unit_weak_equivalence
    (he : ∀ X, W (lastVertex.app X))
    (hj : ∀ X, W (canonicalExtension.app X)) (X : SSet.{u}) :
    W (SSet.sdExAdjunction.unit.app X) := by
  apply W.of_postcomp _ (SSet.ex.map (lastVertex.app X))
    ((ex_map_iff W canonicalExtension hj _).mpr (he X))
  rw [← canonicalExtension_fac]
  exact hj X

/-- The unit for two subdivisions and two extensions is also a weak equivalence. -/
theorem subdivision_twice_unit_weak_equivalence
    (he : ∀ X, W (lastVertex.app X))
    (hj : ∀ X, W (canonicalExtension.app X)) (X : SSet.{u}) :
    W ((SSet.sdExAdjunction.comp SSet.sdExAdjunction).unit.app X) := by
  rw [Adjunction.comp_unit_app]
  exact W.comp_mem _ _ (subdivision_unit_weak_equivalence W he hj X)
    ((ex_map_iff W canonicalExtension hj _).mpr
      (subdivision_unit_weak_equivalence W he hj (SSet.sd.obj X)))

end Simplicial

section Adjunct

variable {C D : Type*} [Category* C] [Category* D]
variable (W : MorphismProperty C) [W.HasTwoOutOfThreeProperty]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- The weak-equivalence calculation underlying the Quillen-equivalence
criterion: if the unit is weak, an adjunct is weak exactly when its image
under the right adjoint is weak. -/
theorem adjunct_weak_equivalence_iff (hu : ∀ X, W (adj.unit.app X))
    {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    W (adj.homEquiv X Y f) ↔ W (R.map f) := by
  rw [adj.homEquiv_unit]
  exact ⟨W.of_precomp _ _ (hu X), W.comp_mem _ _ (hu X)⟩

end Adjunct

end Thomason.Construction

end

section

/-! # Injectivity of the actual canonical extension

The last-vertex map on each standard simplex has an explicit section: a
vertex is sent to its initial segment. Taking mates therefore embeds every
simplicial set into its actual extension. No weak-equivalence premise is used.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder

universe u

noncomputable section

/-- The initial segment ending at a vertex of a finite ordered simplex. -/
def initialVertexChain {n : ℕ} (i : ULift.{u} (Fin (n + 1))) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) where
  finset := Finset.univ.filter (· ≤ i)
  nonempty := ⟨i, by simp⟩
  comparable _ _ := le_total _ _

theorem initialVertexChain_monotone {n : ℕ} :
    Monotone (initialVertexChain.{u} (n := n)) := by
  intro i j hij x hx
  simp only [initialVertexChain, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.trans hij

/-- Initial segments form a monotone section of the maximum operation. -/
def initialVertexChainHom (n : ℕ) : ULift.{u} (Fin (n + 1)) →o
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) :=
  ⟨initialVertexChain, initialVertexChain_monotone⟩

theorem chainMaximum_initialVertexChain {n : ℕ} (i : ULift.{u} (Fin (n + 1))) :
    chainMaximum (initialVertexChain i) = i := by
  apply le_antisymm
  · apply Finset.max'_le
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  · exact Finset.le_max' _ _ (by simp [initialVertexChain])

/-- A degreewise section, not claimed to be natural in the ordinal. -/
def simplexInitialVertexChain (n : SimplexCategory) :
    SimplexCategory.toPartOrd.{u}.obj n ⟶
      (SimplexCategory.toPartOrd.{u} ⋙ PartOrd.nonemptyFiniteChainsFunctor).obj n :=
  PartOrd.ofHom (initialVertexChainHom n.len)

theorem simplexInitialVertexChain_fac (n : SimplexCategory) :
    simplexInitialVertexChain.{u} n ≫ simplexChainMaximum.app n = 𝟙 _ := by
  apply PartOrd.ext
  intro i
  exact chainMaximum_initialVertexChain i

/-- The section on the nerve of each ordinal. -/
def simplexLastVertexSection (n : SimplexCategory) :
    SSet.stdSimplex.{u}.obj n ⟶ SimplexCategory.sd.obj n :=
  simplexNerveIso.hom.app n ≫
    PartOrd.nerveFunctor.map (simplexInitialVertexChain n)

theorem simplexLastVertexSection_fac (n : SimplexCategory) :
    simplexLastVertexSection.{u} n ≫ simplexLastVertex.app n = 𝟙 _ := by
  have h := simplexInitialVertexChain_fac.{u} n
  calc
    _ = simplexNerveIso.hom.app n ≫
        PartOrd.nerveFunctor.map (simplexInitialVertexChain n ≫
          simplexChainMaximum.app n) ≫ simplexNerveIso.inv.app n := by
      change (simplexNerveIso.hom.app n ≫
        PartOrd.nerveFunctor.map (simplexInitialVertexChain n)) ≫
          (PartOrd.nerveFunctor.map (simplexChainMaximum.app n) ≫
            simplexNerveIso.inv.app n) = _
      rw [Functor.map_comp, Category.assoc, Category.assoc]
    _ = _ := by
      rw [h, CategoryTheory.Functor.map_id]
      exact (congrArg (fun k => simplexNerveIso.hom.app n ≫ k)
        (Category.id_comp (simplexNerveIso.inv.app n))).trans
          (simplexNerveIso.hom_inv_id_app n)

/-- Last vertex is split surjective on every standard simplex. -/
def lastVertexStandardSection (n : SimplexCategory) :
    SSet.stdSimplex.{u}.obj n ⟶ SSet.sd.obj (SSet.stdSimplex.obj n) :=
  simplexLastVertexSection n ≫ SSet.stdSimplex.sdIso.inv.app n

theorem lastVertexStandardSection_fac (n : SimplexCategory) :
    lastVertexStandardSection.{u} n ≫ lastVertex.app (SSet.stdSimplex.obj n) = 𝟙 _ := by
  rw [lastVertexStandardSection, Category.assoc, lastVertex_on_standard_simplex,
    simplexLastVertexSection_fac]

theorem lastVertex_standard_epi (n : SimplexCategory) :
    Epi (lastVertex.{u}.app (SSet.stdSimplex.obj n)) := by
  apply epi_of_epi_fac (lastVertexStandardSection_fac n)

/-- The adjoint of `j_X` after a standard simplex is precisely the
last-vertex map followed by that simplex. -/
theorem canonicalExtension_simplex (X : SSet.{u}) (n : SimplexCategory)
    (f : SSet.stdSimplex.obj n ⟶ X) :
    f ≫ canonicalExtension.app X = SSet.sdExAdjunction.homEquiv _ _
      (lastVertex.app (SSet.stdSimplex.obj n) ≫ f) := by
  have he : SSet.sd.map f ≫ lastVertex.app X =
      lastVertex.app (SSet.stdSimplex.obj n) ≫ f := lastVertex.naturality f
  calc
    _ = SSet.sdExAdjunction.homEquiv _ _ (SSet.sd.map f ≫ lastVertex.app X) :=
      (SSet.sdExAdjunction.homEquiv_naturality_left f (lastVertex.app X)).symm
    _ = _ := congrArg (SSet.sdExAdjunction.homEquiv _ _) he

/-- The canonical extension map is an actual monomorphism in every degree. -/
theorem canonicalExtension_mono (X : SSet.{u}) : Mono (canonicalExtension.app X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y hxy
  have h : (SSet.yonedaEquiv.symm x : SSet.stdSimplex.obj n.unop ⟶ X) ≫
      canonicalExtension.app X = SSet.yonedaEquiv.symm y ≫ canonicalExtension.app X := by
    simpa only [SSet.yonedaEquiv_symm_comp] using congrArg SSet.yonedaEquiv.symm hxy
  have h' := (canonicalExtension_simplex X n.unop (SSet.yonedaEquiv.symm x)).symm.trans
    (h.trans (canonicalExtension_simplex X n.unop (SSet.yonedaEquiv.symm y)))
  have hs := (SSet.sdExAdjunction.homEquiv _ _).injective h'
  have := lastVertex_standard_epi.{u} n.unop
  have hfg : SSet.yonedaEquiv.symm x = SSet.yonedaEquiv.symm y :=
    (cancel_epi (lastVertex.app (SSet.stdSimplex.obj n.unop))).mp hs
  exact SSet.yonedaEquiv.symm.injective hfg

end

end Thomason.Construction

end

section

/-! # The canonical extension is cartesian over subobjects

The last-vertex map of a standard simplex has a section. Its adjoint
therefore creates no new preimages of any original subcomplex.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

/-- A simplex of an extension lying over an original simplex has a unique
original lift along a monomorphism. -/
theorem canonicalExtension_simplex_lift {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (n : SimplexCategory) (x : SSet.stdSimplex.obj n ⟶ B)
    (a : SSet.stdSimplex.obj n ⟶ SSet.ex.obj A)
    (h : x ≫ canonicalExtension.app B = a ≫ SSet.ex.map i) :
    ∃ b : SSet.stdSimplex.obj n ⟶ A,
      b ≫ i = x ∧ b ≫ canonicalExtension.app A = a := by
  let f := (SSet.sdExAdjunction.homEquiv (SSet.stdSimplex.obj n) A).symm a
  have hf : SSet.sdExAdjunction.homEquiv _ _ f = a :=
    (SSet.sdExAdjunction.homEquiv _ _).apply_symm_apply a
  have he : lastVertex.app (SSet.stdSimplex.obj n) ≫ x = f ≫ i := by
    apply (SSet.sdExAdjunction.homEquiv _ _).injective
    calc
      _ = x ≫ canonicalExtension.app B := (canonicalExtension_simplex B n x).symm
      _ = a ≫ SSet.ex.map i := h
      _ = SSet.sdExAdjunction.homEquiv _ _ (f ≫ i) := by
        rw [SSet.sdExAdjunction.homEquiv_naturality_right, hf]
  let b := lastVertexStandardSection n ≫ f
  have hb : b ≫ i = x := by
    calc
      _ = lastVertexStandardSection n ≫ (f ≫ i) := Category.assoc _ _ _
      _ = lastVertexStandardSection n ≫
          (lastVertex.app (SSet.stdSimplex.obj n) ≫ x) := congrArg (_ ≫ ·) he.symm
      _ = x := by rw [← Category.assoc, lastVertexStandardSection_fac, Category.id_comp]
  refine ⟨b, hb, ?_⟩
  apply (cancel_mono (SSet.ex.map i)).mp
  calc
    _ = b ≫ (i ≫ canonicalExtension.app B) := by
      rw [Category.assoc, ← canonicalExtension.naturality]
      rfl
    _ = x ≫ canonicalExtension.app B := by rw [← Category.assoc, hb]
    _ = _ := h

/-- Naturality of the actual canonical extension is a pullback along every
monomorphism of simplicial sets. -/
theorem canonicalExtension_isPullback {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    IsPullback i (canonicalExtension.app A) (canonicalExtension.app B) (SSet.ex.map i) := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  rw [Types.isPullback_iff]
  refine ⟨NatTrans.congr_app (canonicalExtension.naturality i) n, ?_, ?_⟩
  · intro x y h
    exact (injective_of_mono (i.app n)) h.1
  · intro x a h
    have he : (SSet.yonedaEquiv.symm x : SSet.stdSimplex.obj n.unop ⟶ B) ≫
        canonicalExtension.app B = SSet.yonedaEquiv.symm a ≫ SSet.ex.map i := by
      simpa only [SSet.yonedaEquiv_symm_comp] using congrArg SSet.yonedaEquiv.symm h
    obtain ⟨b, hb, ha⟩ := canonicalExtension_simplex_lift i n.unop _ _ he
    refine ⟨SSet.yonedaEquiv b, ?_, ?_⟩
    · simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
        congrArg SSet.yonedaEquiv hb
    · simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
        congrArg SSet.yonedaEquiv ha

/-- A pullback square identifies the preimage of the bottom map's range
with the range of its top map. -/
theorem preimage_range_of_isPullback {W X Y Z : SSet.{u}}
    {t : W ⟶ X} {l : W ⟶ Y} {r : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback t l r b) :
    (SSet.Subcomplex.range b).preimage r = SSet.Subcomplex.range t := by
  apply Subfunctor.ext
  funext n
  ext x
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb, _⟩ := Types.exists_of_isPullback
      (h.app n) x a ha.symm
    exact ⟨b, hb⟩
  · rintro ⟨a, rfl⟩
    refine ⟨l.app n a, ?_⟩
    exact (ConcreteCategory.congr_hom (h.app n).w a).symm

/-- A simplex of `B` enters the extension of a subobject precisely when it
already lies in that subobject. -/
theorem canonicalExtension_preimage_range {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    (SSet.Subcomplex.range (SSet.ex.map i)).preimage (canonicalExtension.app B) =
      SSet.Subcomplex.range i :=
  preimage_range_of_isPullback (canonicalExtension_isPullback i)

end

end Thomason.Construction

end

end OAI
