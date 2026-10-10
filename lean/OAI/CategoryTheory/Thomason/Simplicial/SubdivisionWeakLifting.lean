import OAI.CategoryTheory.Thomason.Gray.PosetPrismEndpoints
import OAI.CategoryTheory.Thomason.Simplicial.BarycentricSortedCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionImageLattice
import OAI.CategoryTheory.Thomason.Simplicial.ConstructedExtensionLocalizer
import OAI.CategoryTheory.Thomason.Simplicial.FiniteSingularRelativeLifting
import OAI.CategoryTheory.Thomason.Simplicial.InfiniteExtensionBaseChange
import OAI.CategoryTheory.Thomason.Simplicial.LastVertexWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionUnions
import OAI.CategoryTheory.Thomason.Strict.StreetWhitehead
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Extension.Linear

namespace OAI

section

/-! # Extension preserves the deletion/closed-star cover

A map from the nerve of a poset with a greatest vertex into a simplex
subcomplex either avoids its greatest allowed vertex, or lies in that
vertex's closed star.  Appending the greatest source vertex supplies the
face witnessing the second alternative.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits PartialOrder
open scoped Simplicial

noncomputable section

def appendGreatestSimplex {Q : Type} [PartialOrder Q] (v : Q) (hv : ∀ q, q ≤ v)
    {d : ℕ} (s : (nerve Q) _⦋d⦌) : (nerve Q) _⦋d+1⦌ :=
  NormalizedSimplexIdentities.orderSimplex {
    toFun := Fin.snoc s.obj v
    monotone' := by
      intro i j hij
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simpa only [Fin.snoc_castSucc] using
            leOfHom (s.map (homOfLE (Fin.castSucc_le_castSucc_iff.mp hij)))
        · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hv (s.obj i)
      · have hj : j = Fin.last (d+1) := le_antisymm (Fin.le_last j) hij
        subst j
        exact le_rfl }

@[simp]
theorem appendGreatestSimplex_castSucc {Q : Type} [PartialOrder Q]
    (v : Q) (hv : ∀ q, q ≤ v) {d : ℕ} (s : (nerve Q) _⦋d⦌) (i : Fin (d+1)) :
    (appendGreatestSimplex v hv s).obj i.castSucc = s.obj i := by
  change Fin.snoc (α := fun _ : Fin (d+2) => Q) s.obj v i.castSucc = s.obj i
  exact Fin.snoc_castSucc (α := fun _ : Fin (d+2) => Q) v s.obj i

@[simp]
theorem appendGreatestSimplex_last {Q : Type} [PartialOrder Q]
    (v : Q) (hv : ∀ q, q ≤ v) {d : ℕ} (s : (nerve Q) _⦋d⦌) :
    (appendGreatestSimplex v hv s).obj (Fin.last (d+1)) = v := by
  change Fin.snoc (α := fun _ : Fin (d+2) => Q) s.obj v (Fin.last (d+1)) = v
  exact Fin.snoc_last (α := fun _ : Fin (d+2) => Q) v s.obj

theorem simplex_in_containing_face {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex)
    {d : SimplexCategoryᵒᵖ} (x : A.toSSet.obj d) :
    ∃ T : Finset (Fin (n+1)), SSet.stdSimplex.face T ≤ A ∧
      ∀ i : Fin (d.unop.len+1), (SSet.stdSimplex.objEquiv x.val).toOrderHom i ∈ T := by
  classical
  let y : (Δ[n] : SSet.{0}).obj d := x.val
  have hx : y ∈ A.obj d := x.property
  rw [← faceUnion_subcomplexFaceFamily A] at hx
  simp only [faceUnion, Finset.sup_eq_iSup, Subfunctor.iSup_obj, Set.mem_iUnion] at hx
  obtain ⟨T, hT, hx⟩ := hx
  exact ⟨T, (Finset.mem_filter.mp hT).2,
    (SSet.stdSimplex.mem_face_iff T _).mp hx⟩

theorem nerve_map_factors_deletion_or_star {n : ℕ}
    (A : (Δ[n] : SSet.{0}).Subcomplex) (S : Finset (Fin (n+1)))
    (hA : A ≤ SSet.stdSimplex.face S) (v : Fin (n+1))
    (hmax : ∀ w ∈ S, w ≤ v)
    {Q : Type} [PartialOrder Q] (q : Q) (hq : ∀ x, x ≤ q)
    (f : nerve Q ⟶ A.toSSet) :
    (∃ g : nerve Q ⟶ ((SSet.stdSimplex.face (S.erase v)).preimage A.ι).toSSet,
      g ≫ ((SSet.stdSimplex.face (S.erase v)).preimage A.ι).ι = f) ∨
    (∃ g : nerve Q ⟶ ((closedVertexStar A v).preimage A.ι).toSSet,
      g ≫ ((closedVertexStar A v).preimage A.ι).ι = f) := by
  classical
  let u : nerve Q ⟶ nerve (ULift.{0} (Fin (n+1))) :=
    f ≫ A.ι ≫ (simplexNerveIso.app (.mk n)).hom
  let F : Q ⥤ ULift.{0} (Fin (n+1)) :=
    (nerveFunctor.preimage (X := Cat.of Q) (Y := Cat.of (ULift.{0} (Fin (n+1)))) u).toFunctor
  have hF : nerveMap F = u :=
    nerveFunctor.map_preimage (X := Cat.of Q) (Y := Cat.of (ULift.{0} (Fin (n+1)))) u
  have hf (d : SimplexCategoryᵒᵖ) (s : (nerve Q).obj d) (i : Fin (d.unop.len+1)) :
      (SSet.stdSimplex.objEquiv (f.app d s).val).toOrderHom i = (F.obj (s.obj i)).down := by
    have h := congrArg (fun a : nerve Q ⟶ nerve (ULift.{0} (Fin (n+1))) =>
      ((a.app d s).obj i).down) hF
    exact h.symm
  by_cases he : (F.obj q).down = v
  · right
    have hr : SSet.Subcomplex.range f ≤ (closedVertexStar A v).preimage A.ι := by
      intro d x hx
      obtain ⟨s, rfl⟩ := hx
      let t := appendGreatestSimplex q hq s
      obtain ⟨T, hT, ht⟩ := simplex_in_containing_face A (f.app _ t)
      refine ⟨T, ?_, hT, (SSet.stdSimplex.mem_face_iff T _).mpr ?_⟩
      · have hv := ht (Fin.last (d.unop.len+1))
        rw [hf, appendGreatestSimplex_last, he] at hv
        exact hv
      · intro i
        have hi := ht i.castSucc
        rw [hf, appendGreatestSimplex_castSucc, ← hf] at hi
        exact hi
    exact ⟨SSet.Subcomplex.lift f hr, SSet.Subcomplex.lift_ι f hr⟩
  · left
    have hr : SSet.Subcomplex.range f ≤ (SSet.stdSimplex.face (S.erase v)).preimage A.ι := by
      intro d x hx
      obtain ⟨s, rfl⟩ := hx
      apply (SSet.stdSimplex.mem_face_iff (S.erase v) _).mpr
      intro i
      apply Finset.mem_erase.mpr
      refine ⟨?_, (SSet.stdSimplex.mem_face_iff S _).mp (hA _ (f.app d s).property) i⟩
      intro hi
      change (SSet.stdSimplex.objEquiv (f.app d s).val).toOrderHom i = v at hi
      have hle : (F.obj (s.obj i)).down ≤ (F.obj q).down :=
        leOfHom (F.map (homOfLE (hq (s.obj i))))
      have htop : (F.obj q).down ≤ v := by
        let z : (nerve Q) _⦋0⦌ := CategoryTheory.ComposableArrows.mk₀ q
        have hvq := (SSet.stdSimplex.mem_face_iff S _).mp
          (hA _ (f.app (.op (.mk 0)) z).property) 0
        change (SSet.stdSimplex.objEquiv
          (f.app (.op (.mk 0)) z).val).toOrderHom 0 ∈ S at hvq
        have hqf := hf (.op (.mk 0)) z 0
        exact hmax _ (Eq.mp (congrArg (fun w => w ∈ S) hqf) hvq)
      have hvle : v ≤ (F.obj q).down := by
        rw [← hf, hi] at hle
        exact hle
      exact he (le_antisymm htop hvle)
    exact ⟨SSet.Subcomplex.lift f hr, SSet.Subcomplex.lift_ι f hr⟩

theorem extension_deletion_star_cover {n : ℕ}
    (A : (Δ[n] : SSet.{0}).Subcomplex) (S : Finset (Fin (n+1)))
    (hA : A ≤ SSet.stdSimplex.face S) (v : Fin (n+1))
    (hmax : ∀ w ∈ S, w ≤ v) :
    extensionImage ((SSet.stdSimplex.face (S.erase v)).preimage A.ι) ⊔
      extensionImage ((closedVertexStar A v).preimage A.ι) = ⊤ := by
  apply top_unique
  intro d s _
  let a := (SSet.sdExAdjunction.homEquiv (SSet.stdSimplex.obj d.unop) A.toSSet).symm
    (SSet.yonedaEquiv.symm s)
  let e := subdivisionFaceIso d.unop
  have h := nerve_map_factors_deletion_or_star A S hA v hmax
    (simplexTopFace d.unop.len) (fun _ => Finset.subset_univ _) (e.inv ≫ a)
  have hmem (C : A.toSSet.Subcomplex)
      (g : nerve (NonemptyFiniteChains (ULift.{0} (Fin (d.unop.len+1)))) ⟶ C.toSSet)
      (hg : g ≫ C.ι = e.inv ≫ a) : s ∈ (extensionImage C).obj d := by
    let b := e.hom ≫ g
    have hb : b ≫ C.ι = a := by
      rw [Category.assoc, hg, e.hom_inv_id_assoc]
    have he : SSet.sdExAdjunction.homEquiv _ _ b ≫ SSet.ex.map C.ι =
        SSet.yonedaEquiv.symm s := by
      rw [← SSet.sdExAdjunction.homEquiv_naturality_right, hb]
      exact (SSet.sdExAdjunction.homEquiv _ _).apply_symm_apply _
    refine ⟨SSet.yonedaEquiv (SSet.sdExAdjunction.homEquiv _ _ b), ?_⟩
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv he
  exact h.imp (fun ⟨g, hg⟩ => hmem _ g hg) (fun ⟨g, hg⟩ => hmem _ g hg)

end

end Thomason.Construction

end

section

/-! # Canonical extension on every simplex subcomplex

Induct on the allowed vertex set.  Delete its greatest vertex and cover
the subcomplex by that deletion and the greatest vertex's closed star.
The star contracts, and extension preserves this particular cover.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

def containedSubcomplexIso {X : SSet.{0}} {C A : X.Subcomplex} (h : C ≤ A) :
    C.toSSet ≅ (C.preimage A.ι).toSSet where
  hom := {
    app d := ↾fun x => ⟨⟨x.val, h d x.property⟩, x.property⟩
    naturality _ _ _ := rfl }
  inv := {
    app _ := ↾fun x => ⟨x.val.val, x.property⟩
    naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

theorem canonicalExtension_anodyne_of_cover_inside {X : SSet.{0}}
    (A C D : X.Subcomplex) (hC : C ≤ A) (hD : D ≤ A)
    (hcover : extensionImage (C.preimage A.ι) ⊔ extensionImage (D.preimage A.ι) = ⊤)
    (hjC : SSet.anodyneExtensions (canonicalExtension.app C.toSSet))
    (hjD : SSet.anodyneExtensions (canonicalExtension.app D.toSSet))
    (hjCD : SSet.anodyneExtensions (canonicalExtension.app (C ⊓ D).toSSet)) :
    SSet.anodyneExtensions (canonicalExtension.app A.toSSet) := by
  apply canonicalExtension_anodyne_of_extended_cover (C.preimage A.ι) (D.preimage A.ι) hcover
  · exact canonicalExtension_anodyne_of_iso (containedSubcomplexIso hC).symm hjC
  · exact canonicalExtension_anodyne_of_iso (containedSubcomplexIso hD).symm hjD
  · rw [← SSet.Subcomplex.preimage_min]
    exact canonicalExtension_anodyne_of_iso
      (containedSubcomplexIso (show C ⊓ D ≤ A from inf_le_left.trans hC)).symm hjCD

private theorem canonicalExtension_simplexSubcomplex_aux (k : ℕ) :
    ∀ (n : ℕ) (S : Finset (Fin (n+1))), S.card = k →
      ∀ (A : (Δ[n] : SSet.{0}).Subcomplex), A ≤ SSet.stdSimplex.face S →
        SSet.anodyneExtensions (canonicalExtension.app A.toSSet) := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro n S hcard A hA
    rcases S.eq_empty_or_nonempty with hS | hS
    · have hi : IsInitial A.toSSet := SSet.isInitialOfNotNonempty (by
        rintro ⟨x⟩
        have hx := hA _ x.property
        rw [hS, SSet.stdSimplex.face_empty] at hx
        exact hx)
      have := canonicalExtension_isIso_of_initial hi
      exact SSet.anodyneExtensions.of_isIso _
    · let v := S.max' hS
      have hv : v ∈ S := Finset.max'_mem S hS
      have hmax : ∀ w ∈ S, w ≤ v := fun w hw => Finset.le_max' S w hw
      let C := A ⊓ SSet.stdSimplex.face (S.erase v)
      let D := closedVertexStar A v
      have hsmall : (S.erase v).card < k := by
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem hv
      have hpre : C.preimage A.ι = (SSet.stdSimplex.face (S.erase v)).preimage A.ι := by
        ext d x
        exact and_iff_right x.property
      apply canonicalExtension_anodyne_of_cover_inside A C D inf_le_left
        (closedVertexStar_le A v)
      · rw [hpre]
        exact extension_deletion_star_cover A S hA v hmax
      · exact ih (S.erase v).card hsmall n (S.erase v) rfl C inf_le_right
      · exact canonicalExtension_closedVertexStar_anodyne A v (fun d x i =>
          hmax _ ((SSet.stdSimplex.mem_face_iff S _).mp (hA d x.property) i))
      · exact ih (S.erase v).card hsmall n (S.erase v) rfl (C ⊓ D)
          (inf_le_left.trans inf_le_right)

/-- Every subcomplex of a standard simplex has an anodyne canonical
extension, including its entire original boundary. -/
theorem canonicalExtension_simplexSubcomplex_anodyne {n : ℕ}
    (A : (Δ[n] : SSet.{0}).Subcomplex) :
    SSet.anodyneExtensions (canonicalExtension.app A.toSSet) :=
  canonicalExtension_simplexSubcomplex_aux (Finset.univ : Finset (Fin (n+1))).card n
    Finset.univ rfl A (by rw [SSet.stdSimplex.face_univ]; exact le_top)

theorem canonicalExtension_boundary_anodyne (n : ℕ) :
    SSet.anodyneExtensions (canonicalExtension.app (SSet.boundary.{0} n).toSSet) :=
  canonicalExtension_simplexSubcomplex_anodyne _

theorem relativeCanonicalExtension_boundary_anodyne (n : ℕ) :
    SSet.anodyneExtensions (relativeCanonicalExtension (SSet.boundary.{0} n).ι) :=
  relativeCanonicalExtension_anodyne _ (canonicalExtension_boundary_anodyne n)
    (canonicalExtension_standard_anodyne n)

end

end Thomason.Construction

end

section

/-! # Descending subdivided maps into a Kan complex

The proved double-last-vertex homotopy identifies the two relevant mates.
An anodyne canonical extension of the subdivided parameter then suffices
to descend a map, together with an actual simplicial comparison homotopy.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

/-- The mate of the double-last-vertex homotopy compares the canonical
extension on Sd K with the adjunction unit on K. -/
def subdivisionUnitHomotopy (K : SSet.{0}) :
    SSet.Homotopy (lastVertex.app K ≫ SSet.sdExAdjunction.unit.app K)
      (canonicalExtension.app (SSet.sd.obj K)) := by
  let H := subdivisionAdjunctHomotopy (subdivisionLastVertexHomotopy K)
  have h₀ : SSet.sdExAdjunction.homEquiv (SSet.sd.obj K) (SSet.sd.obj K)
      (SSet.sd.map (lastVertex.app K)) =
        lastVertex.app K ≫ SSet.sdExAdjunction.unit.app K := by
    rw [SSet.sdExAdjunction.homEquiv_unit]
    exact (SSet.sdExAdjunction.unit.naturality (lastVertex.app K)).symm
  have h₁ : SSet.sdExAdjunction.homEquiv (SSet.sd.obj K) (SSet.sd.obj K)
      (lastVertex.app (SSet.sd.obj K)) = canonicalExtension.app (SSet.sd.obj K) := rfl
  exact { h := H.h, h₀ := H.h₀.trans h₀, h₁ := H.h₁.trans h₁, rel := H.rel }

/-- If the canonical extension of the subdivided parameter is anodyne,
every map from that subdivision into a Kan complex descends up to an
actual simplicial homotopy. -/
theorem exists_subdivision_descent (K X : SSet.{0}) [SSet.KanComplex X]
    (hK : SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj K)))
    (f : SSet.sd.obj K ⟶ X) :
    ∃ g : K ⟶ X, Nonempty (SSet.Homotopy
      (lastVertex.app K ≫ g) f) := by
  let p : X ⟶ ⊤_ SSet.{0} := terminal.from X
  have hp : J.rlp p := (fibration_iff p).mp inferInstance
  let : HasLiftingProperty (canonicalExtension.app (SSet.sd.obj K)) p := hK p hp
  let sq : CommSq f (canonicalExtension.app (SSet.sd.obj K)) p
      (terminal.from (SSet.ex.obj (SSet.sd.obj K))) := ⟨Subsingleton.elim _ _⟩
  let g : K ⟶ X := SSet.sdExAdjunction.unit.app K ≫ sq.lift
  let H := postcomposeSimplicialHomotopy (subdivisionUnitHomotopy K) sq.lift
  refine ⟨g, ⟨{ h := H.h, h₀ := ?_, h₁ := ?_, rel := H.rel }⟩⟩
  · exact H.h₀.trans (Category.assoc _ _ _)
  · exact H.h₁.trans sq.fac_left

/-- This descent is already unconditional for every standard simplex. -/
theorem exists_standard_subdivision_descent (n : ℕ) (X : SSet.{0}) [SSet.KanComplex X]
    (f : SSet.sd.obj (SSet.stdSimplex.obj (.mk n)) ⟶ X) :
    ∃ g : SSet.stdSimplex.obj (.mk n) ⟶ X, Nonempty (SSet.Homotopy
      (lastVertex.app (SSet.stdSimplex.obj (.mk n)) ≫ g) f) :=
  exists_subdivision_descent _ X (canonicalExtension_subdivision_standard_anodyne n) f

end

end Thomason.Construction

end

section

/-! # Finite poset parameters descend into the original Kan complex

A finite linear extension embeds a finite poset nerve into a standard
simplex.  Its image is a finite union of faces, so the canonical extension
of its subdivision is anodyne.  The actual unit/last-vertex homotopy then
descends maps from the subdivision into a Kan complex.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

theorem finitePoset_nerve_simplex_embedding (P : Type) [PartialOrder P]
    [Finite P] [Nonempty P] :
    ∃ (n : ℕ) (f : nerve P ⟶ (Δ[n] : SSet.{0})), Mono f := by
  have : Finite (LinearExtension P) := by change Finite P; infer_instance
  have : Nonempty (LinearExtension P) := by change Nonempty P; infer_instance
  let := Fintype.ofFinite (LinearExtension P)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Fintype.card_ne_zero : Fintype.card (LinearExtension P) ≠ 0)
  let e := Fintype.orderIsoFinOfCardEq (LinearExtension P) hn
  let v : P →o ULift.{0} (Fin (n+1)) :=
    { toFun p := ULift.up (e.symm (toLinearExtension p))
      monotone' _ _ h := e.symm.monotone (toLinearExtension.monotone h) }
  have hv : Function.Injective v := by
    intro p q h
    exact e.symm.injective (congrArg ULift.down h)
  have := SubdivisionHornFaces.nerveMap_mono v hv
  let e₀ : (Δ[n] : SSet.{0}) ≅ nerve (ULift.{0} (Fin (n+1))) :=
    simplexNerveIso.app ⦋n⦌
  have hf : Mono (nerveMap v.monotone.functor ≫ e₀.inv) := inferInstance
  exact ⟨n, nerveMap v.monotone.functor ≫ e₀.inv, hf⟩

theorem canonicalExtension_subdivision_of_simplex_mono {K : SSet.{0}} {n : ℕ}
    (f : K ⟶ (Δ[n] : SSet.{0})) [Mono f] :
    SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj K)) := by
  let e : K ≅ (SSet.Subcomplex.range f).toSSet := asIso (SSet.Subcomplex.toRange f)
  exact canonicalExtension_anodyne_of_iso (SSet.sd.mapIso e)
    (canonicalExtension_subdivision_subcomplex_anodyne (SSet.Subcomplex.range f))

theorem canonicalExtension_subdivision_finitePoset_anodyne (P : Type)
    [PartialOrder P] [Finite P] :
    SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj (nerve P))) := by
  rcases isEmpty_or_nonempty P with hP | hP
  · have hi : IsInitial (nerve P) := SSet.isInitialOfNotNonempty (by
      rintro ⟨s⟩
      exact isEmptyElim (s.obj 0))
    have := canonicalExtension_isIso_of_initial (IsInitial.isInitialObj SSet.sd _ hi)
    exact SSet.anodyneExtensions.of_isIso _
  · obtain ⟨n, f, hf⟩ := finitePoset_nerve_simplex_embedding P
    exact canonicalExtension_subdivision_of_simplex_mono f

theorem exists_finitePoset_subdivision_descent (P : Type) [PartialOrder P] [Finite P]
    (X : SSet.{0}) [SSet.KanComplex X] (f : SSet.sd.obj (nerve P) ⟶ X) :
    ∃ g : nerve P ⟶ X, Nonempty (SSet.Homotopy
      (lastVertex.app (nerve P) ≫ g) f) :=
  exists_subdivision_descent _ X (canonicalExtension_subdivision_finitePoset_anodyne P) f

theorem exists_subcomplex_subdivision_descent {n : ℕ}
    (A : (Δ[n] : SSet.{0}).Subcomplex) (X : SSet.{0}) [SSet.KanComplex X]
    (f : SSet.sd.obj A.toSSet ⟶ X) :
    ∃ g : A.toSSet ⟶ X, Nonempty (SSet.Homotopy (lastVertex.app A.toSSet ≫ g) f) :=
  exists_subdivision_descent _ X (canonicalExtension_subdivision_subcomplex_anodyne A) f

end

end Thomason.Construction

end

section

/-! # Actual subdivision homeomorphisms for finite poset parameters

The finite linear extension realizes a poset nerve as a simplex
subcomplex. Transporting the constructed barycentric homeomorphism gives
the finite parameter homeomorphism needed for repeated approximation.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

def subdivisionHomeomorphOfMono {K : SSet.{0}} {n : ℕ}
    (f : K ⟶ (Δ[n] : SSet.{0})) [Mono f] :
    SSet.toTop.obj (SSet.sd.obj K) ≃ₜ SSet.toTop.obj K :=
  let e : K ≅ (SSet.Subcomplex.range f).toSSet := asIso (SSet.Subcomplex.toRange f)
  (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.sd.mapIso e))).trans
    ((subcomplexSubdivisionHomeomorph (SSet.Subcomplex.range f)).trans
      (TopCat.homeoOfIso (SSet.toTop.mapIso e)).symm)

/-- For every finite poset, including the empty one, subdivision retains
the actual realization space homeomorphically. -/
def finitePosetSubdivisionHomeomorph (P : Type) [PartialOrder P] [Finite P] :
    SSet.toTop.obj (SSet.sd.obj (nerve P)) ≃ₜ SSet.toTop.obj (nerve P) := by
  classical
  by_cases hP : Nonempty P
  · letI := hP
    let n := (finitePoset_nerve_simplex_embedding P).choose
    let f := (finitePoset_nerve_simplex_embedding P).choose_spec.choose
    have : Mono f := (finitePoset_nerve_simplex_embedding P).choose_spec.choose_spec
    exact subdivisionHomeomorphOfMono (n := n) f
  · letI : IsEmpty P := not_nonempty_iff.mp hP
    have hi : IsInitial (nerve P) := SSet.isInitialOfNotNonempty (by
      rintro ⟨s⟩
      exact isEmptyElim (s.obj 0))
    exact TopCat.homeoOfIso (SSet.toTop.mapIso
      ((IsInitial.isInitialObj SSet.sd _ hi).uniqueUpToIso hi))

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Weak-equivalence compatibility of Kan subdivision descent

The descended map into the original Kan complex has the same actual
realization weak-equivalence test as the map on the subdivided parameter.
The comparison uses the proved last-vertex weak equivalence.
-/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

theorem subdivision_descent_weak_iff {K X : SSet.{0}}
    {g : K ⟶ X} {f : SSet.sd.obj K ⟶ X}
    (H : SSet.Homotopy (lastVertex.app K ≫ g) f) :
    realizationWeakEquivalences g ↔ realizationWeakEquivalences f := by
  have h := RealizedCylinder.weakEquivalence_iff H
  constructor
  · intro hg
    exact h.mp (realizationWeakEquivalences.comp_mem _ _ (lastVertex_weak K) hg)
  · intro hf
    exact realizationWeakEquivalences.of_precomp (lastVertex.app K) g
      (lastVertex_weak K) (h.mpr hf)

/-- Finite-poset descent preserves and reflects the actual topological
weak-equivalence predicate, with a simplicial comparison homotopy. -/
theorem exists_finitePoset_weak_descent (P : Type) [PartialOrder P] [Finite P]
    (X : SSet.{0}) [SSet.KanComplex X] (f : SSet.sd.obj (nerve P) ⟶ X) :
    ∃ g : nerve P ⟶ X, Nonempty (SSet.Homotopy (lastVertex.app (nerve P) ≫ g) f) ∧
      (realizationWeakEquivalences g ↔ realizationWeakEquivalences f) := by
  obtain ⟨g, ⟨H⟩⟩ := exists_finitePoset_subdivision_descent P X f
  exact ⟨g, ⟨H⟩, subdivision_descent_weak_iff H⟩

end

end Thomason.Construction

end

section

/-! # Subdivision descent with an exact prescribed base map

For a Kan fibration over a Kan base, the finite-parameter descent retains
the base map exactly. Only the comparison with the original subdivided
map is homotopical.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

theorem subdivision_unit_extension_lastVertex (K : SSet.{0}) :
    SSet.sdExAdjunction.unit.app K ≫ SSet.ex.map (lastVertex.app K) =
      canonicalExtension.app K :=
  (SSet.sdExAdjunction.homEquiv_unit K K (lastVertex.app K)).symm

/-- A map on a subdivided parameter descends over the same base map.
The two anodyne premises hold for the finite poset parameters used below. -/
theorem exists_subdivision_descent_over_kan {K E B : SSet.{0}}
    [SSet.KanComplex B] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (hK : SSet.anodyneExtensions (canonicalExtension.app K))
    (hSd : SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj K)))
    (a : SSet.sd.obj K ⟶ E) (b : K ⟶ B)
    (hab : a ≫ p = lastVertex.app K ≫ b) :
    ∃ g : K ⟶ E, g ≫ p = b ∧
      Nonempty (SSet.Homotopy (lastVertex.app K ≫ g) a) := by
  let t : B ⟶ ⊤_ SSet.{0} := terminal.from B
  have ht : J.rlp t := (fibration_iff t).mp inferInstance
  let : HasLiftingProperty (canonicalExtension.app K) t := hK t ht
  let sqB : CommSq b (canonicalExtension.app K) t
      (terminal.from (SSet.ex.obj K)) := ⟨Subsingleton.elim _ _⟩
  let q : SSet.ex.obj (SSet.sd.obj K) ⟶ B :=
    SSet.ex.map (lastVertex.app K) ≫ sqB.lift
  have hp : J.rlp p := (fibration_iff p).mp inferInstance
  let : HasLiftingProperty (canonicalExtension.app (SSet.sd.obj K)) p := hSd p hp
  let sq : CommSq a (canonicalExtension.app (SSet.sd.obj K)) p q := ⟨by
    dsimp only [q]
    rw [hab, ← Category.assoc, ← canonicalExtension.naturality]
    change lastVertex.app K ≫ b = (lastVertex.app K ≫ canonicalExtension.app K) ≫ sqB.lift
    rw [Category.assoc, sqB.fac_left]⟩
  let g : K ⟶ E := SSet.sdExAdjunction.unit.app K ≫ sq.lift
  have hgp : g ≫ p = b := by
    dsimp only [g]
    rw [Category.assoc, sq.fac_right]
    dsimp only [q]
    rw [← Category.assoc,
      subdivision_unit_extension_lastVertex, sqB.fac_left]
  let H := postcomposeSimplicialHomotopy (subdivisionUnitHomotopy K) sq.lift
  refine ⟨g, hgp, ⟨{ h := H.h, h₀ := ?_, h₁ := ?_, rel := H.rel }⟩⟩
  · exact H.h₀.trans (Category.assoc _ _ _)
  · exact H.h₁.trans sq.fac_left

/-- Concrete relative descent for every finite poset, with no additional
published input. -/
theorem exists_finitePoset_subdivision_descent_over_kan
    (P : Type) [PartialOrder P] [Finite P] {E B : SSet.{0}}
    [SSet.KanComplex B] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (a : SSet.sd.obj (nerve P) ⟶ E) (b : nerve P ⟶ B)
    (hab : a ≫ p = lastVertex.app (nerve P) ≫ b) :
    ∃ g : nerve P ⟶ E, g ≫ p = b ∧
      Nonempty (SSet.Homotopy (lastVertex.app (nerve P) ≫ g) a) :=
  exists_subdivision_descent_over_kan p (canonicalExtension_finitePoset_anodyne P)
    (canonicalExtension_subdivision_finitePoset_anodyne P) a b hab

end

end Thomason.Construction

end

section

/-! # Subdivision of a finite poset nerve is its chain nerve

The canonical map is surjective because each target simplex is contained
in one greatest finite face. Finite linear extensions prove monicity.
This identifies actual repeated subdivisions used in finite approximation.
-/

namespace Thomason.Construction.NerveSubdivisionMap

open CategoryTheory CategoryTheory.Limits PartialOrder
open scoped Simplicial

noncomputable section

def faceEmbedding {P : Type} [PartialOrder P] (C : NonemptyFiniteChains P) :
    ULift.{0} (Fin ((ChainOrdinal.choose C).dim+1)) ↪o P where
  toFun i := ((ChainOrdinal.choose C).enum i.down).val
  inj' := by
    intro i j h
    exact ULift.ext _ _ ((ChainOrdinal.choose C).enum.injective (Subtype.ext h))
  map_rel_iff' := by
    intro i j
    exact (ChainOrdinal.choose C).enum.le_iff_le

theorem faceEmbedding_range {P : Type} [PartialOrder P] (C : NonemptyFiniteChains P) :
    Set.range (faceEmbedding C) = (C.finset : Set P) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ((ChainOrdinal.choose C).enum i.down).property
  · intro hx
    obtain ⟨i, hi⟩ := (ChainOrdinal.choose C).enum.surjective ⟨x, hx⟩
    exact ⟨ULift.up i, congrArg Subtype.val hi⟩

/-- Every simplex of the chain nerve lifts through one actual standard
subdivision simplex. -/
theorem map_surjective (P : Type) [PartialOrder P] (d : SimplexCategoryᵒᵖ) :
    Function.Surjective ((map P).app d) := by
  intro s
  let C := s.obj (Fin.last d.unop.len)
  let e := faceEmbedding C
  have hs : s ∈ (SSet.Subcomplex.range (chainNerveMap e.toOrderHom)).obj d := by
    change s ∈ (SSet.Subcomplex.range
      (nerveMap (NonemptyFiniteChains.orderHomMap e.toOrderHom).monotone.functor)).obj d
    rw [finiteChain_nerve_range e]
    intro i x hx
    rw [faceEmbedding_range]
    exact leOfHom (s.map (homOfLE (Fin.le_last i))) hx
  obtain ⟨t, ht⟩ := hs
  let u : (Δ[(ChainOrdinal.choose C).dim] : SSet.{0}) ⟶ nerve P :=
    SSet.yonedaEquiv.symm
      (NormalizedSimplexIdentities.orderSimplex
        { toFun i := e (ULift.up i)
          monotone' _ _ h := e.monotone h })
  have hv : vertices u = e.toOrderHom := by
    ext i
    change (SSet.yonedaEquiv u).obj i.down = e i
    rw [SSet.yonedaEquiv.apply_symm_apply]
    rfl
  let v := (SSet.stdSimplex.sdIso.inv.app (.mk (ChainOrdinal.choose C).dim)).app d t
  refine ⟨(SSet.sd.map u).app d v, ?_⟩
  have hf := congrArg (fun f => f.app d v) (map_fac u)
  change (map P).app d ((SSet.sd.map u).app d v) = _ at hf
  rw [hf]
  change (chainNerveMap (vertices u)).app d
    ((SSet.stdSimplex.sdIso.hom.app (.mk (ChainOrdinal.choose C).dim)).app d v) = s
  rw [hv]
  have hi : (SSet.stdSimplex.sdIso.hom.app (.mk (ChainOrdinal.choose C).dim)).app d v = t := by
    have he := SSet.stdSimplex.sdIso.inv_hom_id_app (.mk (ChainOrdinal.choose C).dim)
    exact congrArg (fun f : SimplexCategory.sd.obj (.mk (ChainOrdinal.choose C).dim) ⟶
      SimplexCategory.sd.obj (.mk (ChainOrdinal.choose C).dim) => f.app d t) he
  exact hi ▸ ht

theorem map_epi (P : Type) [PartialOrder P] : Epi (map P) := by
  rw [NatTrans.epi_iff_epi_app]
  intro d
  exact (CategoryTheory.epi_iff_surjective _).mpr (map_surjective P d)

/-- A finite linear extension reduces monicity to the standard simplex. -/
theorem map_mono (P : Type) [PartialOrder P] [Finite P] : Mono (map P) := by
  classical
  rcases isEmpty_or_nonempty P with hP | hP
  · have hi : IsInitial (nerve P) := SSet.isInitialOfNotNonempty (by
      rintro ⟨s⟩
      exact isEmptyElim (s.obj 0))
    have hs := IsInitial.isInitialObj SSet.sd _ hi
    rw [NatTrans.mono_iff_mono_app]
    intro d
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro x y _
    exact ((Types.initial_iff_empty _).mp ⟨IsInitial.isInitialObj (SSet.evaluation.obj d) _ hs⟩).elim x
  · have : Finite (LinearExtension P) := by change Finite P; infer_instance
    have : Nonempty (LinearExtension P) := by change Nonempty P; infer_instance
    let := Fintype.ofFinite (LinearExtension P)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (Fintype.card_ne_zero : Fintype.card (LinearExtension P) ≠ 0)
    let e := Fintype.orderIsoFinOfCardEq (LinearExtension P) hn
    let v : P →o ULift.{0} (Fin (n+1)) :=
      { toFun p := ULift.up (e.symm (toLinearExtension p))
        monotone' _ _ h := e.symm.monotone (toLinearExtension.monotone h) }
    have hv : Function.Injective v := by
      intro p q h
      exact e.symm.injective (congrArg ULift.down h)
    have := SubdivisionHornFaces.nerveMap_mono v hv
    have := subdivision_map_mono (nerveMap v.monotone.functor)
    have : Mono (map (ULift.{0} (Fin (n+1)))) := by
      let u : SSet.sd.obj (Δ[n] : SSet.{0}) ⟶
          SSet.sd.obj (nerve (ULift.{0} (Fin (n+1)))) :=
        SSet.sd.map (simplexNerveIso.hom.app (.mk n))
      have : IsIso u := by
        change IsIso (SSet.sd.mapIso (simplexNerveIso.app (.mk n))).hom
        infer_instance
      have : Mono (u ≫ map (ULift.{0} (Fin (n+1)))) := by
        rw [show u ≫ map (ULift.{0} (Fin (n+1))) =
          SSet.stdSimplex.sdIso.hom.app (.mk n) from map_standard (.mk n)]
        change Mono (SSet.stdSimplex.sdIso.app (.mk n)).hom
        infer_instance
      have h : Mono (inv u ≫ (u ≫ map (ULift.{0} (Fin (n+1))))) := inferInstance
      have hu : inv u ≫ u = 𝟙 _ := IsIso.inv_hom_id u
      have he : inv u ≫ (u ≫ map (ULift.{0} (Fin (n+1)))) =
          map (ULift.{0} (Fin (n+1))) := by
        rw [← Category.assoc, hu]
        exact Category.id_comp _
      exact he ▸ h
    have hc : Mono (SSet.sd.map (nerveMap v.monotone.functor) ≫
        map (ULift.{0} (Fin (n+1)))) := inferInstance
    have : Mono (map P ≫ chainNerveMap v) := by
      have he : SSet.sd.map (nerveMap v.monotone.functor) ≫
          map (ULift.{0} (Fin (n+1))) = map P ≫ chainNerveMap v := map_naturality v
      rw [← he]
      exact hc
    exact mono_of_mono (map P) (chainNerveMap v)

def iso (P : Type) [PartialOrder P] [Finite P] :
    SSet.sd.obj (nerve P) ≅ nerve (NonemptyFiniteChains P) := by
  have := map_mono P
  have : IsIso (map P) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro d
    exact (CategoryTheory.isIso_iff_bijective _).mpr
      ⟨(CategoryTheory.mono_iff_injective _).mp inferInstance, map_surjective P d⟩
  exact asIso (map P)

end

end Thomason.Construction.NerveSubdivisionMap

end

section

/-! # Actual iterated subdivision of finite poset parameters

Each stage is the nerve of an explicitly iterated finite-chain poset.
Its canonical extension is anodyne, so repeated approximation can be
descended one stage at a time in the original Kan target.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder

noncomputable section

def iteratedChainPoset (P : PartOrd.{0}) : ℕ → PartOrd.{0}
  | 0 => P
  | r+1 => PartOrd.nonemptyFiniteChainsFunctor.obj (iteratedChainPoset P r)

instance iteratedChainPoset_finite (P : PartOrd.{0}) [Finite P] (r : ℕ) :
    Finite (iteratedChainPoset P r) := by
  induction r with
  | zero => exact inferInstanceAs (Finite P)
  | succ r ih =>
    let := ih
    exact finite_nonemptyFiniteChains (iteratedChainPoset P r)

def iteratedSubdivisionNerveIso (P : PartOrd.{0}) [Finite P] (r : ℕ) :
    (iteratedSubdivision r).obj (nerve P) ≅ nerve (iteratedChainPoset P r) :=
  match r with
  | 0 => Iso.refl _
  | r+1 => SSet.sd.mapIso (iteratedSubdivisionNerveIso P r) ≪≫
      NerveSubdivisionMap.iso (iteratedChainPoset P r)

/-- Every iterated finite parameter has the exact canonical-extension
lifting property, rather than just a realization weak equivalence. -/
theorem iteratedSubdivision_canonical_anodyne (P : PartOrd.{0}) [Finite P] (r : ℕ) :
    SSet.anodyneExtensions (canonicalExtension.app ((iteratedSubdivision r).obj (nerve P))) :=
  canonicalExtension_anodyne_of_iso (iteratedSubdivisionNerveIso P r)
    (canonicalExtension_finitePoset_anodyne (iteratedChainPoset P r))

def iteratedLastVertex (K : SSet.{0}) : (r : ℕ) → (iteratedSubdivision r).obj K ⟶ K
  | 0 => 𝟙 K
  | r+1 => lastVertex.app ((iteratedSubdivision r).obj K) ≫ iteratedLastVertex K r

theorem iteratedLastVertex_weak (K : SSet.{0}) (r : ℕ) :
    realizationWeakEquivalences (iteratedLastVertex K r) := by
  induction r with
  | zero => exact realizationWeakEquivalences.id_mem K
  | succ r ih =>
    exact realizationWeakEquivalences.comp_mem _ _ (lastVertex_weak _) ih

/-- A map out of the next actual subdivision descends into the same Kan
target with an actual simplicial comparison and unchanged weak test. -/
theorem exists_iteratedSubdivision_step_descent (P : PartOrd.{0}) [Finite P]
    (r : ℕ) (X : SSet.{0}) [SSet.KanComplex X]
    (f : (iteratedSubdivision (r+1)).obj (nerve P) ⟶ X) :
    ∃ g : (iteratedSubdivision r).obj (nerve P) ⟶ X,
      Nonempty (SSet.Homotopy (lastVertex.app ((iteratedSubdivision r).obj (nerve P)) ≫ g) f) ∧
        (realizationWeakEquivalences g ↔ realizationWeakEquivalences f) := by
  obtain ⟨g, ⟨H⟩⟩ := exists_subdivision_descent _ X
    (iteratedSubdivision_canonical_anodyne P (r+1)) f
  exact ⟨g, ⟨H⟩, subdivision_descent_weak_iff H⟩

end

end Thomason.Construction

end

section

/-! # One dimension bound for every iterated face subdivision

Taking chains increases the number of vertices, but it does not increase
the dimension of nondegenerate simplices. This supplies a fixed mesh
contraction factor through all finite approximation stages.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder

noncomputable section

def ChainCardBound (P : Type) [PartialOrder P] (N : ℕ) : Prop :=
  ∀ C : NonemptyFiniteChains P, C.finset.card ≤ N+1

theorem chainCardBound_chains {P : Type} [PartialOrder P] {N : ℕ}
    (hP : ChainCardBound P N) : ChainCardBound (NonemptyFiniteChains P) N := by
  classical
  intro D
  let f : D.finset → Fin (N+1) := fun C =>
    ⟨C.val.finset.card-1, by
      have hc := hP C.val
      have hp := Finset.card_pos.mpr C.val.nonempty
      omega⟩
  have hf : Function.Injective f := by
    intro C E he
    have hv := congrArg Fin.val he
    have hpC := Finset.card_pos.mpr C.val.nonempty
    have hpE := Finset.card_pos.mpr E.val.nonempty
    have hc : C.val.finset.card = E.val.finset.card := by
      change C.val.finset.card-1 = E.val.finset.card-1 at hv
      omega
    apply Subtype.ext
    apply NonemptyFiniteChains.ext
    rcases D.comparable C E with hCE | hEC
    · exact Finset.eq_of_subset_of_card_le hCE hc.ge
    · exact (Finset.eq_of_subset_of_card_le hEC hc.le).symm
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

theorem iteratedChainPoset_cardBound (P : PartOrd.{0}) {N : ℕ}
    (hP : ChainCardBound P N) (r : ℕ) : ChainCardBound (iteratedChainPoset P r) N := by
  induction r with
  | zero => exact hP
  | succ r ih => exact chainCardBound_chains ih

theorem simplex_dimension_le_chainCardBound {P : Type} [PartialOrder P] {N m : ℕ}
    (hP : ChainCardBound P N) (s : Fin (m+1) ⥤ P) (hs : StrictMono s.obj) : m ≤ N := by
  classical
  let C : NonemptyFiniteChains P :=
    { finset := Finset.univ.image s.obj
      nonempty := Finset.univ_nonempty.image s.obj
      comparable := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
        exact (le_total i j).elim (fun h => Or.inl (s.monotone h))
          (fun h => Or.inr (s.monotone h)) }
  have hc := hP C
  have he : C.finset.card = m+1 := by
    change (Finset.univ.image s.obj).card = m+1
    rw [Finset.card_image_of_injective _ hs.injective, Finset.card_univ, Fintype.card_fin]
  omega

/-- Every finite starting poset gives one bound valid at every stage. -/
theorem iteratedChainPoset_dimension_le (P : PartOrd.{0}) [Fintype P]
    (r m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset P r) (hs : StrictMono s.obj) :
    m ≤ Fintype.card P := by
  apply simplex_dimension_le_chainCardBound (iteratedChainPoset_cardBound P ?_ r) s hs
  intro C
  exact (Finset.card_le_univ C.finset).trans (Nat.le_succ _)

end

end Thomason.Construction

end

section

/-! # Subdivision compatibility with actual weak equivalences and lifting

These are consequences of the constructed last-vertex equivalence. The
arbitrary acyclic-Kan lifting implication is not assumed or asserted.
-/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

/-- Weak monomorphisms remain weak monomorphisms under actual subdivision. -/
theorem subdivision_weak_mono {K L : SSet.{0}} (f : K ⟶ L) [Mono f]
    (hf : realizationWeakEquivalences f) :
    Mono (SSet.sd.map f) ∧ realizationWeakEquivalences (SSet.sd.map f) :=
  ⟨subdivision_map_mono f, (subdivision_weak_iff f).mpr hf⟩

/-- Subdividing a weak mono retains an exact stationary deformation on its
entire realized image. -/
theorem subdivision_weak_mono_deformation {K L : SSet.{0}} (f : K ⟶ L) [Mono f]
    (hf : realizationWeakEquivalences f) :
    ∃ r : SSet.toTop.obj (SSet.sd.obj L) ⟶ SSet.toTop.obj (SSet.sd.obj K),
      SSet.toTop.map (SSet.sd.map f) ≫ r = 𝟙 _ ∧
      Nonempty ((r ≫ SSet.toTop.map (SSet.sd.map f)).hom.HomotopyRel
        (ContinuousMap.id _) (Set.range (SSet.toTop.map (SSet.sd.map f)).hom)) := by
  have := subdivision_map_mono f
  exact weak_mono_realization_deformation _ ((subdivision_weak_iff f).mpr hf)

/-- Extension preserves boundary lifting and consequently its actual weak
 equivalence, without requiring the open general acyclic-Kan implication. -/
theorem extension_boundary_weak {K L : SSet.{0}} (p : K ⟶ L) (hp : I.rlp p) :
    I.rlp (SSet.ex.map p) ∧ realizationWeakEquivalences (SSet.ex.map p) :=
  ⟨extension_boundary_rlp p hp, boundary_rlp_weak _ (extension_boundary_rlp p hp)⟩

/-- The same precise consequence for the double extension in the Thomason
fibration functor. -/
theorem extension_twice_boundary_weak {K L : SSet.{0}} (p : K ⟶ L) (hp : I.rlp p) :
    I.rlp ((SSet.ex ⋙ SSet.ex).map p) ∧
      realizationWeakEquivalences ((SSet.ex ⋙ SSet.ex).map p) :=
  extension_boundary_weak _ (extension_boundary_rlp p hp)

/-- The proved singular acyclic case remains a boundary-lifting weak map
after the actual double extension. -/
theorem extension_twice_singular_acyclic {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) :
    I.rlp ((SSet.ex ⋙ SSet.ex).map (TopCat.toSSet.map p)) ∧
      realizationWeakEquivalences ((SSet.ex ⋙ SSet.ex).map (TopCat.toSSet.map p)) :=
  extension_twice_boundary_weak _ (singular_fibration_boundary_rlp p hp)

/-- Double subdivision detects exactly the implemented omega-Street weak
 equivalences. No Gray or Kan–Quillen assumption appears. -/
theorem street_subdivision_twice_weak_iff (h : NormalizedSimplexIdentities)
    {C D : StrictOmegaCategory} (f : C ⟶ D) :
    realizationWeakEquivalences ((SSet.sd ⋙ SSet.sd).map (h.streetNerve.map f)) ↔
      h.streetWeakEquivalences f :=
  subdivision_twice_weak_iff (h.streetNerve.map f)

end Thomason.Construction

end

end OAI
