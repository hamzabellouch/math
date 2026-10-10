import OAI.CategoryTheory.Thomason.Gray.TopologicalConePrism
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Strict.OrientalFiniteCells
import OAI.CategoryTheory.Thomason.Strict.StreetSingularWeakReflection
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeCategory
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import OAI.CategoryTheory.Thomason.Transfer.FiniteEmptyAttachmentFibers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Presentable.Adjunction

namespace OAI

section

/-! # Finite limits and colimits in the actual positive finite categories

The constructed intelligent reflection makes the full inclusion reflective.
Finite limits and small colimits therefore follow from the explicitly
constructed omega-category limits and colimits.
-/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)

/-- The actual truncation inclusion, with the given reflection adjunction. -/
@[instance_reducible]
noncomputable def reflectiveInclusion : Reflective (StrictOmegaCategory.inclusion (n+1)) where
  toFull := inferInstance
  toFaithful := inferInstance
  L := r.reflect
  adj := r.adjunction

include r

/-- Small colimits exist in the finite category itself. -/
theorem hasSmallColimits : HasColimitsOfSize.{0,0} (Truncated.{0} (n+1)) := by
  let := r.reflectiveInclusion
  exact hasColimits_of_reflective (StrictOmegaCategory.inclusion (n+1))

/-- Finite limits exist in the finite category itself. -/
theorem hasFiniteLimits : HasFiniteLimits (Truncated.{0} (n+1)) := by
  let := r.reflectiveInclusion
  have := strictOmegaHasFiniteLimits
  exact { out := fun _J _ _ =>
    hasLimitsOfShape_of_reflective (StrictOmegaCategory.inclusion (n+1)) }

end Thomason.Construction.FiniteReflectionInput

namespace Thomason.Construction

open CategoryTheory.Limits StrictOmegaCategory

instance constructedFiniteHasSmallColimits (n : ℕ) :
    HasColimitsOfSize.{0,0} (Truncated.{0} (n+1)) :=
  (constructedFiniteReflection n).hasSmallColimits

instance constructedFiniteHasFiniteLimits (n : ℕ) :
    HasFiniteLimits (Truncated.{0} (n+1)) :=
  (constructedFiniteReflection n).hasFiniteLimits

end Thomason.Construction

end

section

/-! # The actual adjunction unit on posets with a greatest element

The point comparison is an isomorphism. Monotone contractions give weak
equivalences on both ordinary nerves and their strict categorifications;
naturality then transports the unit comparison. No finite-poset unit theorem
or strict-category model structure is assumed here.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/-- A retraction whose other composite is weak has both maps weak. -/
theorem retraction_weakEquivalences {C : Type*} [Category* C]
    (W : MorphismProperty C) [W.HasTwoOutOfThreeProperty]
    [W.ContainsIdentities] [W.IsStableUnderRetracts]
    {A X : C} (i : A ⟶ X) (r : X ⟶ A) (hi : i ≫ r = 𝟙 A)
    (hri : W (r ≫ i)) : W i ∧ W r := by
  have hretract : RetractArrow i (r ≫ i) :=
    { i := Arrow.homMk i (𝟙 X) (by simp [← Category.assoc, hi])
      r := Arrow.homMk r (𝟙 X) (by simp)
      retract := by apply Arrow.hom_ext <;> simp [hi] }
  have hwi : W i := MorphismProperty.of_retract hretract hri
  refine ⟨hwi, W.of_precomp i r hwi ?_⟩
  rw [hi]
  exact W.id_mem A

/-- A natural transformation is weak at either end of a map which is weak
both before and after applying the endofunctor. -/
theorem weak_component_iff {C : Type*} [Category* C]
    (W : MorphismProperty C) [W.HasTwoOutOfThreeProperty]
    {F : C ⥤ C} (η : 𝟭 C ⟶ F) {X Y : C} (f : X ⟶ Y)
    (hf : W f) (hFf : W (F.map f)) : W (η.app X) ↔ W (η.app Y) := by
  have hn : f ≫ η.app Y = η.app X ≫ F.map f := η.naturality f
  constructor
  · intro hx
    apply W.of_precomp f (η.app Y) hf
    rw [hn]
    exact W.comp_mem _ _ hx hFf
  · intro hy
    apply W.of_postcomp (η.app X) (F.map f) hFf
    rw [← hn]
    exact W.comp_mem _ _ hf hy

/-- The ordinary point used in the contraction, with its canonical simplex iso. -/
abbrev PosetPoint : Type := ULift.{0} (Fin 1)

def posetToPoint (P : Type) [PartialOrder P] : P →o PosetPoint :=
  OrderHom.const P ⟨0⟩

def posetFromPoint {P : Type} [PartialOrder P] (x : P) : PosetPoint →o P :=
  OrderHom.const PosetPoint x

theorem poset_point_retraction {P : Type} [PartialOrder P] (x : P) :
    (posetToPoint P).comp (posetFromPoint x) = OrderHom.id := by
  apply DFunLike.ext
  intro a
  exact Subsingleton.elim _ _

/-- The greatest-element contraction satisfies precisely the hypotheses of
the constructed relative chain prism, with empty stationary locus. -/
def greatestElementPrism {P : Type} [PartialOrder P] (x : P) (hx : ∀ y, y ≤ x) :
    RelativePrismData P where
  old := ∅
  lower := by intro a b hab hb; exact hb.elim
  first := OrderHom.id
  last := (posetFromPoint x).comp (posetToPoint P)
  le := hx
  agree := by intro y hy; exact hy.elim
  constant := by intros; rfl

/-- The point inclusion and collapse of a greatest-element poset are weak
equivalences of ordinary nerves, with the actual realization definition. -/
theorem nerve_greatest_point_weakEquivalences (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] (x : P) (hx : ∀ y, y ≤ x) :
    realizationWeakEquivalences (nerveMap (posetFromPoint x).monotone.functor) ∧
      realizationWeakEquivalences (nerveMap (posetToPoint P).monotone.functor) := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  have := kq.weakEquivalences_retracts
  apply retraction_weakEquivalences realizationWeakEquivalences
  · rw [← orderNerveMap_comp, poset_point_retraction, orderNerveMap_id]
  · rw [← orderNerveMap_comp]
    apply (orderNerve_weakEquivalence_iff kq OrderHom.id
      ((posetFromPoint x).comp (posetToPoint P)) hx).mp
    rw [orderNerveMap_id]
    exact realizationWeakEquivalences.id_mem _

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

/-- The constructed zero-dimensional oriental has exactly one cell. -/
theorem object_zero_subsingleton : Subsingleton (h.object 0) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨i, hi⟩ := SimplexComplex.eq_vertex_of_dimensionLE h x (h.isTruncated 0 x)
  obtain ⟨j, hj⟩ := SimplexComplex.eq_vertex_of_dimensionLE h y (h.isTruncated 0 y)
  have he : i = j := by omega
  exact hi.trans ((congrArg (SimplexComplex.vertex h) he).trans hj.symm)

/-- Its terminality uses the full strict functor laws, not just its objects. -/
noncomputable def object_zero_isTerminal : IsTerminal (h.object 0) := by
  letI := h.object_zero_subsingleton
  apply IsTerminal.ofUniqueHom (X := h.object 0)
    (fun X => (show StrictOmegaCategory.Hom X (h.object 0) from
              { toFun := fun _ => SimplexComplex.vertex h 0
                map_face := fun _ _ _ => Subsingleton.elim _ _
                map_comp := fun _ _ _ _ _ => Subsingleton.elim _ _ }))
  intro X f
  apply StrictOmegaCategory.Hom.ext
  funext x
  exact Subsingleton.elim _ _

variable [StrictColimitsInput]

/-- The unit on the standard point is an actual isomorphism. -/
theorem unit_point_isIso : IsIso (h.categorificationAdjunction.unit.app (Δ[0])) := by
  have := h.categorificationAdjunction.rightAdjoint_preservesLimits
  have ht : IsTerminal (h.categorification.obj (Δ[0])) :=
    h.object_zero_isTerminal.ofIso (h.categorificationSimplexIso.app (.mk 0)).symm
  exact isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀
    (ht.isTerminalObj h.streetNerve _) _

/-- The comparison on any simplicial point is weak, by naturality along an
actual isomorphism from the standard point. -/
theorem unit_of_point_iso (kq : KanQuillenPublishedInput.{0})
    {X : SSet.{0}} (e : (Δ[0] : SSet.{0}) ≅ X) :
    realizationWeakEquivalences (h.categorificationAdjunction.unit.app X) := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  have := kq.weakEquivalences_retracts
  have := h.unit_point_isIso
  exact (weak_component_iff realizationWeakEquivalences h.categorificationAdjunction.unit
    e.hom (realizationWeakEquivalences.of_isIso _)
    (realizationWeakEquivalences.of_isIso _)).mp
      (realizationWeakEquivalences.of_isIso _)

/-- The same contraction is weak after actual strict categorification. -/
theorem categorified_greatest_point_weakEquivalences
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] (x : P) (hx : ∀ y, y ≤ x) :
    h.streetWeakEquivalences (h.posetMap (posetFromPoint x)) ∧
      h.streetWeakEquivalences (h.posetMap (posetToPoint P)) := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  have := kq.weakEquivalences_retracts
  have : h.streetWeakEquivalences.HasTwoOutOfThreeProperty :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).HasTwoOutOfThreeProperty
  have : h.streetWeakEquivalences.IsStableUnderRetracts :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).IsStableUnderRetracts
  have : h.streetWeakEquivalences.ContainsIdentities :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).ContainsIdentities
  apply retraction_weakEquivalences h.streetWeakEquivalences
  · rw [← h.posetMap_comp, poset_point_retraction, h.posetMap_id]
  · rw [← h.posetMap_comp]
    apply ((greatestElementPrism x hx).weakEquivalence_iff h G aw kq).mp
    change h.streetWeakEquivalences (h.posetMap (OrderHom.id : P →o P))
    rw [h.posetMap_id]
    exact h.streetWeakEquivalences.id_mem _

/-- The finite-poset unit input is proved here for every greatest-element
poset; finiteness is not needed in this case. -/
theorem unit_greatestElement (G : RightGrayInput h)
    (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] (x : P) (hx : ∀ y, y ≤ x) :
    realizationWeakEquivalences (h.categorificationAdjunction.unit.app (nerve P)) := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  exact (weak_component_iff realizationWeakEquivalences h.categorificationAdjunction.unit
    (nerveMap (posetFromPoint x).monotone.functor)
    (nerve_greatest_point_weakEquivalences kq x hx).1
    (h.categorified_greatest_point_weakEquivalences G aw kq x hx).1).mp
      (h.unit_of_point_iso kq (SSet.stdSimplex.isoNerve 0))

end NormalizedSimplexIdentities

end Thomason.Construction

end

section

/-! # Greatest-element unit comparisons in every positive finite dimension

Terminality of the reflected point follows from the fully faithful inclusion
and its counit. The finite prism then gives the same weak-equivalence bridge
as in omega dimension, without assuming that inclusion preserves colimits.
-/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory
open scoped Simplicial

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The zero-dimensional oriental is terminal also in the full finite category. -/
noncomputable def finitePoint : Truncated (n + 1) :=
  ⟨h.object 0, fun x => (h.object 0).dimensionLE_mono (Nat.zero_le _) (h.isTruncated 0 x)⟩

noncomputable def finitePoint_isTerminal : IsTerminal ((finitePoint (n := n) h)) := by
  apply IsTerminal.ofUniqueHom (X := (finitePoint (n := n) h))
    (fun X => h.object_zero_isTerminal.from X.val)
  intro X f
  exact h.object_zero_isTerminal.hom_ext f (h.object_zero_isTerminal.from X.val)

/-- The actual composite adjunction has an isomorphic unit on the point. -/
theorem unit_point_isIso : IsIso ((r.categorificationAdjunction h).unit.app (Δ[0])) := by
  have := (r.categorificationAdjunction h).rightAdjoint_preservesLimits
  have he : IsIso (C := Truncated (n + 1)) (r.adjunction.counit.app ((finitePoint (n := n) h))) := inferInstance
  let e₀ : r.reflect.obj ((finitePoint (n := n) h).val) ≅ finitePoint (n := n) h :=
    @asIso (Truncated (n + 1)) _ _ _ (r.adjunction.counit.app (finitePoint (n := n) h)) he
  let e : (r.categorification h).obj (Δ[0]) ≅ (finitePoint (n := n) h) :=
    r.reflect.mapIso (h.categorificationSimplexIso.app (.mk 0)) ≪≫
      e₀
  have ht : IsTerminal ((r.categorification h).obj (Δ[0])) :=
    (finitePoint_isTerminal (n := n) h).ofIso e.symm
  exact isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀
    (ht.isTerminalObj (h.finiteStreetNerve (n + 1)) _) _

theorem unit_of_point_iso (kq : KanQuillenPublishedInput.{0})
    {X : SSet.{0}} (e : (Δ[0] : SSet.{0}) ≅ X) :
    realizationWeakEquivalences ((r.categorificationAdjunction h).unit.app X) := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  have := kq.weakEquivalences_retracts
  have := r.unit_point_isIso h
  exact (weak_component_iff realizationWeakEquivalences (r.categorificationAdjunction h).unit
    e.hom (realizationWeakEquivalences.of_isIso _)
    (realizationWeakEquivalences.of_isIso _)).mp
      (realizationWeakEquivalences.of_isIso _)

/-- Reflection of the strict contraction gives actual finite Street weak
equivalences on both the point inclusion and the collapse. -/
theorem categorified_greatest_point_weakEquivalences
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] (x : P) (hx : ∀ y, y ≤ x) :
    realizationWeakEquivalences ((h.finiteStreetNerve (n + 1)).map
      (r.reflect.map (h.posetMap (posetFromPoint x)))) ∧
    realizationWeakEquivalences ((h.finiteStreetNerve (n + 1)).map
      (r.reflect.map (h.posetMap (posetToPoint P)))) := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  have := kq.weakEquivalences_retracts
  let F := h.categorification ⋙ r.reflect ⋙ h.finiteStreetNerve (n + 1)
  apply retraction_weakEquivalences realizationWeakEquivalences
  · change F.map (nerveMap (posetFromPoint x).monotone.functor) ≫
      F.map (nerveMap (posetToPoint P).monotone.functor) = 𝟙 _
    rw [← F.map_comp, ← orderNerveMap_comp, poset_point_retraction,
      orderNerveMap_id, F.map_id]
  · change realizationWeakEquivalences (F.map (nerveMap (posetToPoint P).monotone.functor) ≫
      F.map (nerveMap (posetFromPoint x).monotone.functor))
    rw [← F.map_comp, ← orderNerveMap_comp]
    apply ((greatestElementPrism x hx).finite_weakEquivalence_iff h G t r aw kq).mp
    change realizationWeakEquivalences (F.map (nerveMap (OrderHom.id : P →o P).monotone.functor))
    rw [orderNerveMap_id, F.map_id]
    exact realizationWeakEquivalences.id_mem _

/-- The actual unit comparison is weak on all greatest-element posets in
dimension n+1. No finite-poset unit theorem is used. -/
theorem unit_greatestElement
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] (x : P) (hx : ∀ y, y ≤ x) :
    realizationWeakEquivalences ((r.categorificationAdjunction h).unit.app (nerve P)) := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  exact (weak_component_iff realizationWeakEquivalences (r.categorificationAdjunction h).unit
    (nerveMap (posetFromPoint x).monotone.functor)
    (nerve_greatest_point_weakEquivalences kq x hx).1
    (r.categorified_greatest_point_weakEquivalences h G t aw kq x hx).1).mp
      (r.unit_of_point_iso h kq (SSet.stdSimplex.isoNerve 0))

end Thomason.Construction.FiniteReflectionInput

end

section

/-! # The actual unit on the empty poset

The object equivalence for categorified poset nerves rules out all cells
when the poset is empty. Hence both sides of the unit are empty in every
simplicial degree, including after finite reflection.
-/

namespace Thomason.Construction

open CategoryTheory StrictOmegaCategory Opposite

private theorem isIso_of_empty_levels {X Y : SSet.{0}} (f : X ⟶ Y)
    (hx : ∀ m, IsEmpty (X.obj m)) (hy : ∀ m, IsEmpty (Y.obj m)) : IsIso f := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro m
  rw [isIso_iff_bijective]
  constructor
  · intro x
    exact (hx m).false x |>.elim
  · intro y
    exact (hy m).false y |>.elim

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The omega-dimensional unit on an empty poset is an isomorphism. -/
theorem unit_empty_isIso (P : Type) [PartialOrder P] [IsEmpty P] :
    IsIso (h.categorificationAdjunction.unit.app (nerve P)) := by
  apply isIso_of_empty_levels
  · intro m
    exact ⟨fun s => isEmptyElim (s.obj 0)⟩
  · intro m
    refine ⟨fun f => ?_⟩
    let x := f.toFun (SimplexComplex.vertex h 0)
    exact isEmptyElim (h.posetObjectsEquiv P
      ((h.categorification.obj (nerve P)).boundaryObject false x))

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Empty posets remain empty under the actual finite categorification. -/
theorem unit_empty_isIso (P : Type) [PartialOrder P] [IsEmpty P] :
    IsIso ((r.categorificationAdjunction h).unit.app (nerve P)) := by
  apply isIso_of_empty_levels
  · intro m
    exact ⟨fun s => isEmptyElim (s.obj 0)⟩
  · intro m
    refine ⟨fun f => ?_⟩
    let x := f.toFun (SimplexComplex.vertex h 0)
    exact isEmptyElim (r.posetObjectsEquiv h P
      (((r.categorification h).obj (nerve P)).val.boundaryObject false x))

end FiniteReflectionInput
end Thomason.Construction

end

section

/-! # Filtered colimits preserve a uniform finite dimension bound

The ordinary strict filtered colimit remains truncated because every cell
comes from a single stage. Thus the actual full-subcategory inclusion
preserves filtered colimits.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory CategoryTheory.Limits

namespace TruncatedFilteredColimit

variable {J : Type} [Category.{0} J] [IsFiltered J] (n : ℕ)
    (F : J ⥤ Truncated.{0} n)

theorem isTruncated :
    (FilteredColimit.category (F ⋙ inclusion n)).IsTruncated n := by
  intro x
  obtain ⟨j, y, rfl⟩ := FilteredColimit.exists_representative (F ⋙ inclusion n) x
  constructor
  · change FilteredColimit.face (F ⋙ inclusion n) false n
      (FilteredColimit.ι (F ⋙ inclusion n) j y) = _
    rw [FilteredColimit.face_ι]
    exact congrArg (FilteredColimit.ι (F ⋙ inclusion n) j) ((F.obj j).property y).1
  · change FilteredColimit.face (F ⋙ inclusion n) true n
      (FilteredColimit.ι (F ⋙ inclusion n) j y) = _
    rw [FilteredColimit.face_ι]
    exact congrArg (FilteredColimit.ι (F ⋙ inclusion n) j) ((F.obj j).property y).2

noncomputable def cocone : Cocone F where
  pt := ⟨FilteredColimit.category (F ⋙ inclusion n), isTruncated n F⟩
  ι := {
    app j := FilteredColimit.leg (F ⋙ inclusion n) j
    naturality _j _k f := (FilteredColimit.cocone (F ⋙ inclusion n)).w f }

noncomputable def underlyingIsColimit :
    IsColimit ((inclusion n).mapCocone (cocone n F)) :=
  FilteredColimit.isColimit (F ⋙ inclusion n)

noncomputable def isColimit : IsColimit (cocone n F) :=
  isColimitOfReflects (inclusion n) (underlyingIsColimit n F)

end TruncatedFilteredColimit

instance inclusion_preservesFilteredColimitsOfShape {J : Type} [Category.{0} J]
    [IsFiltered J] (n : ℕ) : PreservesColimitsOfShape J (inclusion.{0} n) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone
    (TruncatedFilteredColimit.isColimit n F)
    (TruncatedFilteredColimit.underlyingIsColimit n F)

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Local finite presentability in every finite strict dimension

Intelligent truncation is left adjoint to the fully faithful inclusion.
That inclusion preserves filtered colimits by the cell construction, so
the existing adjunction criterion applies to the proved omega-dimensional
local finite presentability.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance inclusion_preservesFilteredColimits (n : ℕ) :
    PreservesFilteredColimitsOfSize.{0,0} (inclusion.{0} n) where
  preserves_filtered_colimits _J := inferInstance

instance inclusion_finitelyAccessible (n : ℕ) :
    (inclusion.{0} n).IsFinitelyAccessible.{0} :=
  Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.mpr inferInstance

instance truncated_locallyFinitelyPresentable (n : ℕ) :
    IsCardinalLocallyPresentable.{0} (Truncated.{0} n) Cardinal.aleph0 :=
  (IntelligentTruncation.adjunction n).isCardinalLocallyPresentable Cardinal.aleph0

instance truncated_locallyPresentable (n : ℕ) :
    IsLocallyPresentable.{0} (Truncated.{0} n) where
  exists_cardinal := ⟨Cardinal.aleph0, inferInstance, inferInstance⟩

/-- The reflected finite globes are finitely presentable in finite dimension. -/
instance truncated_globe_finitelyPresentable (n k : ℕ) :
    IsFinitelyPresentable.{0} ((IntelligentTruncation.functor n).obj (Globe.category k)) :=
  (IntelligentTruncation.adjunction n).isCardinalPresentable_leftAdjoint_obj
    Cardinal.aleph0 (Globe.category k)

end Thomason.Construction.StrictOmegaCategory

end

end OAI
