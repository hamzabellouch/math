import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Simplicial.ExhaustionWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Strict.StrictPosetWeakEquivalences
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor

namespace OAI

section

/-! # Intelligent finite reflection

The quotient of bounded cells gives the reflection adjunction of
Ara–Maltsiniotis (2014), §5.8.
-/

namespace Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

open CategoryTheory

noncomputable def functor (n : ℕ) : StrictOmegaCategory.{0} ⥤ Truncated.{0} n where
  obj C := ⟨category C n, isTruncated C n⟩
  map {C D} f := descend (isTruncated D n) (f ≫ unit D n)
  map_id C := by
    apply unit_hom_ext (C := C) (n := n)
    change unit C n ≫ descend (isTruncated C n) ((𝟙 C) ≫ unit C n) =
      unit C n ≫ (𝟙 (category C n))
    rw [unit_descend, Category.id_comp, Category.comp_id]
  map_comp {C D E} f g := by
    apply unit_hom_ext (C := C) (n := n)
    change unit C n ≫ descend (isTruncated E n) ((f ≫ g) ≫ unit E n) =
      unit C n ≫ (descend (isTruncated D n) (f ≫ unit D n) ≫
        descend (isTruncated E n) (g ≫ unit E n))
    rw [unit_descend]
    symm
    rw [← Category.assoc, unit_descend, Category.assoc, unit_descend]
    exact (Category.assoc f g (unit E n)).symm

/-- The projection is natural on all original strict cells. -/
theorem unit_naturality (n : ℕ) {C D : StrictOmegaCategory.{0}} (f : C ⟶ D) :
    unit C n ≫ (functor n).map f = f ≫ unit D n := unit_descend _ _

noncomputable def homEquiv (n : ℕ) (C : StrictOmegaCategory.{0}) (D : Truncated.{0} n) :
    ((functor n).obj C ⟶ D) ≃ (C ⟶ D.val) where
  toFun f := unit C n ≫ f
  invFun g := descend D.property g
  left_inv f := (descend_unique D.property (unit C n ≫ f) f rfl).symm
  right_inv g := unit_descend D.property g

/-- The explicit intelligent-truncation / inclusion adjunction. -/
noncomputable def adjunction (n : ℕ) : functor n ⊣ inclusion n :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv n
      homEquiv_naturality_left_symm := by
        intro C' C D f g
        change C ⟶ D.val at g
        apply unit_hom_ext (C := C') (n := n)
        change unit C' n ≫ descend D.property (f ≫ g) =
          unit C' n ≫ (descend (isTruncated C n) (f ≫ unit C n) ≫ descend D.property g)
        rw [unit_descend, ← Category.assoc, unit_descend, Category.assoc, unit_descend]
      homEquiv_naturality_right := by
        intro C D E f g
        exact (Category.assoc (unit C n) f g).symm }

end Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

namespace Thomason.Construction

/-- Positive finite reflection, obtained from the quotient universal property. -/
noncomputable def constructedFiniteReflection (n : ℕ) : FiniteReflectionInput n where
  reflect := StrictOmegaCategory.IntelligentTruncation.functor (n+1)
  adjunction := StrictOmegaCategory.IntelligentTruncation.adjunction (n+1)

end Thomason.Construction

end

section

/-! # Cell topology and lifting for actual strict Street inclusions -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory Convexity Opposite HomotopicalAlgebra StrictOmegaCategory
open RealizationPrism
open scoped Simplicial

noncomputable section

variable (h : NormalizedSimplexIdentities) (C : StrictOmegaCategory.{0})

/-- A strict full inclusion has an actual relative barycentric cell
    presentation on Street realizations. -/
def fullStreetCellComplex (S : Set C) :
    RelativeCellComplex.{0} barycentricBoundaryCell
      (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S))) :=
  barycentricCellComplexOfMono _

theorem fullStreet_realized_range (S : Set C) :
    Set.range (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S))).hom =
      Set.range (SSet.toTop.map (h.fullStreetSubcomplex C S).ι).hom := by
  have he := congrArg SSet.toTop.map (h.fullStreetIso_hom_ι C S)
  rw [SSet.toTop.map_comp] at he
  let e := TopCat.homeoOfIso (SSet.toTop.mapIso (h.fullStreetIso C S))
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e y, ConcreteCategory.congr_hom he y⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := e.surjective y
    exact ⟨z, (ConcreteCategory.congr_hom he z).symm⟩

/-- A point in a Street simplex interior lies in a full strict realization
    exactly when all cells of that strict simplex lie in the full subcategory. -/
theorem fullStreet_interior_iff (S : Set C) {n : ℕ}
    (s : (h.streetNerve.obj C).obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (n+1))) (hx : x ∈ fullSupport n) :
    simplexPoint (h.streetNerve.obj C) s x ∈
        Set.range (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S))).hom ↔
      ∀ a, C.FullCell S (s.toFun a) := by
  rw [h.fullStreet_realized_range C S]
  exact interior_mem_subcomplex_iff (h.streetNerve.obj C) (h.fullStreetSubcomplex C S) s x hx

/-- The concrete barycentric boundary lifting property suffices to extend
    continuous maps across every full strict Street inclusion. -/
theorem fullStreet_topological_lifting (S : Set C) {X Y : TopCat.{0}} (p : X ⟶ Y)
    (hp : ∀ n, HasLiftingProperty (boundaryInclusion n) p) :
    HasLiftingProperty (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S))) p :=
  realization_mono_lifting p hp _

end

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Continuous extension of full Street and Gray homotopies -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory StrictOmegaCategory
open scoped Simplicial

noncomputable section

variable (h : NormalizedSimplexIdentities) (C : StrictOmegaCategory.{0})

/-- A homotopy on a full strict higher subcategory extends over the entire
actual Street realization, with its restriction retained pointwise. -/
theorem fullStreet_homotopy_extension (S : Set C) {X : TopCat.{0}}
    (f : SSet.toTop.obj (h.streetNerve.obj C) ⟶ X)
    {g : SSet.toTop.obj (h.streetNerve.obj (C.fullOn S)) ⟶ X}
    (H : (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S)) ≫ f).hom.Homotopy g.hom) :
    ∃ (g' : SSet.toTop.obj (h.streetNerve.obj C) ⟶ X)
      (H' : f.hom.Homotopy g'.hom),
      ∀ t x, H' (t, (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S))).hom x) =
        H (t, x) :=
  realization_homotopy_extension_endpoint (h.streetNerve.map (C.fullInclusion S)) f H

/-- A prescribed full-subcategory Gray homotopy extends continuously over the
ambient Street realization. The endpoint keeps the actual weak test of the
initial strict functor. No strict ambient Gray extension is asserted. -/
theorem fullStreet_gray_homotopy_extension (S : Set C)
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    {D : StrictOmegaCategory.{0}} (f : C ⟶ D)
    (P : G.cylinder.obj (C.fullOn S) ⟶ D)
    (h₀ : (G.endpoint false).app (C.fullOn S) ≫ P = C.fullInclusion S ≫ f) :
    ∃ (g' : SSet.toTop.obj (h.streetNerve.obj C) ⟶
        SSet.toTop.obj (h.streetNerve.obj D))
      (H' : (SSet.toTop.map (h.streetNerve.map f)).hom.Homotopy g'.hom),
      (∀ t x,
        H' (t, (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S))).hom x) =
          G.realizedHomotopy aw P (t, x)) ∧
      (h.streetWeakEquivalences f ↔ IsWeakHomotopyEquivalence g'.hom) := by
  let H : (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S)) ≫
      SSet.toTop.map (h.streetNerve.map f)).hom.Homotopy
        (SSet.toTop.map (h.streetNerve.map ((G.endpoint true).app (C.fullOn S) ≫ P))).hom :=
    (G.realizedHomotopy aw P).cast
      (by simp only [h₀, h.streetNerve.map_comp, SSet.toTop.map_comp]) rfl
  obtain ⟨g', H', hH'⟩ := h.fullStreet_homotopy_extension C S _ H
  refine ⟨g', H', ?_, isWeakHomotopyEquivalence_homotopy_iff H'⟩
  intro t x
  simpa only [H, ContinuousMap.Homotopy.cast_apply] using hH' t x

end

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Singular weak reflection for the Street nerve -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory

/-- Weak equivalence of the singular map of an actual Street realization
implies the original Thomason weak-equivalence test, without Gray or KQ inputs. -/
theorem streetWeak_of_singular_realization (h : NormalizedSimplexIdentities)
    {C D : StrictOmegaCategory.{0}} (f : C ⟶ D)
    (hf : realizationWeakEquivalences
      (TopCat.toSSet.map (SSet.toTop.map (h.streetNerve.map f)))) :
    h.streetWeakEquivalences f :=
  singular_realization_reflects_weak (SSet.toTop.map (h.streetNerve.map f)) hf

end Thomason.Construction.NormalizedSimplexIdentities

end

end OAI
