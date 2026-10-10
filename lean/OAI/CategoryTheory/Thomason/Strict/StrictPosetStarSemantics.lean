import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionAnodyneHorn
import OAI.CategoryTheory.Thomason.Simplicial.SieveFiberPresentation
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.TruncatedLocalPresentability
import OAI.CategoryTheory.Thomason.Strict.StrictPosetWeakEquivalences
import OAI.CategoryTheory.Thomason.Transfer.FiniteEmptyAttachmentFibers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

namespace OAI

section

/-! # Finite reflection of sieve comparisons

The canonical comparison is compatible with the actual reflected inclusion.
Consequently finite reflection transports the omega sieve isomorphism to
all finite-dimensional instances.
-/

namespace Thomason.Construction

open CategoryTheory StrictOmegaCategory

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The characteristic label in finite dimension descends the original label. -/
theorem membershipLabel_unit {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsLowerSet A) :
    r.adjunction.unit.app (h.categorification.obj (nerve P)) ≫ r.membershipLabel h A hA =
      h.membershipLabel A hA := by
  let u := r.adjunction.unit.app (h.categorification.obj (nerve P))
  let e := r.descendPosetLabel (h.posetEvaluation P)
  let b := StrictPoset.map (sieveCharacteristic A hA)
  change u ≫ (e ≫ b) = h.posetEvaluation P ≫ b
  exact (Category.assoc u e b).symm.trans
    (congrArg (fun k => k ≫ b) (r.descendPosetLabel_fac (h.posetEvaluation P)))

/-- The finite canonical sieve map is exactly the reflected omega map
followed by the canonical zero-fibre comparison. -/
theorem posetFiberMap_eq_reflect {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsLowerSet A) :
    r.posetFiberMap h A hA = r.reflect.map (h.posetFiberMap A hA) ≫
      r.zeroFiberComparison (h.membershipLabel A hA) (r.membershipLabel h A hA)
        (r.membershipLabel_unit h A hA) := by
  let C : StrictOmegaCategory := h.categorification.obj (nerve A)
  let p := h.membershipLabel A hA
  let q := r.membershipLabel h A hA
  let hq := r.membershipLabel_unit h A hA
  let Q := r.reflectedLabelFiber q
  let f : C ⟶ labelFiber p 0 := h.posetFiberMap A hA
  let c := r.zeroFiberComparison p q hq
  let v : labelFiber p 0 ⟶ Q.val := r.zeroFiberUnit p q hq
  have hleft : r.adjunction.unit.app C ≫ r.posetFiberMap h A hA = f ≫ v := by
    apply Hom.ext
    funext x
    apply Subtype.ext
    exact congrArg (fun k : C ⟶ (r.reflect.obj (h.categorification.obj (nerve P))).val =>
      k.toFun x) (r.adjunction.unit.naturality (h.posetMap (subposetInclusion A))).symm
  let R := r.reflect.obj (labelFiber p 0)
  let cr : R.val ⟶ Q.val := c
  let fr : (r.reflect.obj C).val ⟶ R.val := r.reflect.map f
  let u : labelFiber p 0 ⟶ R.val := r.adjunction.unit.app (labelFiber p 0)
  let uC : C ⟶ (r.reflect.obj C).val := r.adjunction.unit.app C
  have hc : u ≫ cr = v := r.zeroFiberComparison_fac p q hq
  have hn : f ≫ u = uC ≫ fr := r.adjunction.unit.naturality f
  apply r.unit_hom_ext C Q
  change uC ≫ r.posetFiberMap h A hA = uC ≫ (fr ≫ cr)
  have hright : uC ≫ (fr ≫ cr) = f ≫ v :=
    (Category.assoc uC fr cr).symm.trans
      ((congrArg (fun k : C ⟶ R.val => k ≫ cr) hn.symm).trans
        ((Category.assoc f u cr).trans
          (congrArg (fun k : labelFiber p 0 ⟶ Q.val => f ≫ k) hc)))
  exact hleft.trans hright.symm

/-- Finite reflection preserves the sieve comparison isomorphism. -/
theorem posetFiberMap_isIso_of_omega {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsLowerSet A) [IsIso (h.posetFiberMap A hA)] :
    IsIso (C := Truncated (n + 1)) (r.posetFiberMap h A hA) := by
  rw [r.posetFiberMap_eq_reflect h A hA]
  exact IsIso.comp_isIso'
    (inferInstanceAs (IsIso (r.reflect.map (h.posetFiberMap A hA))))
    (r.zeroFiberComparison_isIso (h.membershipLabel A hA)
      (r.membershipLabel h A hA) (r.membershipLabel_unit h A hA))

end FiniteReflectionInput

/-- The omega-category specialization of AM2014 Proposition 5.5,
Lemma 5.12 and Proposition 5.13(c), for finite posets. -/
structure PublishedOmegaPosetSieveInput (h : NormalizedSimplexIdentities)
    [StrictColimitsInput] : Prop where
  omega {P : Type} [PartialOrder P] [Finite P] (A : Set P) (hA : IsLowerSet A) :
    IsIso (h.posetFiberMap A hA)

/-- Recover all positive finite cases using the constructed compatibility. -/
theorem PublishedOmegaPosetSieveInput.allDimensions
    {h : NormalizedSimplexIdentities} [StrictColimitsInput]
    (s : PublishedOmegaPosetSieveInput h) : PublishedPosetSieveInput h where
  omega := s.omega
  finite n r := by
    intro P _ _ A hA
    have := s.omega A hA
    exact r.posetFiberMap_isIso_of_omega h A hA

end Thomason.Construction

end

section

/-! # Actual Street and Thomason nerve pullback comparisons

The constructed finite limits exist in every category under consideration.
The genuine right adjunctions identify their canonical nerve comparisons
with simplicial pullbacks. No transferred model structure is used.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable (h : NormalizedSimplexIdentities)

/-- The original Street nerve preserves the actual finite limits. -/
theorem streetNerve_preservesFiniteLimits : PreservesFiniteLimits h.streetNerve := by
  have := h.categorificationAdjunction.rightAdjoint_preservesLimits
  infer_instance

/-- Its canonical comparison with a simplicial pullback is an isomorphism. -/
theorem streetNerve_pullbackComparison_isIso
    {X Y Z : StrictOmegaCategory.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsIso (pullbackComparison h.streetNerve f g) := by
  have := h.streetNerve_preservesFiniteLimits
  infer_instance

/-- The same comparison is an isomorphism for the actual Thomason right adjoint. -/
theorem thomasonRight_pullbackComparison_isIso
    {X Y Z : StrictOmegaCategory.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsIso (pullbackComparison h.thomasonRight f g) := by
  have := h.thomasonAdjunction.rightAdjoint_preservesLimits
  infer_instance

/-- The finite Street nerve preserves the finite-category pullback itself. -/
theorem finiteStreetNerve_pullbackComparison_isIso (n : ℕ)
    {X Y Z : Truncated.{0} (n+1)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsIso (pullbackComparison (h.finiteStreetNerve (n+1)) f g) := by
  have := ((constructedFiniteReflection n).categorificationAdjunction h).rightAdjoint_preservesLimits
  infer_instance

/-- Twice extension preserves that actual finite-category pullback as well. -/
theorem finiteThomasonRight_pullbackComparison_isIso (n : ℕ)
    {X Y Z : Truncated.{0} (n+1)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsIso (pullbackComparison (h.finiteStreetNerve (n+1) ⋙ SSet.ex ⋙ SSet.ex) f g) := by
  have := ((constructedFiniteReflection n).thomasonAdjunction h).rightAdjoint_preservesLimits
  infer_instance

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Actual Street homotopies for ordered strict poset labels

The source is an arbitrary strict omega-category and the target is thin.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory MonoidalCategory StrictOmegaCategory
open scoped Simplicial

noncomputable section

variable (h : NormalizedSimplexIdentities)
variable {C : StrictOmegaCategory.{0}} {P : Type} [PartialOrder P]
variable (f g : C ⟶ StrictPoset.category P)
variable (hfg : ∀ x : Objects C, (f.toFun x.val).first ≤ (g.toFun x.val).first)

include hfg

theorem strictLabel_vertex_le
    (v : (h.streetNerve.obj C).obj (.op (.mk 0))) :
    ((h.streetNerve.map f ≫ h.strictPosetNerveMap P).app (.op (.mk 0)) v).obj 0 ≤
      ((h.streetNerve.map g ≫ h.strictPosetNerveMap P).app (.op (.mk 0)) v).obj 0 := by
  exact hfg (v.toOneFunctor.obj ((SimplexComplex.objectsEquiv h 0).symm 0))

/-- Ordered object labels give a constructed homotopy of the actual Street nerves. -/
def strictLabelHomotopy : SSet.Homotopy (h.streetNerve.map f) (h.streetNerve.map g) := by
  let e := h.strictPosetNerveIso P
  let H := PosetGeometry.orderedVertexHomotopy
    (h.streetNerve.map f ≫ e.hom) (h.streetNerve.map g ≫ e.hom)
    (h.strictLabel_vertex_le f g hfg)
  exact {
    h := H.h ≫ e.inv
    h₀ := by rw [← Category.assoc, H.h₀]; simp
    h₁ := by rw [← Category.assoc, H.h₁]; simp
    rel := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }

/-- The actual Street weak-equivalence test is invariant under ordered
    labels out of any strict higher category. -/
theorem strictLabel_weak_iff : h.streetWeakEquivalences f ↔ h.streetWeakEquivalences g :=
  RealizedCylinder.weakEquivalence_iff (h.strictLabelHomotopy f g hfg)

end

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Relative stationarity of Street homotopies between ordered labels -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory MonoidalCategory CartesianMonoidalCategory StrictOmegaCategory
open scoped Simplicial

noncomputable section

variable (h : NormalizedSimplexIdentities)
variable {C D : StrictOmegaCategory.{0}} {P : Type} [PartialOrder P]
variable (f g : C ⟶ StrictPoset.category P)
variable (hfg : ∀ x : Objects C, (f.toFun x.val).first ≤ (g.toFun x.val).first)

/-- Equality of the labels on a strict subdiagram gives exact stationarity
    on its entire Street cylinder, in every dimension. -/
theorem strictLabelHomotopy_stationary (i : D ⟶ C) (hi : i ≫ f = i ≫ g) :
    h.streetNerve.map i ▷ Δ[1] ≫ (h.strictLabelHomotopy f g hfg).h =
      fst (h.streetNerve.obj D) Δ[1] ≫ h.streetNerve.map i ≫ h.streetNerve.map f := by
  let e := h.strictPosetNerveIso P
  let a := h.streetNerve.map f ≫ e.hom
  let b := h.streetNerve.map g ≫ e.hom
  have hab : h.streetNerve.map i ≫ a = h.streetNerve.map i ≫ b := by
    dsimp [a, b]
    rw [← Category.assoc, ← Category.assoc, ← h.streetNerve.map_comp,
      ← h.streetNerve.map_comp, hi]
  change h.streetNerve.map i ▷ Δ[1] ≫
    ((PosetGeometry.orderedVertexHomotopy a b (h.strictLabel_vertex_le f g hfg)).h ≫ e.inv) = _
  rw [← Category.assoc]
  exact (congrArg (fun k => k ≫ e.inv)
    (PosetGeometry.orderedVertexHomotopy_stationary a b
      (h.strictLabel_vertex_le f g hfg) (h.streetNerve.map i) hab)).trans (by
        simp only [a, Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- The realized ordered-label homotopy fixes the entire realized image
    of the equal-label subdiagram, with its actual topology. -/
def strictLabelRealizedHomotopyRel (i : D ⟶ C) (hi : i ≫ f = i ≫ g) :
    (SSet.toTop.map (h.streetNerve.map f)).hom.HomotopyRel
      (SSet.toTop.map (h.streetNerve.map g)).hom
      (Set.range (SSet.toTop.map (h.streetNerve.map i)).hom) :=
  RealizedCylinder.homotopyRelOfStationary (h.strictLabelHomotopy f g hfg)
    (h.streetNerve.map i) (h.strictLabelHomotopy_stationary f g hfg i hi)

end

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Contractible Street charts and their actual singular comparison

These results concern the strict-poset local models used in the Thomason
construction. They do not assert local contractibility of arbitrary Street
vertex stars or supply an unproved global Kan--Quillen comparison.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory Opposite RealizationPrism
open scoped Simplicial

noncomputable section

variable (h : NormalizedSimplexIdentities) (P : Type) [PartialOrder P]

/-- Every vertex star of the actual Street nerve of a strict poset is
    contractible in its actual realization topology. -/
theorem strictPoset_vertexStar_contractible
    (v : (h.streetNerve.obj (StrictPoset.category P)).obj (.op (.mk 0))) :
    ContractibleSpace (vertexStar (h.streetNerve.obj (StrictPoset.category P)) v) := by
  let e := h.strictPosetNerveIso P
  let u := e.hom.app (.op (.mk 0)) v
  have hu : u = PosetGeometry.vertex (u.obj 0) := (PosetGeometry.eq_vertex_iff _ _).mpr rfl
  let : ContractibleSpace (vertexStar (nerve P) u) := by
    rw [hu]
    exact PosetGeometry.vertexStar_contractible _
  exact (isoVertexStarHomeomorph e v).contractibleSpace

/-- On these Street charts, evaluation from the realized singular set
    satisfies the full actual weak-homotopy-equivalence test. -/
theorem strictPoset_vertexStar_singular_counit_weak
    (v : (h.streetNerve.obj (StrictPoset.category P)).obj (.op (.mk 0))) :
    topologicalWeakEquivalences (sSetTopAdj.counit.app
      (TopCat.of (vertexStar (h.streetNerve.obj (StrictPoset.category P)) v))) := by
  let := h.strictPoset_vertexStar_contractible P v
  exact singular_counit_weak_contractible _

/-- Compact cube maps into strict-poset Street realizations have a finite
    grid controlled by charts with proved singular weak equivalences. -/
theorem strictPoset_cube_grid_singular_comparison (n : ℕ)
    (f : C((Fin n → unitInterval), SSet.toTop.obj (h.streetNerve.obj (StrictPoset.category P)))) :
    ∃ m : ℕ, ∀ k : Fin n → Fin (m+1),
      ∃ v : (h.streetNerve.obj (StrictPoset.category P)).obj (.op (.mk 0)),
        (∀ x ∈ CubeGrid.cell n m k,
          f x ∈ vertexStar (h.streetNerve.obj (StrictPoset.category P)) v) ∧
        topologicalWeakEquivalences (sSetTopAdj.counit.app
          (TopCat.of (vertexStar (h.streetNerve.obj (StrictPoset.category P)) v))) := by
  obtain ⟨m, hm⟩ := cube_grid_vertexStar_refinement _ n f
  exact ⟨m, fun k => by
    obtain ⟨v, hv⟩ := hm k
    exact ⟨v, hv, h.strictPoset_vertexStar_singular_counit_weak P v⟩⟩

end

end Thomason.Construction.NormalizedSimplexIdentities

end

end OAI
