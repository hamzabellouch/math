import OAI.CategoryTheory.Thomason.Gray.GrayChainGlobeRestriction
import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Gray.TopologicalConePrism
import OAI.CategoryTheory.Thomason.Transfer.StrictPushoutGeneration
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge

namespace OAI

section

/-! # Stationary zigzag retractions across finite-dimensional pushouts -/

namespace Thomason.Construction.RightGrayInput

open CategoryTheory

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  (t : GrayTruncationInput G) {n : ℕ}
  (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0})

include t aw kq

/-- The finite-dimensional gluing theorem uses the finite pushout itself,
without assuming the ambient inclusion preserves it. -/
theorem finite_stationary_zigzag_pushout_weakEquivalence
    {A B X Y : StrictOmegaCategory.Truncated.{0} (n + 1)}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (P Q : G.cylinder.obj B.val ⟶ B.val)
    (hP : G.cylinder.map i ≫ P = G.projection.app A.val ≫ i)
    (hQ : G.cylinder.map i ≫ Q = G.projection.app A.val ≫ i)
    (hP₀ : (G.endpoint false).app B.val ≫ P = 𝟙 B.val)
    (hPQ : (G.endpoint true).app B.val ≫ P = (G.endpoint true).app B.val ≫ Q)
    (hQ₀ : (G.endpoint false).app B.val ≫ Q =
      (StrictOmegaCategory.inclusion (n + 1)).map r ≫ (StrictOmegaCategory.inclusion (n + 1)).map i) :
    h.streetWeakEquivalences ((StrictOmegaCategory.inclusion (n + 1)).map j) := by
  let ib : A.val ⟶ B.val := (StrictOmegaCategory.inclusion (n + 1)).map i
  let ab : A.val ⟶ X.val := (StrictOmegaCategory.inclusion (n + 1)).map a
  let bb : B.val ⟶ Y.val := (StrictOmegaCategory.inclusion (n + 1)).map b
  let jb : X.val ⟶ Y.val := (StrictOmegaCategory.inclusion (n + 1)).map j
  let rb : B.val ⟶ A.val := (StrictOmegaCategory.inclusion (n + 1)).map r
  have hw : ib ≫ bb = ab ≫ jb := hp.w
  obtain ⟨p, hbp, hjp⟩ := hp.exists_desc (r ≫ a) (𝟙 X) (by
    rw [← Category.assoc, hir]
    simp)
  let pb : Y.val ⟶ X.val := (StrictOmegaCategory.inclusion (n + 1)).map p
  have hbp' : bb ≫ pb = rb ≫ ab := hbp
  have hjp' : jb ≫ pb = 𝟙 X.val := hjp
  obtain ⟨U, _, _, huj, hub⟩ := G.glue_finite_stationary_cylinder t hp P hP
  obtain ⟨V, _, _, hvj, hvb⟩ := G.glue_finite_stationary_cylinder t hp Q hQ
  have hu₀ : (G.endpoint false).app Y.val ≫ U = 𝟙 Y.val := by
    apply hp.hom_ext
    · change bb ≫ ((G.endpoint false).app Y.val ≫ U) = bb ≫ 𝟙 Y.val
      exact (hub false).trans ((congrArg (fun f => f ≫ bb) hP₀).trans
        ((Category.id_comp bb).trans (Category.comp_id bb).symm))
    · change jb ≫ ((G.endpoint false).app Y.val ≫ U) = jb ≫ 𝟙 Y.val
      exact (huj false).trans (Category.comp_id jb).symm
  have huv : (G.endpoint true).app Y.val ≫ U = (G.endpoint true).app Y.val ≫ V := by
    apply hp.hom_ext
    · change bb ≫ ((G.endpoint true).app Y.val ≫ U) = bb ≫ ((G.endpoint true).app Y.val ≫ V)
      exact (hub true).trans ((congrArg (fun f => f ≫ bb) hPQ).trans (hvb true).symm)
    · change jb ≫ ((G.endpoint true).app Y.val ≫ U) = jb ≫ ((G.endpoint true).app Y.val ≫ V)
      exact (huj true).trans (hvj true).symm
  have hc : (rb ≫ ib) ≫ bb = bb ≫ (pb ≫ jb) := by
    rw [Category.assoc, hw, ← Category.assoc, ← hbp', Category.assoc]
  have hbV : bb ≫ ((G.endpoint false).app Y.val ≫ V) = bb ≫ (pb ≫ jb) :=
    (hvb false).trans ((congrArg (fun f : B.val ⟶ B.val => f ≫ bb) hQ₀).trans hc)
  have hjV : jb ≫ ((G.endpoint false).app Y.val ≫ V) = jb ≫ (pb ≫ jb) := by
    exact (hvj false).trans (((Category.id_comp jb).symm.trans
      (congrArg (fun f => f ≫ jb) hjp'.symm)).trans (Category.assoc _ _ _))
  have hv₀ : (G.endpoint false).app Y.val ≫ V = pb ≫ jb := hp.hom_ext hbV hjV
  have := kq.twoOutOfThree
  have := kq.weakEquivalences_retracts
  have : h.streetWeakEquivalences.ContainsIdentities :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).ContainsIdentities
  have : h.streetWeakEquivalences.IsStableUnderRetracts :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).IsStableUnderRetracts
  have huW : h.streetWeakEquivalences ((G.endpoint true).app Y.val ≫ U) := by
    have hc := G.cylinder_weakEquivalence_iff aw kq U
    rw [hu₀] at hc
    exact hc.mp (h.streetWeakEquivalences.id_mem Y.val)
  have hvW : h.streetWeakEquivalences (pb ≫ jb) := by
    have hc := G.cylinder_weakEquivalence_iff aw kq V
    rw [hv₀, ← huv] at hc
    exact hc.mpr huW
  have hr : RetractArrow jb (pb ≫ jb) :=
    { i := Arrow.homMk jb (𝟙 Y.val) (by simp [← Category.assoc, hjp'])
      r := Arrow.homMk pb (𝟙 Y.val) (by simp)
      retract := by apply Arrow.hom_ext <;> simp [hjp'] }
  exact MorphismProperty.of_retract hr hvW

end Thomason.Construction.RightGrayInput

end

section

/-!
# The greatest-new-element couniversality step in every positive dimension

The actual finite categorification functor and actual finite-category
pushout occur in the statement. The proof descends the constructed prisms
and uses the finite internal-hom gluing theorem.
-/

namespace Thomason.Construction.SieveRetraction

open CategoryTheory

variable {E : Type} [PartialOrder E] {A : Set E} (R : SieveRetraction A)
  {x : E} (hx : GreatestNew (A := A) x)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]
  (G : RightGrayInput h) (t : GrayTruncationInput G) {n : ℕ} (r : FiniteReflectionInput n)
  (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0})

include R hx G t aw kq

/-- Every finite-dimensional attaching pushout in the greatest-new-element
case is a Street weak equivalence. -/
theorem finite_greatest_new_pushout_weakEquivalence
    {X Y : StrictOmegaCategory.Truncated.{0} (n + 1)}
    {a : r.reflect.obj (h.categorification.obj (nerve A)) ⟶ X}
    {b : r.reflect.obj (h.categorification.obj (nerve E)) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j) :
    h.streetWeakEquivalences ((StrictOmegaCategory.inclusion (n + 1)).map j) := by
  let D := R.upperPrismData hx
  let D' := R.lowerPrismData hx
  let F := r.reflect ⋙ StrictOmegaCategory.inclusion (n + 1)
  let P := D.finitePrism h G t r
  let Q := D'.finitePrism h G t r
  have hir : r.reflect.map (h.posetMap (subposetInclusion A)) ≫
      r.reflect.map (h.posetMap (R.oldCollapseRetraction hx)) = 𝟙 _ :=
    (r.reflect.map_comp _ _).symm.trans
      ((congrArg r.reflect.map (R.oldCollapse_posetMap_retraction hx h).1).trans (r.reflect.map_id _))
  have hri : F.map (h.posetMap (R.oldCollapseRetraction hx)) ≫ F.map (h.posetMap (subposetInclusion A)) =
      F.map (h.posetMap (R.oldCollapse hx)) :=
    (F.map_comp _ _).symm.trans (congrArg F.map (R.oldCollapse_posetMap_retraction hx h).2)
  have hP₀ : (G.endpoint false).app _ ≫ P = 𝟙 _ :=
    (D.finitePrism_endpoint h G t r false).trans
      ((congrArg F.map (h.posetMap_id E)).trans (F.map_id _))
  have hPQ : (G.endpoint true).app _ ≫ P = (G.endpoint true).app _ ≫ Q :=
    (D.finitePrism_endpoint h G t r true).trans (D'.finitePrism_endpoint h G t r true).symm
  have hQ₀ : (G.endpoint false).app _ ≫ Q =
      F.map (h.posetMap (R.oldCollapseRetraction hx)) ≫ F.map (h.posetMap (subposetInclusion A)) :=
    (D'.finitePrism_endpoint h G t r false).trans hri.symm
  have hP : G.cylinder.map (F.map (h.posetMap (subposetInclusion A))) ≫ P =
      G.projection.app _ ≫ F.map (h.posetMap (subposetInclusion A)) := by
    have he : D.first.comp D.oldInclusion = subposetInclusion A := rfl
    exact (D.finitePrism_stationary h G t r).trans
      (congrArg (fun f => G.projection.app _ ≫ F.map (h.posetMap f)) he)
  have hQ : G.cylinder.map (F.map (h.posetMap (subposetInclusion A))) ≫ Q =
      G.projection.app _ ≫ F.map (h.posetMap (subposetInclusion A)) := by
    have he : D'.first.comp D'.oldInclusion = subposetInclusion A := by
      apply DFunLike.ext
      intro a
      exact R.oldCollapse_old hx a.property
    exact (D'.finitePrism_stationary h G t r).trans
      (congrArg (fun f => G.projection.app _ ≫ F.map (h.posetMap f)) he)
  exact G.finite_stationary_zigzag_pushout_weakEquivalence t aw kq hp
    (r.reflect.map (h.posetMap (R.oldCollapseRetraction hx))) hir P Q hP hQ hP₀ hPQ hQ₀

end Thomason.Construction.SieveRetraction

end

section

/-!
# Relative Gray zigzags give weak equivalences after every pushout

This is the homotopical gluing step for the greatest-new-element case.
It imposes no cofibrancy or injectivity assumptions on the attaching map.
-/

namespace Thomason.Construction.RightGrayInput

open CategoryTheory

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0})

include aw kq

/-- A stationary two-cylinder contraction makes every pushout of its
retract inclusion a Street-nerve weak equivalence. -/
theorem stationary_zigzag_pushout_weakEquivalence
    {A B X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (P Q : G.cylinder.obj B ⟶ B)
    (hP : G.cylinder.map i ≫ P = G.projection.app A ≫ i)
    (hQ : G.cylinder.map i ≫ Q = G.projection.app A ≫ i)
    (hP₀ : (G.endpoint false).app B ≫ P = 𝟙 B)
    (hPQ : (G.endpoint true).app B ≫ P = (G.endpoint true).app B ≫ Q)
    (hQ₀ : (G.endpoint false).app B ≫ Q = r ≫ i) :
    h.streetWeakEquivalences j := by
  obtain ⟨p, hbp, hjp⟩ := hp.exists_desc (r ≫ a) (𝟙 X) (by
    rw [← Category.assoc, hir]
    simp)
  obtain ⟨U, _, _, huj, hub⟩ := G.glue_stationary_cylinder hp P hP
  obtain ⟨V, _, _, hvj, hvb⟩ := G.glue_stationary_cylinder hp Q hQ
  have hu₀ : (G.endpoint false).app Y ≫ U = 𝟙 Y := by
    apply hp.hom_ext
    · exact (hub false).trans (by rw [hP₀]; simp)
    · simpa using huj false
  have huv : (G.endpoint true).app Y ≫ U = (G.endpoint true).app Y ≫ V := by
    apply hp.hom_ext
    · exact (hub true).trans ((congrArg (fun f => f ≫ b) hPQ).trans (hvb true).symm)
    · exact (huj true).trans (hvj true).symm
  have hv₀ : (G.endpoint false).app Y ≫ V = p ≫ j := by
    apply hp.hom_ext
    · calc
        _ = ((G.endpoint false).app B ≫ Q) ≫ b := hvb false
        _ = (r ≫ i) ≫ b := congrArg (fun f => f ≫ b) hQ₀
        _ = r ≫ (a ≫ j) := by rw [Category.assoc, hp.w]
        _ = (r ≫ a) ≫ j := (Category.assoc _ _ _).symm
        _ = (b ≫ p) ≫ j := congrArg (fun f => f ≫ j) hbp.symm
        _ = _ := Category.assoc _ _ _
    · calc
        _ = j := hvj false
        _ = (j ≫ p) ≫ j := by rw [hjp]; simp
        _ = _ := Category.assoc _ _ _
  have := kq.twoOutOfThree
  have := kq.weakEquivalences_retracts
  have : h.streetWeakEquivalences.ContainsIdentities :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).ContainsIdentities
  have : h.streetWeakEquivalences.IsStableUnderRetracts :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).IsStableUnderRetracts
  have huW : h.streetWeakEquivalences ((G.endpoint true).app Y ≫ U) := by
    have hc := G.cylinder_weakEquivalence_iff aw kq U
    rw [hu₀] at hc
    exact hc.mp (h.streetWeakEquivalences.id_mem Y)
  have hvW : h.streetWeakEquivalences (p ≫ j) := by
    have hc := G.cylinder_weakEquivalence_iff aw kq V
    rw [hv₀, ← huv] at hc
    exact hc.mpr huW
  have hr : RetractArrow j (p ≫ j) :=
    { i := Arrow.homMk j (𝟙 Y) (by simp [← Category.assoc, hjp])
      r := Arrow.homMk p (𝟙 Y) (by simp)
      retract := by apply Arrow.hom_ext <;> simp [hjp] }
  exact MorphismProperty.of_retract hr hvW

end Thomason.Construction.RightGrayInput

end

section

/-!
# Couniversality for a greatest new element

This proves the omega-dimensional greatest-new-element step of Section 5
using the constructed stationary prisms. Neither the attaching functor nor
the posets are assumed finite, injective, free, or cofibrant.
-/

namespace Thomason.Construction.SieveRetraction

open CategoryTheory

variable {E : Type} [PartialOrder E] {A : Set E} (R : SieveRetraction A)
  {x : E} (hx : GreatestNew (A := A) x)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput] (G : RightGrayInput h)
  (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0})

include R hx G aw kq

/-- Every pushout of this categorified sieve inclusion is an actual
Street-nerve weak equivalence. -/
theorem greatest_new_pushout_weakEquivalence {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve E) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j) :
    h.streetWeakEquivalences j := by
  obtain ⟨P, Q, hP₀, hP₁, hQ₀, hQ₁, hP, hQ⟩ := R.greatest_new_cylinders hx h G
  obtain ⟨hir, hri⟩ := R.oldCollapse_posetMap_retraction hx h
  exact G.stationary_zigzag_pushout_weakEquivalence aw kq hp
    (h.posetMap (R.oldCollapseRetraction hx)) hir P Q hP hQ hP₀
    (hP₁.trans hQ₁.symm) (hQ₀.trans hri.symm)

end Thomason.Construction.SieveRetraction

end

section

/-! # Gluing ordered atoms through their common piece

Two strict categories are generated by specified subsets of the atoms of
one ordered complex. Their subsets cover the target atoms, and every atom
in their intersection is the image of a cell in the common source. These
concrete data imply that their strict pushout is the positive-table
realization. No preservation of colimits by realization is assumed.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

/-- Atomic data for gluing two pieces. The overlap condition is an actual
common-source representative, rather than an equality assumed in the
unknown target pushout. -/
structure PushoutGluing {A C D : StrictOmegaCategory.{0}} (f : A ⟶ C) (g : A ⟶ D) where
  leftAtoms : Set B.AtomIndex
  rightAtoms : Set B.AtomIndex
  leftLift : leftAtoms → C
  rightLift : rightAtoms → D
  left : C ⟶ K.realization
  right : D ⟶ K.realization
  condition : f ≫ left = g ≫ right
  left_image (a : leftAtoms) : left.toFun (leftLift a) = B.atomCell a.val
  right_image (a : rightAtoms) : right.toFun (rightLift a) = B.atomCell a.val
  left_dimension (a : leftAtoms) : C.DimensionLE a.val.1 (leftLift a)
  right_dimension (a : rightAtoms) : D.DimensionLE a.val.1 (rightLift a)
  left_generated (x : C) : Nonempty (CompositionExpression C leftLift x)
  right_generated (x : D) : Nonempty (CompositionExpression D rightLift x)
  cover (a : B.AtomIndex) : a ∈ leftAtoms ∨ a ∈ rightAtoms
  overlap (a : B.AtomIndex) (hl : a ∈ leftAtoms) (hr : a ∈ rightAtoms) :
    ∃ z : A, f.toFun z = leftLift ⟨a, hl⟩ ∧ g.toFun z = rightLift ⟨a, hr⟩

namespace PushoutGluing

noncomputable section

variable {B} {A C D : StrictOmegaCategory.{0}} {f : A ⟶ C} {g : A ⟶ D}
variable (d : B.PushoutGluing f g)

abbrev Source (_d : B.PushoutGluing f g) : StrictOmegaCategory.{0} := pushout f g

abbrev Index := d.leftAtoms ⊕ d.rightAtoms

def label : d.Index → B.AtomIndex
  | .inl a => a.val
  | .inr a => a.val

def sourceLift : d.Index → d.Source
  | .inl a => (pushout.inl f g).toFun (d.leftLift a)
  | .inr a => (pushout.inr f g).toFun (d.rightLift a)

def comparison : d.Source ⟶ K.realization :=
  pushout.desc d.left d.right d.condition

theorem sourceLift_image (a : d.Index) :
    d.comparison.toFun (d.sourceLift a) = B.atomCell (d.label a) := by
  cases a with
  | inl a =>
    have h := congrArg (fun F => F.toFun (d.leftLift a))
      (pushout.inl_desc d.left d.right d.condition)
    exact h.trans (d.left_image a)
  | inr a =>
    have h := congrArg (fun F => F.toFun (d.rightLift a))
      (pushout.inr_desc d.left d.right d.condition)
    exact h.trans (d.right_image a)

theorem sourceLift_dimension (a : d.Index) :
    d.Source.DimensionLE (d.label a).1 (d.sourceLift a) := by
  cases a with
  | inl a => exact (pushout.inl f g).dimensionLE (d.left_dimension a)
  | inr a => exact (pushout.inr f g).dimensionLE (d.right_dimension a)

/-- Duplicate labels are identified by the given common-source cells. -/
theorem sourceLift_eq {a b : d.Index} (h : d.label a = d.label b) :
    d.sourceLift a = d.sourceLift b := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have he : a = b := Subtype.ext h
      exact congrArg (fun z => (pushout.inl f g).toFun (d.leftLift z)) he
    | inr b =>
      change a.val = b.val at h
      obtain ⟨z, hz, hw⟩ := d.overlap a.val a.property (h.symm ▸ b.property)
      have hb : (⟨a.val, h.symm ▸ b.property⟩ : d.rightAtoms) = b := Subtype.ext h
      have he := congrArg (fun F => F.toFun z) (pushout.condition (f := f) (g := g))
      change (pushout.inl f g).toFun (f.toFun z) =
        (pushout.inr f g).toFun (g.toFun z) at he
      rw [hz, hw, hb] at he
      exact he
  | inr a =>
    cases b with
    | inl b =>
      change a.val = b.val at h
      obtain ⟨z, hz, hw⟩ := d.overlap b.val b.property (h ▸ a.property)
      have ha : (⟨b.val, h ▸ a.property⟩ : d.rightAtoms) = a := Subtype.ext h.symm
      have he := congrArg (fun F => F.toFun z) (pushout.condition (f := f) (g := g))
      change (pushout.inl f g).toFun (f.toFun z) =
        (pushout.inr f g).toFun (g.toFun z) at he
      rw [hz, hw, ha] at he
      exact he.symm
    | inr b =>
      have he : a = b := Subtype.ext h
      exact congrArg (fun z => (pushout.inr f g).toFun (d.rightLift z)) he

def representative (a : B.AtomIndex) : d.Index := by
  classical
  exact if h : a ∈ d.leftAtoms then .inl ⟨a, h⟩
    else .inr ⟨a, (d.cover a).resolve_left h⟩

@[simp] theorem label_representative (a : B.AtomIndex) :
    d.label (d.representative a) = a := by
  unfold representative
  split <;> rfl

def atomLift (a : B.AtomIndex) : d.Source := d.sourceLift (d.representative a)

theorem atomLift_image (a : B.AtomIndex) :
    d.comparison.toFun (d.atomLift a) = B.atomCell a := by
  exact (d.sourceLift_image (d.representative a)).trans
    (congrArg B.atomCell (d.label_representative a))

theorem atomLift_dimension (a : B.AtomIndex) :
    d.Source.DimensionLE a.1 (d.atomLift a) := by
  change d.Source.DimensionLE a.1 (d.sourceLift (d.representative a))
  have h := d.sourceLift_dimension (d.representative a)
  simpa only [label_representative] using h

theorem sourceLift_eq_atomLift (a : d.Index) :
    d.sourceLift a = d.atomLift (d.label a) :=
  d.sourceLift_eq (d.label_representative (d.label a)).symm

theorem generated_left_image (x : C) :
    Nonempty (CompositionExpression d.Source d.atomLift ((pushout.inl f g).toFun x)) := by
  obtain ⟨t⟩ := d.left_generated x
  apply t.substitute (pushout.inl f g)
  intro a
  change Nonempty (CompositionExpression d.Source d.atomLift (d.sourceLift (.inl a)))
  rw [d.sourceLift_eq_atomLift]
  exact ⟨.generator (d.label (.inl a))⟩

theorem generated_right_image (x : D) :
    Nonempty (CompositionExpression d.Source d.atomLift ((pushout.inr f g).toFun x)) := by
  obtain ⟨t⟩ := d.right_generated x
  apply t.substitute (pushout.inr f g)
  intro a
  change Nonempty (CompositionExpression d.Source d.atomLift (d.sourceLift (.inr a)))
  rw [d.sourceLift_eq_atomLift]
  exact ⟨.generator (d.label (.inr a))⟩

/-- Covering piece atoms generate the actual strict pushout. -/
theorem generated (x : d.Source) :
    Nonempty (CompositionExpression d.Source d.atomLift x) := by
  obtain ⟨t⟩ := PushoutGeneration.generated_by_pieces f g x
  exact t.substitute (𝟙 d.Source) (fun a => by
    cases a with
    | inl y => exact d.generated_left_image y
    | inr y => exact d.generated_right_image y)

/-- Atomic coverage and actual common-source overlaps imply the full
strict pushout comparison is an isomorphism. -/
def iso : d.Source ≅ K.realization :=
  B.comparisonIso d.atomLift d.comparison d.atomLift_image d.atomLift_dimension d.generated

@[simp] theorem iso_hom : d.iso.hom = d.comparison := rfl

theorem comparison_isIso : IsIso d.comparison := by
  change IsIso d.iso.hom
  infer_instance

theorem isPushout : IsPushout f g d.left d.right := by
  apply IsPushout.of_iso_pushout ⟨d.condition⟩ d.iso.symm
  · have he : pushout.inl f g ≫ d.iso.hom = d.left :=
      pushout.inl_desc d.left d.right d.condition
    rw [← he, Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]
  · have he : pushout.inr f g ≫ d.iso.hom = d.right :=
      pushout.inr_desc d.left d.right d.condition
    rw [← he, Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

end
end PushoutGluing
end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Actual strict pushouts of the two globe cylinders

The source is the strict pushout of the original pieces. Its bounded
atom lifts, exact positive-table images, and composition generation have
all been constructed. The ordered free-comparison theorem therefore
makes the canonical cylinder comparison an actual strict isomorphism.
-/

namespace Thomason.Construction.StrictOmegaCategory.PastingGlobe.CylinderSource

open CategoryTheory CategoryTheory.Limits

noncomputable section

def basisIso {n k : ℕ} (hkn : k < n) :
    source n k ≅ (PastingGlobeCylinderBasis.Cylinder hkn).realization :=
  (atomBasis hkn).comparisonIso (atomLift hkn) (basisComparison hkn)
    (atomLift_image hkn) (atomLift_dimension hkn) (generated hkn)

@[simp] theorem basisIso_hom {n k : ℕ} (hkn : k < n) :
    (basisIso hkn).hom = basisComparison hkn := rfl

def modelIso {n k : ℕ} (hkn : k < n) :
    source n k ≅ model.obj (PastingGlobe.category n n k) :=
  basisIso hkn ≪≫ (PastingGlobeCylinderBasis.modelIso hkn).symm

@[simp] theorem modelIso_hom {n k : ℕ} (hkn : k < n) :
    (modelIso hkn).hom = comparison n k := by
  change (basisComparison hkn) ≫ (PastingGlobeCylinderBasis.modelIso hkn).inv = _
  simp only [basisComparison, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem comparison_isIso {n k : ℕ} (hkn : k < n) : IsIso (comparison n k) := by
  rw [← modelIso_hom hkn]
  infer_instance

/-- The actual chain-model cylinder preserves this pasted-globe pushout.
No preservation of colimits by positive-table realization is assumed. -/
theorem isPushout {n k : ℕ} (hkn : k < n) :
    IsPushout (model.map (Globe.faceMap true k n)) (model.map (Globe.faceMap false k n))
      (model.map (PastingGlobe.left n n k)) (model.map (PastingGlobe.right n n k)) := by
  apply IsPushout.of_iso_pushout
    (⟨by rw [← model.map_comp, ← model.map_comp, pushout.condition]⟩) (modelIso hkn).symm
  · have he : pushout.inl (model.map (Globe.faceMap true k n))
        (model.map (Globe.faceMap false k n)) ≫ (modelIso hkn).hom =
        model.map (PastingGlobe.left n n k) := by
      rw [modelIso_hom]
      exact piece_comparison n k false
    rw [← he, Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]
  · have he : pushout.inr (model.map (Globe.faceMap true k n))
        (model.map (Globe.faceMap false k n)) ≫ (modelIso hkn).hom =
        model.map (PastingGlobe.right n n k) := by
      rw [modelIso_hom]
      exact piece_comparison n k true
    rw [← he, Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

end
end Thomason.Construction.StrictOmegaCategory.PastingGlobe.CylinderSource

end

end OAI
