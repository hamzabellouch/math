import OAI.CategoryTheory.Thomason.Gray.GlobePastingDensity
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeChains
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderPath
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderRetractions
import OAI.CategoryTheory.Thomason.Gray.PosetPrismEndpoints
import OAI.CategoryTheory.Thomason.Gray.RightCylinderPrism
import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Gray.TopologicalIntervalCylinder
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Transfer.StrictPushoutGeneration
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.Order.Fin.InsertNth

namespace OAI

section

/-!
# Gray deformation retractions induce actual Thomason weak equivalences

This connects the constructed strict cylinders, their Street-nerve homotopies,
and the actual realization weak equivalences. Its classical inputs are only
the specified normalized chains, right Gray comparison, Alexander--Whitney
identities and Kan--Quillen WFS. No strict-category model structure is assumed.
-/

namespace Thomason.Construction

open CategoryTheory HomotopicalAlgebra

namespace KanQuillenPublishedInput

variable (kq : KanQuillenPublishedInput.{0})

include kq in
/-- Retract stability is derived from the two classical WFS, through the
model-category constructor, rather than added as a new input. -/
theorem weakEquivalences_retracts : realizationWeakEquivalences.{0}.IsStableUnderRetracts := by
  exact kq.model.cm3a

end KanQuillenPublishedInput

namespace RightGrayInput

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0})

include aw kq

/-- Strict right-cylinder homotopies preserve the prescribed Thomason
weak-equivalence class, defined by actual realizations of Street nerves. -/
theorem cylinder_weakEquivalence_iff {X Y : StrictOmegaCategory.{0}}
    (P : G.cylinder.obj X ⟶ Y) :
    h.streetWeakEquivalences ((G.endpoint false).app X ≫ P) ↔
      h.streetWeakEquivalences ((G.endpoint true).app X ≫ P) :=
  kq.homotopy_weakEquivalence_iff (G.nerveHomotopy aw P)

/-- A strict retraction with a Gray homotopy from its other composite to
identity is a weak equivalence on both maps. -/
theorem deformation_retract_weakEquivalences {A X : StrictOmegaCategory.{0}}
    (i : A ⟶ X) (r : X ⟶ A) (hi : i ≫ r = 𝟙 A)
    (P : G.cylinder.obj X ⟶ X)
    (h₀ : (G.endpoint false).app X ≫ P = r ≫ i)
    (h₁ : (G.endpoint true).app X ≫ P = 𝟙 X) :
    h.streetWeakEquivalences i ∧ h.streetWeakEquivalences r := by
  have := kq.twoOutOfThree
  have := kq.weakEquivalences_retracts
  have : h.streetWeakEquivalences.ContainsIdentities :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).ContainsIdentities
  have : h.streetWeakEquivalences.HasTwoOutOfThreeProperty :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).HasTwoOutOfThreeProperty
  have : h.streetWeakEquivalences.IsStableUnderRetracts :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).IsStableUnderRetracts
  have hri : h.streetWeakEquivalences (r ≫ i) := by
    have hc := G.cylinder_weakEquivalence_iff aw kq P
    rw [h₀, h₁] at hc
    exact hc.mpr (h.streetWeakEquivalences.id_mem X)
  have hretract : RetractArrow i (r ≫ i) :=
    { i := Arrow.homMk i (𝟙 X) (by simp [← Category.assoc, hi])
      r := Arrow.homMk r (𝟙 X) (by simp)
      retract := by
        apply Arrow.hom_ext <;> simp [hi] }
  have hwi : h.streetWeakEquivalences i :=
    MorphismProperty.of_retract hretract hri
  refine ⟨hwi, ?_⟩
  apply h.streetWeakEquivalences.of_precomp i r hwi
  rw [hi]
  exact h.streetWeakEquivalences.id_mem A

end RightGrayInput
end Thomason.Construction

end

section

/-! # Actual Street weak equivalences for finite relative prisms -/

namespace Thomason.Construction.RelativePrismData

open CategoryTheory

variable {E : Type} [PartialOrder E] (D : RelativePrismData E)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]
  (G : RightGrayInput h) (t : GrayTruncationInput G) {n : ℕ} (r : FiniteReflectionInput n)
  (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0})

include G t aw kq

/-- In every positive finite dimension, either categorified endpoint is a
Street-nerve weak equivalence exactly when the other endpoint is. -/
theorem finite_weakEquivalence_iff :
    h.streetWeakEquivalences ((StrictOmegaCategory.inclusion (n + 1)).map
      (r.reflect.map (h.posetMap D.first))) ↔
    h.streetWeakEquivalences ((StrictOmegaCategory.inclusion (n + 1)).map
      (r.reflect.map (h.posetMap D.last))) := by
  let X : StrictOmegaCategory := (r.reflect.obj (h.categorification.obj (nerve E))).val
  let W : (X ⟶ X) → Prop := fun f => h.streetWeakEquivalences f
  exact (congrArg W (D.finitePrism_endpoint h G t r false)).symm.to_iff.trans
    ((G.cylinder_weakEquivalence_iff aw kq (D.finitePrism h G t r)).trans
      (congrArg W (D.finitePrism_endpoint h G t r true)).to_iff)

end Thomason.Construction.RelativePrismData

end

section

/-! # Essential expressions over a fixed positive-table level

A lower composite of a level-n cell has both factors at level n. Combined
with atomic indecomposability above n, this bounds every composition in an
essential preimage expression. The resulting strings are the source-side
input to the free-comparison induction.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory StrictOmegaCategory StrictOmegaCategory.ExpressionDegree

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

/-- At a strictly lower composition degree, the upper atom belongs to
one factor and the other factor has zero upper tables. -/
theorem aboveAtomOrZero_comp_factors (n s : ℕ) (hs : s < n)
    (Y Z : Cell K) (hyz : Y.face true s = Z.face false s)
    (hX : B.AboveAtomOrZero n (Cell.comp Y Z s hyz)) :
    B.AboveAtomOrZero n Y ∧ B.AboveAtomOrZero n Z := by
  rcases hX with hz | ⟨a, ha, he⟩
  · have hzero (q : ℕ) (hq : n < q) (side : Bool) :
        Y.table side q = 0 ∧ Z.table side q = 0 := by
      apply B.positive_add_eq_zero q _ _ (Y.positive side q) (Z.positive side q)
      have hh := hz q hq side
      simpa only [Cell.comp_table, Cell.pasteTable, Nat.not_lt.mpr (hs.le.trans hq.le),
        Nat.ne_of_gt (hs.trans hq), ite_false] using hh
    exact ⟨Or.inl (fun q hq side => (hzero q hq side).1),
      Or.inl (fun q hq side => (hzero q hq side).2)⟩
  · have hsum : ∀ q, n < q → ∀ side,
        Y.table side q + Z.table side q = (B.atom a.1 a.2).table side q := by
      intro q hq side
      have hh := he q hq side
      simpa only [Cell.comp_table, Cell.pasteTable, Nat.not_lt.mpr (hs.le.trans hq.le),
        Nat.ne_of_gt (hs.trans hq), ite_false, atomCell] using hh
    rcases B.atom_summands a.2 n ha Y Z hsum with ⟨hY, hZ⟩ | ⟨hY, hZ⟩
    · exact ⟨Or.inr ⟨a, ha, hY⟩, Or.inl hZ⟩
    · exact ⟨Or.inl hY, Or.inr ⟨a, ha, hZ⟩⟩

/-- No essential composition lies above the preceding decomposition
level of the image. This controls the whole expression, not just its root. -/
theorem essential_levelsLE {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    {x : C} (t : EssentialExpression C g x) (n : ℕ)
    (hX : B.AboveAtomOrZero (n+1) (F.toFun x)) : t.levelsLE n := by
  induction t with
  | generator a => trivial
  | @comp x y s hxy tx ty hx hy ihx ihy =>
    have hf : (F.toFun x).face true s = (F.toFun y).face false s :=
      (F.map_face true s x).symm.trans
        ((congrArg F.toFun hxy).trans (F.map_face false s y))
    have himage : B.AboveAtomOrZero (n+1)
        (Cell.comp (F.toFun x) (F.toFun y) s hf) := by
      have he : F.toFun (C.comp s x y hxy) = Cell.comp (F.toFun x) (F.toFun y) s hf :=
        F.map_comp s x y hxy hf
      rw [← he]
      exact hX
    have hs : s < n+1 := by
      by_contra hs
      rcases B.aboveAtomOrZero_comp_identity_factor (n+1) s (by omega)
        (F.toFun x) (F.toFun y) hf himage with h | h
      · exact hx (B.dimensionLE_of_expression_image g F hg hd tx.expression s h)
      · exact hy (B.dimensionLE_of_expression_image g F hg hd ty.expression s h)
    have hparts := B.aboveAtomOrZero_comp_factors (n+1) s hs
      (F.toFun x) (F.toFun y) hf himage
    exact ⟨by omega, ihx hparts.1, ihy hparts.2⟩

/-- Every preimage of a level-(n+1) cell is either n-dimensional or an
actual n-string whose factors have specified upper atoms above n. -/
theorem preimage_atom_string {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    (hgen : ∀ x : C, Nonempty (CompositionExpression C g x))
    (n : ℕ) (x : C) (hX : B.AboveAtomOrZero (n+1) (F.toFun x)) :
    C.DimensionLE n x ∨ ∃ xs : List C, xs ≠ [] ∧ CompositeList C n xs x ∧
      ∀ y ∈ xs, ∃ a : B.AtomIndex, n < a.1 ∧
        ∀ q, n < q → ∀ side, (F.toFun y).table side q = (B.atomCell a).table side q := by
  obtain ⟨t⟩ := hgen x
  obtain ⟨s⟩ := t.exists_essential
  by_cases hcount : highCount (fun a : B.AtomIndex => a.1) n s.expression.labels = 0
  · exact Or.inl (s.expression.dimensionLE (fun a => a.1) hd n
      ((highCount_eq_zero_iff _ n s.expression.labels).mp hcount))
  · have hdim : DimensionwiseGenerated C g (fun a => a.1) :=
      fun r y hy => B.exists_bounded_expression g F hg hgen r y hy
    obtain ⟨xs, _, hxs, hprop⟩ := exists_normalized_generator_string hd hdim s n
      (B.essential_levelsLE g F hg hd s n hX) (Nat.pos_of_ne_zero hcount)
    refine Or.inr ⟨xs, hxs.nonempty, hxs, ?_⟩
    intro y hy
    obtain ⟨e, he⟩ := hprop y hy
    obtain ⟨a, _, ha, haupper⟩ := B.expression_upper_atom g F hg hd e n he
    exact ⟨a, ha, haupper⟩

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Freeness of the ordered positive-table comparison

This proves the needed specialization of Steiner 2004, Theorem 5.7:
a strict category generated by bounded lifts of an actual ordered atom
basis is isomorphic to its positive-table realization. Generation is an
explicit property of the source, not an assumption of free relations.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory StrictOmegaCategory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem preimages_eq_of_dimensionLE {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) (n : ℕ)
    (hunique : ∀ X, B.AboveAtomOrZero n X → ∃! x : C, F.toFun x = X)
    (X : Cell K) (x y : C) (hx : F.toFun x = X) (hy : F.toFun y = X)
    (hd : C.DimensionLE n x) : x = y := by
  have hX : B.AboveAtomOrZero n X := by
    apply Or.inl
    intro q hq side
    exact (congrArg (fun Y : Cell K => Y.table side q) hx).symm.trans
      (Cell.table_zero_of_dimensionLE (F.dimensionLE hd) hq side)
  obtain ⟨_, _, hu⟩ := hunique X hX
  exact (hu x hx).trans (hu y hy).symm

theorem preimages_eq_successor {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    (hgen : ∀ x : C, Nonempty (CompositionExpression C g x))
    (n : ℕ) (hunique : ∀ X, B.AboveAtomOrZero n X → ∃! x : C, F.toFun x = X)
    (X : Cell K) (hX : B.AboveAtomOrZero (n+1) X)
    (x y : C) (hx : F.toFun x = X) (hy : F.toFun y = X) : x = y := by
  have hfx : B.AboveAtomOrZero (n+1) (F.toFun x) := hx.symm ▸ hX
  have hfy : B.AboveAtomOrZero (n+1) (F.toFun y) := hy.symm ▸ hX
  rcases B.preimage_atom_string g F hg hd hgen n x hfx with hdx | ⟨xs, _, hxs, hxa⟩
  · exact B.preimages_eq_of_dimensionLE F n hunique X x y hx hy hdx
  rcases B.preimage_atom_string g F hg hd hgen n y hfy with hdy | ⟨ys, _, hys, hya⟩
  · exact (B.preimages_eq_of_dimensionLE F n hunique X y x hy hx hdy).symm
  obtain ⟨as, has⟩ := AtomComposite.of_compositeList hxs hxa
  obtain ⟨bs, hbs⟩ := AtomComposite.of_compositeList hys hya
  have him : F.toFun x = F.toFun y := hx.trans hy.symm
  have hp : as.Perm bs := B.upper_sum_perm n as bs
    (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact has.degree a ha
      · exact hbs.degree a ha)
    (fun q hq side => (has.upper_sum q hq side).symm.trans
      ((congrArg (fun Z : Cell K => Z.table side q) him).trans (hbs.upper_sum q hq side)))
  have hsa := AtomComposite.of_sorted_perm hunique has (B.sortAtoms_perm as).symm
    (B.sortAtoms_pairwise as)
  have hsb := AtomComposite.of_sorted_perm hunique hbs
    (hp.symm.trans (B.sortAtoms_perm as).symm) (B.sortAtoms_pairwise as)
  exact AtomComposite.total_unique hunique hsa hsb him

/-- Every atom-decomposition level has unique preimages. The induction
hypotheses are discharged internally by actual sorting and interchange. -/
theorem unique_preimage_level {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    (hgen : ∀ x : C, Nonempty (CompositionExpression C g x)) :
    ∀ n X, B.AboveAtomOrZero n X → ∃! x : C, F.toFun x = X := by
  intro n
  induction n with
  | zero => exact B.unique_preimage_level_zero g F hg hd hgen
  | succ n ih =>
    intro X hX
    obtain ⟨x, hx⟩ := B.exists_preimage_successor F n ih X hX
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact B.preimages_eq_successor g F hg hd hgen n ih X hX y x hy hx

/-- The ordered-atom comparison is bijective on the actual cell carriers. -/
theorem comparison_bijective {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    (hgen : ∀ x : C, Nonempty (CompositionExpression C g x)) :
    Function.Bijective F.toFun := by
  have hall : ∀ X : Cell K, ∃! x : C, F.toFun x = X := by
    intro X
    obtain ⟨n, hn⟩ := X.finite_support
    exact B.unique_preimage_level g F hg hd hgen n X (Or.inl hn)
  constructor
  · intro x y he
    obtain ⟨_, _, hu⟩ := hall (F.toFun x)
    exact (hu x rfl).trans (hu y he.symm).symm
  · intro X
    obtain ⟨x, hx, _⟩ := hall X
    exact ⟨x, hx⟩

/-- The actual strict isomorphism, with the specified comparison as its
forward functor. -/
noncomputable def comparisonIso {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    (hgen : ∀ x : C, Nonempty (CompositionExpression C g x)) : C ≅ K.realization :=
  isoOfBijective F (B.comparison_bijective g F hg hd hgen)

@[simp] theorem comparisonIso_hom {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    (hgen : ∀ x : C, Nonempty (CompositionExpression C g x)) :
    (B.comparisonIso g F hg hd hgen).hom = F := rfl

theorem comparison_isIso {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    (hgen : ∀ x : C, Nonempty (CompositionExpression C g x)) : IsIso F := by
  change IsIso (B.comparisonIso g F hg hd hgen).hom
  infer_instance

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # The untensored pasted-globe comparison is an isomorphism

The actual strict pushout is generated by its two globe pieces. Shared
faces normalize to the chosen basis representatives, so ordered-atom
freeness applies to its canonical positive-table comparison. This also
identifies the abelianization unit on every binary pasting parameter.
-/

namespace Thomason.Construction.PastingGlobeBasis

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex StrictOmegaCategory

noncomputable section

private theorem mixed_coefficient {n k p r : ℕ} (hkn : k < n)
    (b : Basis n k p) (e : Basis n k r) (a : Bool) :
    PastingGlobeCylinderBasis.coefficient hkn (.mixed e)
      ((PastingGlobeCylinderBasis.atom hkn (.mixed b)).table a (r+1)) =
      DFunLike.coe (F := Chains n k r) ((atom hkn b).table a r) e := by
  change DFunLike.coe (F := Chains n k r) (if RightCylinder.prismSide (r+1) a then
      (0, (atom hkn b).table a (r+1), (atom hkn b).table a r)
    else ((atom hkn b).table a (r+1), 0, (atom hkn b).table a r)).2.2 e = _
  split_ifs <;> rfl

private theorem ordered_disjoint {n k p q r : ℕ} (hkn : k < n)
    (b : Basis n k p) (c : Basis n k q) (hrp : r < p) (hrq : r < q)
    (hbc : height b ≤ height c) (e : Basis n k r) :
    DFunLike.coe (F := Chains n k r) ((atom hkn b).table false r) e = 0 ∨
      DFunLike.coe (F := Chains n k r) ((atom hkn c).table true r) e = 0 := by
  have hh : PastingGlobeCylinderBasis.height (.mixed b) ≤
      PastingGlobeCylinderBasis.height (.mixed c) := by
    change 3 * height b ≤ 3 * height c
    omega
  have he := PastingGlobeCylinderBasis.ordered_atoms_disjoint hkn
    (.mixed b) (.mixed c) (Nat.succ_lt_succ hrp) (Nat.succ_lt_succ hrq) hh (.mixed e)
  simpa only [mixed_coefficient] using he

/-- The base ordered atoms are inherited from the explicit signed cylinder. -/
def orderedAtomBasis {n k : ℕ} (hkn : k < n) : OrderedAtomBasis (complex n k hkn) where
  Index := Basis n k
  coordinates _ := AddEquiv.refl _
  positive_iff _ _ := Iff.rfl
  augmentation x := by
    have he (v : Chains n k 0) :
        Finsupp.linearCombination ℤ (fun _ : Basis n k 0 => (1 : ℤ)) v =
          v.sum (fun _ z => z) := by
      simp [Finsupp.linearCombination_apply, Finsupp.sum]
    exact he x
  atom _ := atom hkn
  atom_top _ := atom_top hkn
  atom_above _ b _ h a := atom_above hkn b h a
  height _ := height
  disjoint b c hrp hrq hbc e := ordered_disjoint hkn b c hrp hrq hbc e

private def piece (n k : ℕ) (s : Bool) : Globe.category n ⟶ PastingGlobe.category n n k :=
  if s then PastingGlobe.right n n k else PastingGlobe.left n n k

private def pieceAtom {n k p : ℕ} (s : Bool) (b : DirectedGlobeComplex.Basis n p) :
    PastingGlobe.category n n k :=
  (piece n k s).toFun ((Globe.category n).face b.val p Globe.Cell.top)

/-- Lift the canonical representative to the appropriate actual globe face. -/
def atomLift {n k : ℕ} (hkn : k < n) (a : (orderedAtomBasis hkn).AtomIndex) :
    PastingGlobe.category n n k :=
  pieceAtom a.2.val.1 ⟨a.2.val.2, a.2.property.1⟩

theorem atomLift_dimension {n k : ℕ} (hkn : k < n)
    (a : (orderedAtomBasis hkn).AtomIndex) :
    (PastingGlobe.category n n k).DimensionLE a.1 (atomLift hkn a) :=
  (piece n k a.2.val.1).dimensionLE ((Globe.category n).face_dimensionLE
    a.2.val.2 a.1 Globe.Cell.top)

private theorem pieceAtom_image {n k p : ℕ} (hkn : k < n)
    (s : Bool) (b : DirectedGlobeComplex.Basis n p) :
    (fromPasting hkn).toFun (pieceAtom s b) =
      (inclusion hkn s).realization.toFun ((DirectedGlobeComplex.topCell n).face b.val p) := by
  have ht : (fromPasting hkn).toFun ((piece n k s).toFun Globe.Cell.top) = top hkn s := by
    cases s
    · exact PastingGlobe.desc_left _ _ _ _ _ _
    · exact PastingGlobe.desc_right _ _ _ _ _ _
  calc
    _ = (fromPasting hkn).toFun ((PastingGlobe.category n n k).face b.val p
        ((piece n k s).toFun Globe.Cell.top)) :=
      congrArg (fromPasting hkn).toFun ((piece n k s).map_face _ _ _)
    _ = ((complex n k hkn).realization).face b.val p (top hkn s) := by
      rw [(fromPasting hkn).map_face, ht]
    _ = _ := ((inclusion hkn s).realization.map_face _ _ _).symm

theorem atomLift_image {n k : ℕ} (hkn : k < n)
    (a : (orderedAtomBasis hkn).AtomIndex) :
    (fromPasting hkn).toFun (atomLift hkn a) = (orderedAtomBasis hkn).atomCell a :=
  pieceAtom_image hkn a.2.val.1 ⟨a.2.val.2, a.2.property.1⟩

private theorem shared_lower {n k p : ℕ} (hkn : k < n) (hp : p < k) (a : Bool) :
    pieceAtom (n := n) (k := k) false ⟨a, Or.inl (hp.trans hkn)⟩ =
      pieceAtom (n := n) (k := k) true ⟨a, Or.inl (hp.trans hkn)⟩ := by
  have h := congrArg ((PastingGlobe.category n n k).face a p) (PastingGlobe.matching n n k)
  simp only [source, target, (PastingGlobe.category n n k).globular, hp, ite_true] at h
  exact ((PastingGlobe.left n n k).map_face a p Globe.Cell.top).trans
    (h.trans ((PastingGlobe.right n n k).map_face a p Globe.Cell.top).symm)

private theorem pieceAtom_normalize {n k p : ℕ} (hkn : k < n)
    (s : Bool) (b : DirectedGlobeComplex.Basis n p) :
    pieceAtom (k := k) s b = atomLift hkn ⟨p, embed hkn s b⟩ := by
  cases s with
  | false => rfl
  | true =>
    by_cases hp : p < k
    · simpa [atomLift, embed, right, hp, left] using
        (shared_lower hkn hp b.val).symm
    · by_cases he : p = k
      · subst p
        by_cases hb : b.val = false
        · have hb' : b = ⟨false, Or.inl hkn⟩ := Subtype.ext hb
          subst b
          have h : pieceAtom (n := n) (k := k) true ⟨false, Or.inl hkn⟩ =
              pieceAtom (n := n) (k := k) false ⟨true, Or.inl hkn⟩ :=
            ((PastingGlobe.right n n k).map_face false k Globe.Cell.top).trans
              ((PastingGlobe.matching n n k).symm.trans
                ((PastingGlobe.left n n k).map_face true k Globe.Cell.top).symm)
          simpa [atomLift, embed, right, left] using h
        · have hb' : b = ⟨true, Or.inl hkn⟩ := Subtype.ext (Bool.eq_true_of_not_eq_false hb)
          subst b
          simp [atomLift, embed, right]
      · simp [atomLift, embed, right, hp, he]

private theorem piece_generated {n k : ℕ} (hkn : k < n) (s : Bool)
    (x : Globe.category n) :
    Nonempty (CompositionExpression (PastingGlobe.category n n k) (atomLift hkn)
      ((piece n k s).toFun x)) := by
  let p := Globe.dimension x
  let b := DirectedGlobeComplex.globeBasis x
  have hx : (Globe.category n).face b.val p Globe.Cell.top = x := by
    cases x with
    | top => exact (Globe.category_truncated n Globe.Cell.top).1
    | boundary a j => exact dite_eq_right (Nat.not_le.mpr j.isLt)
  have he := pieceAtom_normalize hkn s b
  have hx' : pieceAtom (k := k) s b = (piece n k s).toFun x := congrArg _ hx
  rw [← hx', he]
  exact ⟨CompositionExpression.generator (C := PastingGlobe.category n n k)
    (g := atomLift hkn) ⟨p, embed hkn s b⟩⟩

theorem generated {n k : ℕ} (hkn : k < n) (x : PastingGlobe.category n n k) :
    Nonempty (CompositionExpression (PastingGlobe.category n n k) (atomLift hkn) x) := by
  obtain ⟨t⟩ := PushoutGeneration.generated_by_pieces
    (Globe.faceMap true k n) (Globe.faceMap false k n) x
  exact t.substitute (𝟙 (PastingGlobe.category n n k)) (fun a => by
    cases a with
    | inl y => exact piece_generated hkn false y
    | inr y => exact piece_generated hkn true y)

/-- The canonical comparison of the actual pasted globes is a strict isomorphism. -/
def pastingIso {n k : ℕ} (hkn : k < n) :
    PastingGlobe.category n n k ≅ (complex n k hkn).realization :=
  (orderedAtomBasis hkn).comparisonIso (atomLift hkn) (fromPasting hkn)
    (atomLift_image hkn) (atomLift_dimension hkn) (generated hkn)

@[simp] theorem pastingIso_hom {n k : ℕ} (hkn : k < n) :
    (pastingIso hkn).hom = fromPasting hkn := rfl

/-- Strict abelianization also recovers the actual binary pasting parameter. -/
def pastingUnitIso {n k : ℕ} (hkn : k < n) :
    PastingGlobe.category n n k ≅
      (Abelianization.complex (PastingGlobe.category n n k)).realization :=
  pastingIso hkn ≪≫ (realizationFunctor.mapIso (abelianizationIso hkn)).symm

theorem pastingUnitIso_hom {n k : ℕ} (hkn : k < n) :
    (pastingUnitIso hkn).hom = Abelianization.unit (PastingGlobe.category n n k) := by
  apply (cancel_mono (realizationFunctor.map (abelianizationIso hkn).hom)).mp
  have he := Abelianization.unit_evaluate (fromPasting hkn)
  calc
    _ = fromPasting hkn := by
      change ((pastingIso hkn).hom ≫
        (realizationFunctor.mapIso (abelianizationIso hkn)).inv) ≫
        (realizationFunctor.mapIso (abelianizationIso hkn)).hom = _
      let e := realizationFunctor.mapIso (abelianizationIso hkn)
      change (fromPasting hkn ≫ e.inv) ≫ e.hom = fromPasting hkn
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun q => fromPasting hkn ≫ q) e.inv_hom_id).trans (Category.comp_id _))
    _ = _ := he.symm

end
end Thomason.Construction.PastingGlobeBasis

end

section

/-! # The actual collapse of the extended right cylinder

The abelianization unit is invertible on the finite globe-and-pasting
parameters. The literal chain collapse therefore takes values in those
strict parameters, and density extends it to every strict category.
Both global endpoints are sections of this collapse.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayChainExtension

open CategoryTheory CategoryTheory.Functor _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- Collapse the interval in the global chain model. -/
def modelCollapse : model ⟶ Abelianization.functor ⋙ realizationFunctor where
  app C := (RightCylinder.projection (Abelianization.complex C)).realization
  naturality C D f := by
    apply Hom.ext
    funext x
    exact RightCylinder.realization_projection_map (Abelianization.map f) x

theorem modelEndpoint_collapse (a : Bool) :
    modelEndpoint a ≫ modelCollapse = Abelianization.adjunction.unit := by
  apply NatTrans.ext
  funext C
  apply Hom.ext
  funext x
  exact RightCylinder.realization_projection_endpoint (Abelianization.complex C) a
    ((Abelianization.unit C).toFun x)

/-- The unit comparison at one actual globe or binary pasting. -/
def parameterUnitComponent (i : GlobePasting.Shape) :
    GlobePasting.object i ≅ (Abelianization.complex (GlobePasting.object i)).realization :=
  match i with
  | .globe n => DirectedGlobeComplex.globeUnitIso n
  | .pair _ _ hk => PastingGlobeBasis.pastingUnitIso hk

@[simp] theorem parameterUnitComponent_hom (i : GlobePasting.Shape) :
    (parameterUnitComponent i).hom = Abelianization.unit (GlobePasting.object i) := by
  cases i with
  | globe n => exact DirectedGlobeComplex.globeUnitIso_hom n
  | pair n k hk => exact PastingGlobeBasis.pastingUnitIso_hom hk

/-- The actual unit is an isomorphism on every chosen finite parameter. -/
def parameterUnitIso : GlobePasting.inclusion ≅
    GlobePasting.inclusion ⋙ Abelianization.functor ⋙ realizationFunctor :=
  NatIso.ofComponents parameterUnitComponent (by
    intro i j f
    let f' : GlobePasting.object i ⟶ GlobePasting.object j := f
    change f' ≫ (parameterUnitComponent j).hom =
      (parameterUnitComponent i).hom ≫ (Abelianization.map f').realization
    rw [parameterUnitComponent_hom, parameterUnitComponent_hom]
    exact Abelianization.adjunction.unit.naturality f')

@[simp] theorem parameterUnitIso_hom_app (i : GlobePasting.Shape) :
    parameterUnitIso.hom.app i = Abelianization.unit (GlobePasting.object i) :=
  parameterUnitComponent_hom i

/-- Collapse on each actual finite parameter, with the unit inverted. -/
def parameterProjection : parameters ⟶ GlobePasting.inclusion :=
  whiskerLeft GlobePasting.inclusion modelCollapse ≫ parameterUnitIso.inv

/-- The global strict cylinder collapse is the unique extension of these maps. -/
def projection : cylinder ⟶ 𝟭 StrictOmegaCategory.{0} :=
  GlobePasting.compare parameters (𝟭 _) parameterProjection

@[reassoc (attr := simp)] theorem projection_parameters :
    parameterIso.hom ≫ whiskerLeft GlobePasting.inclusion projection =
      parameterProjection :=
  GlobePasting.restriction_compare parameters (𝟭 _) parameterProjection

theorem parameterEndpoint_projection (a : Bool) (i : GlobePasting.Shape) :
    (modelEndpoint a).app (GlobePasting.object i) ≫ parameterProjection.app i =
      𝟙 (GlobePasting.object i) := by
  let C := GlobePasting.object i
  let e : C ≅ (Abelianization.complex C).realization := parameterUnitIso.app i
  let q : model.obj C ⟶ (Abelianization.complex C).realization := modelCollapse.app C
  let j : C ⟶ model.obj C := (modelEndpoint a).app C
  have he : j ≫ q = e.hom :=
    (congrArg (fun t => t.app C) (modelEndpoint_collapse a)).trans
      (parameterUnitIso_hom_app i).symm
  change j ≫ (q ≫ e.inv) = 𝟙 C
  exact (Category.assoc j q e.inv).symm.trans
    ((congrArg (fun f => f ≫ e.inv) he).trans e.hom_inv_id)

/-- Both actual global endpoint maps are sections of the constructed collapse. -/
theorem endpoint_projection (a : Bool) (C : StrictOmegaCategory.{0}) :
    (endpoint a).app C ≫ projection.app C = 𝟙 C := by
  have hnat : endpoint a ≫ projection = 𝟙 (𝟭 StrictOmegaCategory.{0}) := by
    apply Functor.hom_ext_of_isLeftKanExtension _ GlobePasting.inclusion.rightUnitor.inv
    apply NatTrans.ext
    funext i
    let C := GlobePasting.object i
    let e : model.obj C ≅ cylinder.obj C := parameterIso.app i
    have he : (endpoint a).app C = (modelEndpoint a).app C ≫ e.hom :=
      congrArg (fun t => t.app i) (endpoint_parameters a)
    let p : model.obj C ⟶ C := parameterProjection.app i
    have hp : e.hom ≫ projection.app C = p :=
      congrArg (fun t => t.app i) projection_parameters
    change (endpoint a).app C ≫ projection.app C = 𝟙 C
    calc
      _ = ((modelEndpoint a).app C ≫ e.hom) ≫ projection.app C :=
        congrArg (fun f => f ≫ projection.app C) he
      _ = (modelEndpoint a).app C ≫ (e.hom ≫ projection.app C) := Category.assoc _ _ _
      _ = (modelEndpoint a).app C ≫ p :=
        congrArg (fun f => (modelEndpoint a).app C ≫ f) hp
      _ = 𝟙 C := parameterEndpoint_projection a i
  exact congrArg (fun t => t.app C) hnat

/-- The strict collapse agrees with the literal chain collapse after the
abelianization unit, on every strict category. -/
theorem projection_unit :
    projection ≫ Abelianization.adjunction.unit = comparison ≫ modelCollapse := by
  apply GlobePasting.compare_ext parameters
  apply NatTrans.ext
  funext i
  let C := GlobePasting.object i
  let e : model.obj C ≅ cylinder.obj C := parameterIso.app i
  let u : C ≅ (Abelianization.complex C).realization := parameterUnitIso.app i
  let q : model.obj C ⟶ (Abelianization.complex C).realization := modelCollapse.app C
  have hp : e.hom ≫ projection.app C = q ≫ u.inv :=
    congrArg (fun t => t.app i) projection_parameters
  have hc : e.hom ≫ comparison.app C = 𝟙 (model.obj C) :=
    congrArg (fun t => t.app i) parameter_comparison
  change e.hom ≫ (projection.app C ≫ Abelianization.unit C) =
    e.hom ≫ (comparison.app C ≫ q)
  have hu : Abelianization.unit C = u.hom := (parameterUnitIso_hom_app i).symm
  calc
    _ = (e.hom ≫ projection.app C) ≫ u.hom :=
      (congrArg (fun f => e.hom ≫ (projection.app C ≫ f)) hu).trans
        (Category.assoc _ _ _).symm
    _ = (q ≫ u.inv) ≫ u.hom := congrArg (fun f => f ≫ u.hom) hp
    _ = q := (Category.assoc _ _ _).trans
      ((congrArg (fun f => q ≫ f) u.inv_hom_id).trans (Category.comp_id _))
    _ = (e.hom ≫ comparison.app C) ≫ q :=
      (Category.id_comp q).symm.trans (congrArg (fun f => f ≫ q) hc.symm)
    _ = _ := Category.assoc _ _ _

end
end Thomason.Construction.StrictOmegaCategory.GrayChainExtension

end

section

/-!
# Weak-equivalence transport through the assembled relative prism

The weak-equivalence class here is the one defined by actual geometric
realization of the Street nerve. Only the previously stated classical
Kan--Quillen and Alexander--Whitney inputs are used.
-/

namespace Thomason.Construction.RelativePrismData

open CategoryTheory

variable {E : Type} [PartialOrder E] (D : RelativePrismData E)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput] (G : RightGrayInput h)
  (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0})

include G aw kq

/-- Relative poset-prism endpoints simultaneously induce Street weak equivalences. -/
theorem weakEquivalence_iff :
    h.streetWeakEquivalences (h.categorification.map (nerveMap D.first.monotone.functor)) ↔
      h.streetWeakEquivalences (h.categorification.map (nerveMap D.last.monotone.functor)) := by
  have hfirst := D.prism_endpoint h G false
  have hlast := D.prism_endpoint h G true
  let W : (h.categorification.obj (nerve E) ⟶ h.categorification.obj (nerve E)) → Prop :=
    fun f => h.streetWeakEquivalences f
  exact (congrArg W hfirst).symm.to_iff.trans
    ((G.cylinder_weakEquivalence_iff aw kq (D.prism h G)).trans
      (congrArg W hlast).to_iff)

end Thomason.Construction.RelativePrismData

end

section

/-! # Descending actual topological prisms through geometric realization

Realization is the colimit of its topological simplices. Product with the
interval preserves that colimit by the explicitly constructed adjunction.
Consequently compatible continuous simplex prisms descend to the actual
realization, with both endpoint equations proved on the original legs.
-/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory CategoryTheory.Limits

/-- The actual topological simplices indexing a realization. -/
noncomputable abbrev diagram (K : SSet.{0}) :=
  CostructuredArrow.proj SSet.stdSimplex K ⋙ SimplexCategory.toTop.{0}

/-- The canonical cocone, using Mathlib's realization comparison on simplices. -/
noncomputable abbrev cocone (K : SSet.{0}) : Cocone (diagram K) :=
  (Functor.LeftExtension.mk SSet.toTop SSet.toTopSimplex.inv).coconeAt K

/-- Its actual colimit universal property. -/
noncomputable def isColimit (K : SSet.{0}) : IsColimit (cocone K) :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension SSet.toTop
    SSet.toTopSimplex.inv K

/-- The continuous map from an original topological simplex to realization. -/
noncomputable abbrev leg (K : SSet.{0}) (j : CostructuredArrow SSet.stdSimplex K) :=
  (cocone K).ι.app j

/-- Realization legs commute with every actual simplicial map. -/
theorem leg_naturality {K L : SSet.{0}} (f : K ⟶ L)
    (j : CostructuredArrow SSet.stdSimplex K) :
    leg K j ≫ SSet.toTop.map f = leg L ((CostructuredArrow.map f).obj j) := by
  change (SSet.toTopSimplex.inv.app j.left ≫ SSet.toTop.map j.hom) ≫ SSet.toTop.map f =
    SSet.toTopSimplex.inv.app j.left ≫ SSet.toTop.map (j.hom ≫ f)
  rw [Category.assoc, Functor.map_comp]

/-- Compatible topological prisms indexed by every simplex, including degenerate ones. -/
noncomputable def prismCocone (K : SSet.{0}) (Z : TopCat.{0})
    (P : ∀ j, TopologicalInterval.cylinder.obj ((diagram K).obj j) ⟶ Z)
    (hp : ∀ {i j} (f : i ⟶ j),
      TopologicalInterval.cylinder.map ((diagram K).map f) ≫ P j = P i) :
    Cocone (diagram K ⋙ TopologicalInterval.cylinder) where
  pt := Z
  ι := { app := P
         naturality := fun i j f => by
           change TopologicalInterval.cylinder.map ((diagram K).map f) ≫ P j = P i ≫ 𝟙 Z
           exact (hp f).trans (Category.comp_id _).symm }

/-- The assembled prism is defined on the actual geometric realization times I. -/
noncomputable def assemble (K : SSet.{0}) (Z : TopCat.{0})
    (P : ∀ j, TopologicalInterval.cylinder.obj ((diagram K).obj j) ⟶ Z)
    (hp : ∀ {i j} (f : i ⟶ j),
      TopologicalInterval.cylinder.map ((diagram K).map f) ≫ P j = P i) :
    TopologicalInterval.cylinder.obj (SSet.toTop.obj K) ⟶ Z :=
  (isColimitOfPreserves TopologicalInterval.cylinder (isColimit K)).desc (prismCocone K Z P hp)

@[reassoc]
theorem assemble_fac (K : SSet.{0}) (Z : TopCat.{0})
    (P : ∀ j, TopologicalInterval.cylinder.obj ((diagram K).obj j) ⟶ Z)
    (hp : ∀ {i j} (f : i ⟶ j),
      TopologicalInterval.cylinder.map ((diagram K).map f) ≫ P j = P i)
    (j : CostructuredArrow SSet.stdSimplex K) :
    TopologicalInterval.cylinder.map (leg K j) ≫ assemble K Z P hp = P j :=
  (isColimitOfPreserves TopologicalInterval.cylinder (isColimit K)).fac (prismCocone K Z P hp) j

/-- The global endpoint equation follows from its equations on original simplex legs. -/
theorem assemble_endpoint (K : SSet.{0}) (Z : TopCat.{0})
    (P : ∀ j, TopologicalInterval.cylinder.obj ((diagram K).obj j) ⟶ Z)
    (hp : ∀ {i j} (f : i ⟶ j),
      TopologicalInterval.cylinder.map ((diagram K).map f) ≫ P j = P i)
    (t : unitInterval) (f : SSet.toTop.obj K ⟶ Z)
    (he : ∀ j, TopologicalInterval.sectionAt ((diagram K).obj j) t ≫ P j = leg K j ≫ f) :
    TopologicalInterval.sectionAt (SSet.toTop.obj K) t ≫ assemble K Z P hp = f := by
  apply (isColimit K).hom_ext
  intro j
  have hn : leg K j ≫ TopologicalInterval.sectionAt (SSet.toTop.obj K) t =
      TopologicalInterval.sectionAt ((diagram K).obj j) t ≫
        TopologicalInterval.cylinder.map (leg K j) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  rw [← Category.assoc, hn, Category.assoc, assemble_fac, he]

/-- A pair of compatible endpoint equations gives an actual continuous homotopy. -/
noncomputable def homotopy (K : SSet.{0}) (Z : TopCat.{0})
    (P : ∀ j, TopologicalInterval.cylinder.obj ((diagram K).obj j) ⟶ Z)
    (hp : ∀ {i j} (f : i ⟶ j),
      TopologicalInterval.cylinder.map ((diagram K).map f) ≫ P j = P i)
    (f g : SSet.toTop.obj K ⟶ Z)
    (h₀ : ∀ j, TopologicalInterval.sectionAt ((diagram K).obj j) 0 ≫ P j = leg K j ≫ f)
    (h₁ : ∀ j, TopologicalInterval.sectionAt ((diagram K).obj j) 1 ≫ P j = leg K j ≫ g) :
    f.hom.Homotopy g.hom where
  toFun p := (assemble K Z P hp).hom (p.2, p.1)
  continuous_toFun := (assemble K Z P hp).hom.continuous.comp (by fun_prop)
  map_zero_left x := congrArg (fun k => k.hom x) (assemble_endpoint K Z P hp 0 f h₀)
  map_one_left x := congrArg (fun k => k.hom x) (assemble_endpoint K Z P hp 1 g h₁)

end Thomason.Construction.RealizationPrism

end

section

/-! # Stationary simplex prisms give actual realization weak equivalences

The hypotheses are continuous prism maps, their endpoint equations and
stationarity, not a weak-equivalence conclusion. They descend through the
actual realization colimit to a strong deformation retraction. This is the
semantic bridge for the relative prism construction, independently of KQ.
-/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory CategoryTheory.Limits

variable {K L : SSet.{0}} (i : K ⟶ L) (r : L ⟶ K) (hi : i ≫ r = 𝟙 K)
  (P : ∀ j, TopologicalInterval.cylinder.obj ((diagram L).obj j) ⟶ SSet.toTop.obj L)
  (hp : ∀ {j k} (f : j ⟶ k),
    TopologicalInterval.cylinder.map ((diagram L).map f) ≫ P k = P j)

/-- Local stationarity descends along the source realization colimit. -/
theorem assemble_stationary
    (hs : ∀ j : CostructuredArrow SSet.stdSimplex K,
      P ((CostructuredArrow.map i).obj j) =
        TopologicalInterval.projection ((diagram K).obj j) ≫ leg K j ≫ SSet.toTop.map i) :
    TopologicalInterval.cylinder.map (SSet.toTop.map i) ≫ assemble L _ P hp =
      TopologicalInterval.projection (SSet.toTop.obj K) ≫ SSet.toTop.map i := by
  apply (isColimitOfPreserves TopologicalInterval.cylinder (isColimit K)).hom_ext
  intro j
  change TopologicalInterval.cylinder.map (leg K j) ≫
      (TopologicalInterval.cylinder.map (SSet.toTop.map i) ≫ assemble L _ P hp) =
    TopologicalInterval.cylinder.map (leg K j) ≫
      (TopologicalInterval.projection (SSet.toTop.obj K) ≫ SSet.toTop.map i)
  have hproj : TopologicalInterval.cylinder.map (leg K j) ≫
      TopologicalInterval.projection (SSet.toTop.obj K) =
      TopologicalInterval.projection ((diagram K).obj j) ≫ leg K j := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  calc
    _ = TopologicalInterval.cylinder.map (leg K j ≫ SSet.toTop.map i) ≫
        assemble L _ P hp := by rw [Functor.map_comp, Category.assoc]
    _ = P ((CostructuredArrow.map i).obj j) := by rw [leg_naturality, assemble_fac]
    _ = _ := hs j
    _ = _ := by rw [← Category.assoc, ← hproj, Category.assoc]

include hi hp

/-- An actual simplicial retraction whose realization has compatible stationary
simplex prisms is a realization weak equivalence. -/
theorem weak_of_stationary_prisms
    (h₀ : ∀ j, TopologicalInterval.sectionAt ((diagram L).obj j) 0 ≫ P j =
      leg L j ≫ (SSet.toTop.map r ≫ SSet.toTop.map i))
    (h₁ : ∀ j, TopologicalInterval.sectionAt ((diagram L).obj j) 1 ≫ P j =
      leg L j ≫ 𝟙 (SSet.toTop.obj L))
    (hs : ∀ j : CostructuredArrow SSet.stdSimplex K,
      P ((CostructuredArrow.map i).obj j) =
        TopologicalInterval.projection ((diagram K).obj j) ≫ leg K j ≫ SSet.toTop.map i) :
    realizationWeakEquivalences i := by
  let H := homotopy L _ P hp (SSet.toTop.map r ≫ SSet.toTop.map i) (𝟙 _) h₀ h₁
  have hir : SSet.toTop.map i ≫ SSet.toTop.map r = 𝟙 (SSet.toTop.obj K) := by
    rw [← SSet.toTop.map_comp i r, hi]
    exact SSet.toTop.map_id K
  have Hrel : ((SSet.toTop.map i).hom.comp (SSet.toTop.map r).hom).HomotopyRel
      (ContinuousMap.id (SSet.toTop.obj L)) (Set.range (SSet.toTop.map i).hom) := {
    toHomotopy := H
    prop' := by
      intro t z hz
      obtain ⟨x, rfl⟩ := hz
      have hx := congrArg (fun f => f.hom (x, t)) (assemble_stationary i P hp hs)
      have hrx := congrArg (fun f => f.hom x) hir
      change (assemble L _ P hp).hom ((SSet.toTop.map i).hom x, t) =
        (SSet.toTop.map i).hom ((SSet.toTop.map r).hom ((SSet.toTop.map i).hom x))
      exact hx.trans (congrArg (SSet.toTop.map i).hom hrx).symm }
  exact weakEquivalence_of_strongDeformationRetract _ _ (congrArg TopCat.Hom.hom hir) Hrel

end Thomason.Construction.RealizationPrism

end

section

/-! # Explicit topological cone prisms

Appending one greatest vertex gives a natural prism on every standard
simplex. The barycentric formula is continuous and compatible with all
ordinal maps, including degeneracies.
-/

namespace Thomason.Construction.ConePrism

open CategoryTheory Convexity

/-- Append a vertex above the final vertex of an ordered simplex. -/
def append {P : Type*} [Preorder P] {n : ℕ} (s : Fin (n+1) →o P)
    (v : P) (hv : s (Fin.last n) ≤ v) : Fin (n+2) →o P where
  toFun := Fin.snoc (fun i => s i) v
  monotone' := by
    simpa only [Fin.insertNth_last'] using Fin.insertNth_last_monotone s.monotone v hv

@[simp]
theorem append_castSucc {P : Type*} [Preorder P] {n : ℕ}
    (s : Fin (n+1) →o P) (v : P) (hv) (i : Fin (n+1)) :
    append s v hv i.castSucc = s i := by
  change Fin.snoc (α := fun _ : Fin (n+2) => P) (fun j => s j) v i.castSucc = s i
  simp only [Fin.snoc_castSucc]

@[simp]
theorem append_last {P : Type*} [Preorder P] {n : ℕ}
    (s : Fin (n+1) →o P) (v : P) (hv) :
    append s v hv (Fin.last (n+1)) = v := by
  change Fin.snoc (α := fun _ : Fin (n+2) => P) (fun j => s j) v (Fin.last (n+1)) = v
  simp only [Fin.snoc_last]

/-- Extend an ordinal map by the new final vertex. -/
def ordinalMap {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) : Fin (m+2) →o Fin (n+2) :=
  append (Fin.castSuccOrderEmb.toOrderHom.comp f) (Fin.last (n+1)) (Fin.le_last _)

@[simp]
theorem ordinalMap_castSucc {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) (i : Fin (m+1)) :
    ordinalMap f i.castSucc = (f i).castSucc := append_castSucc _ _ _ _

@[simp]
theorem ordinalMap_last {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) :
    ordinalMap f (Fin.last (m+1)) = Fin.last (n+1) := append_last _ _ _

/-- The barycentric straight-line cone to the newly appended final vertex. -/
noncomputable def barycentric (n : ℕ) :
    C(StdSimplex ℝ (Fin (n+1)) × unitInterval, StdSimplex ℝ (Fin (n+2))) where
  toFun p := convexCombPair (R := ℝ) (unitInterval.symm p.2) p.2
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp)
    (StdSimplex.map Fin.castSucc p.1) (.single (Fin.last (n+1)))
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff]
    apply continuous_pi
    intro k
    simp only [Function.comp_def, StdSimplex.weights_convexCombPair, Finsupp.coe_add,
      Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitInterval.coe_symm_eq]
    have hc : Continuous (fun p : StdSimplex ℝ (Fin (n+1)) × unitInterval =>
        StdSimplex.map (Fin.castSucc : Fin (n+1) → Fin (n+2)) p.1) :=
      (StdSimplex.continuous_map ℝ _).comp continuous_fst
    have hw := (StdSimplex.continuous_weights_apply ℝ k).comp hc
    exact ((continuous_const.sub continuous_snd.subtype_val).mul hw).add
      (continuous_snd.subtype_val.mul continuous_const)

@[simp]
theorem barycentric_zero (n : ℕ) (x : StdSimplex ℝ (Fin (n+1))) :
    barycentric n (x, 0) = StdSimplex.map Fin.castSucc x := by
  ext k
  simp [barycentric]

@[simp]
theorem barycentric_one (n : ℕ) (x : StdSimplex ℝ (Fin (n+1))) :
    barycentric n (x, 1) = .single (Fin.last (n+1)) := by
  ext k
  simp [barycentric]

/-- Naturality of the topological cone under every ordinal map. -/
theorem barycentric_naturality {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) (t : unitInterval) :
    StdSimplex.map (ordinalMap f) (barycentric m (x, t)) =
      barycentric n (StdSimplex.map f x, t) := by
  change StdSimplex.map (ordinalMap f) (convexCombPair _ _ _ _ _ _ _) = _
  rw [(StdSimplex.isAffineMap_map ℝ (ordinalMap f)).map_convexCombPair]
  have hcomp : (fun j : Fin (m+1) => ordinalMap f j.castSucc) =
      fun j => (f j).castSucc := by funext j; exact ordinalMap_castSucc f j
  have hx : StdSimplex.map (ordinalMap f) (StdSimplex.map Fin.castSucc x) =
      StdSimplex.map Fin.castSucc (StdSimplex.map f x) := by
    rw [← StdSimplex.map_comp, ← StdSimplex.map_comp]
    exact congrArg (fun g => StdSimplex.map g x) hcomp
  simp only [StdSimplex.map_single, ordinalMap_last, hx]
  rfl

end Thomason.Construction.ConePrism

end

end OAI
