import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.RealizedSimplexWeakEquivalences
import OAI.CategoryTheory.Thomason.Strict.OrientalLabelFibers
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor
import OAI.CategoryTheory.Thomason.Transfer.StrictPushoutGeneration
import Mathlib.CategoryTheory.Limits.Over

namespace OAI

section

/-! # Actual full initial faces without atom-generation assumptions -/

namespace Thomason.Construction.SimplexComplex

open CategoryTheory StrictOmegaCategory

/-- The explicit initial ordinal face is an isomorphism onto the full
subcategory on its vertices, proved directly from positive chain support. -/
noncomputable def constructedInitialFaceIso (h : NormalizedSimplexIdentities)
    {q m : ℕ} (hqm : q ≤ m) :
    h.object q ≅ vertexFullSubcategory h (Set.range (initialFace hqm)) :=
  isoOfBijective (fullFaceMap h (initialFace hqm))
    ⟨fun _ _ hxy => map_injective_of_retraction h _ (initialClamp hqm)
      (initialClamp_retract hqm) (congrArg Subtype.val hxy),
      fun y => by
        have hy := (fullCell_vertices_iff h _ _).mp y.property
        have hs : (objectIndex h false y.val).val ≤ q :=
          (congrArg (fun I => objectIndex h false y.val ∈ I) (initialFace_range hqm)).mp hy.1
        have ht : (objectIndex h true y.val).val ≤ q :=
          (congrArg (fun I => objectIndex h true y.val ∈ I) (initialFace_range hqm)).mp hy.2
        obtain ⟨x, hx⟩ := initialFace_full h hqm y.val hs ht
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The isomorphism is the original ordinal face on all cells. -/
theorem constructedInitialFaceIso_hom_inclusion (h : NormalizedSimplexIdentities)
    {q m : ℕ} (hqm : q ≤ m) :
    (constructedInitialFaceIso h hqm).hom ≫
      (h.object m).fullInclusion {x | objectIndex h false x ∈ Set.range (initialFace hqm)} =
        h.map (initialFace hqm).toOrderHom := by
  apply Hom.ext
  rfl

/-- Every nonempty lower set of vertices is its actual smaller oriental. -/
theorem constructedInitialSegment (h : NormalizedSimplexIdentities)
    {m : ℕ} {I : Set (Fin (m+1))} (hI : IsLowerSet I) (hne : I.Nonempty) :
    ∃ q : Fin (m+1), Nonempty (h.object q.val ≅ vertexFullSubcategory h I) := by
  obtain ⟨q, rfl⟩ := lowerSet_eq_Iic hI hne
  have hqm : q.val ≤ m := Nat.le_of_lt_succ q.isLt
  have hr : Set.range (initialFace hqm) = Set.Iic q := initialFace_range hqm
  exact ⟨q, ⟨constructedInitialFaceIso h hqm ≪≫
    eqToIso (congrArg (vertexFullSubcategory h) hr)⟩⟩

/-- The actual nonempty zero fibre of every binary oriental label is a
smaller oriental. No published composition-generation input is used. -/
theorem constructedZeroFiberOriental (h : NormalizedSimplexIdentities)
    {m : ℕ} (b : Fin (m+1) →o Fin 2) (hne : Set.Nonempty {i | b i = 0}) :
    ∃ q : Fin (m+1), Nonempty (h.object q.val ≅ labelFiber (binaryLabel h b) 0) := by
  obtain ⟨q, ⟨e⟩⟩ := constructedInitialSegment h (binaryLabel_zero_initial b) hne
  exact ⟨q, ⟨e ≪≫ (labelFiberVerticesIso h b 0).symm⟩⟩

end Thomason.Construction.SimplexComplex

end

section

/-!
# Labelled simplex presentations and their full fibres

The actual oriental presentation lifts to the slice over the walking arrow.
The endpoint-fibre colimit theorem applies directly to this
constructed diagram. On each piece its label is the monotone vertex label,
so the full initial/final-segment calculations apply.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits Opposite StrictOmegaCategory

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Lift the oriental presentation along a fixed actual binary label. -/
noncomputable def labelledSimplexDiagram {K : SSet.{0}}
    (p : h.categorification.obj K ⟶ StrictPoset.category (Fin 2)) :
    CostructuredArrow SSet.stdSimplex K ⥤ Over (StrictPoset.category (Fin 2)) :=
  Over.lift (CostructuredArrow.proj SSet.stdSimplex K ⋙ h.cosimplicial)
    ((h.simplexCocone K).ι ≫ (Functor.const _).map p)

/-- The corresponding colimit cocone in the actual slice category. -/
noncomputable def labelledSimplexCocone {K : SSet.{0}}
    (p : h.categorification.obj K ⟶ StrictPoset.category (Fin 2)) :
    Cocone (h.labelledSimplexDiagram p) := Over.liftCocone (h.simplexCocone K) p

/-- Forgetting labels recovers the original simplex colimit, so the lifted
cocone is itself a colimit. -/
noncomputable def labelledSimplexCocone_isColimit {K : SSet.{0}}
    (p : h.categorification.obj K ⟶ StrictPoset.category (Fin 2)) :
    IsColimit (h.labelledSimplexCocone p) :=
  Over.isColimitLiftCocone (h.simplexCocone K) p (h.simplexCocone_isColimit K)

/-- Take one full endpoint fibre of every labelled oriental piece. -/
noncomputable def simplexFiberCocone {K : SSet.{0}}
    (p : h.categorification.obj K ⟶ StrictPoset.category (Fin 2)) (e : Fin 2) :
    Cocone (h.labelledSimplexDiagram p ⋙ labelFiberFunctor (Fin 2) e) :=
  (labelFiberFunctor (Fin 2) e).mapCocone (h.labelledSimplexCocone p)

/-- The actual full fibre is the colimit of the actual full simplex fibres. -/
noncomputable def simplexFiberCocone_isColimit (f : PublishedLabelFiberInput) {K : SSet.{0}}
    (p : h.categorification.obj K ⟶ StrictPoset.category (Fin 2)) (e : Fin 2) :
    IsColimit (h.simplexFiberCocone p e) := by
  have := f.omega e
  exact isColimitOfPreserves (labelFiberFunctor (Fin 2) e) (h.labelledSimplexCocone_isColimit p)

/-- These are the actual labels on the pieces of the lifted presentation. -/
theorem labelledSimplexDiagram_obj_hom {K : SSet.{0}}
    (p : h.categorification.obj K ⟶ StrictPoset.category (Fin 2))
    (s : CostructuredArrow SSet.stdSimplex K) :
    ((h.labelledSimplexDiagram p).obj s).hom = h.simplexLeg s.hom ≫ p := rfl

/-- On a poset simplex the membership label is exactly its monotone binary vertex label. -/
theorem membership_simplex_label {E : Type} [PartialOrder E]
    (A : Set E) (hA : IsLowerSet A) {m : SimplexCategory}
    (s : SSet.stdSimplex.obj m ⟶ nerve E) :
    h.simplexLeg s ≫ h.membershipLabel A hA =
      SimplexComplex.binaryLabel h
        ((sieveCharacteristic A hA).comp (simplexOrder (SSet.yonedaEquiv s))) := by
  let p := StrictPoset.map (sieveCharacteristic A hA)
  have he := h.posetEvaluation_fac s
  change h.simplexLeg s ≫ (h.posetEvaluation E ≫ p) = _
  calc
    _ = (h.simplexLeg s ≫ h.posetEvaluation E) ≫ p := (Category.assoc _ _ _).symm
    _ = h.simplexPosetLabel s ≫ p := congrArg (fun k => k ≫ p) he
    _ = _ := by
      apply StrictOmegaCategory.Hom.ext
      rfl

/-- Every nonempty zero-fibre of a simplex piece is a smaller oriental. -/
theorem membership_simplex_fiber_nonempty {E : Type} [PartialOrder E]
    (a : SimplexAtomsInput h) (A : Set E) (hA : IsLowerSet A) {m : SimplexCategory}
    (s : SSet.stdSimplex.obj m ⟶ nerve E)
    (hne : Set.Nonempty {i | simplexOrder (SSet.yonedaEquiv s) i ∈ A}) :
    ∃ q : Fin (m.len + 1), Nonempty (h.object q.val ≅
      labelFiber (h.simplexLeg s ≫ h.membershipLabel A hA) 0) := by
  let b := (sieveCharacteristic A hA).comp (simplexOrder (SSet.yonedaEquiv s))
  have hb : Set.Nonempty {i | b i = 0} := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, (sieveCharacteristic_zero_iff A hA _).mpr hi⟩
  obtain ⟨q, ⟨e⟩⟩ := SimplexComplex.zeroFiber_oriental a b hb
  have he : labelFiber (h.simplexLeg s ≫ h.membershipLabel A hA) 0 =
      labelFiber (SimplexComplex.binaryLabel h b) 0 :=
    congrArg (fun p => labelFiber p 0) (h.membership_simplex_label A hA s)
  exact ⟨q, ⟨e ≪≫ (eqToIso he).symm⟩⟩

/-- The cocone point is exactly the full fibre of the original label. -/
theorem simplexFiberCocone_pt {K : SSet.{0}}
    (p : h.categorification.obj K ⟶ StrictPoset.category (Fin 2)) (e : Fin 2) :
    (h.simplexFiberCocone p e).pt = labelFiber p e := rfl

/-- An empty vertex intersection gives an empty actual simplex fibre. -/
theorem membership_simplex_fiber_empty {E : Type} [PartialOrder E]
    (A : Set E) (hA : IsLowerSet A) {m : SimplexCategory}
    (s : SSet.stdSimplex.obj m ⟶ nerve E)
    (hne : ¬Set.Nonempty {i | simplexOrder (SSet.yonedaEquiv s) i ∈ A}) :
    IsEmpty (labelFiber (h.simplexLeg s ≫ h.membershipLabel A hA) 0) := by
  let b := (sieveCharacteristic A hA).comp (simplexOrder (SSet.yonedaEquiv s))
  have hb : ¬Set.Nonempty {i | b i = 0} := by
    rintro ⟨i, hi⟩
    exact hne ⟨i, (sieveCharacteristic_zero_iff A hA _).mp hi⟩
  have he : labelFiber (h.simplexLeg s ≫ h.membershipLabel A hA) 0 =
      labelFiber (SimplexComplex.binaryLabel h b) 0 :=
    congrArg (fun p => labelFiber p 0) (h.membership_simplex_label A hA s)
  exact he.symm ▸ SimplexComplex.labelFiber_empty h b 0 hb

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # The one-dimensional horn generators are actual realization equivalences

This is the first semantic horn calculation. It uses only the explicit
one-vertex horn isomorphism and the topological simplex contraction; no
Kan–Quillen published input is required.
-/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

/-- Both endpoint inclusions into the simplicial interval are weak. -/
theorem realization_delta_one_weak (j : Fin 2) :
    realizationWeakEquivalences (SSet.stdSimplex.δ j : (Δ[0] : SSet.{0}) ⟶ Δ[1]) :=
  realized_simplex_map_weak (SimplexCategory.δ j)

/-- The two one-dimensional horn inclusions satisfy the prescribed actual
realization weak-equivalence test. -/
theorem realization_horn_one_weak (i : Fin 2) :
    realizationWeakEquivalences (Λ[1, i].ι : _ ⟶ (Δ[1] : SSet.{0})) := by
  have hji : i.rev ≠ i := by fin_cases i <;> decide
  have : IsIso (SSet.horn.ι i i.rev hji : (Δ[0] : SSet.{0}) ⟶ Λ[1, i]) :=
    (hornOneIso i i.rev hji).isIso_hom
  apply (realizationWeakEquivalences.cancel_left_of_respectsIso
    (SSet.horn.ι i i.rev hji) _).mp
  rw [SSet.horn.ι_ι]
  exact realization_delta_one_weak i.rev

end Thomason.Construction

end

section

/-! # Clamping a poset simplex to its nonempty sieve prefix

These are the concrete maps used to descend the full zero-fibre comparison
through the oriental presentation of a poset nerve.
-/

namespace Thomason.Construction

open CategoryTheory StrictOmegaCategory

namespace SieveSimplex

variable {P : Type} [PartialOrder P] (A : Set P) (hA : IsLowerSet A)
  {m : ℕ} (s : Fin (m+1) →o P)

/-- The zero-labelled vertices of a poset simplex form one initial segment. -/
structure Cut where
  last : Fin (m+1)
  mem_iff (i : Fin (m+1)) : s i ∈ A ↔ i ≤ last

/-- Construct the last vertex of the nonempty initial segment. -/
noncomputable def cut (hne : ∃ i, s i ∈ A) : Cut A s := by
  have hl : IsLowerSet {i : Fin (m+1) | s i ∈ A} :=
    fun _ _ hij hj => hA (s.monotone hij) hj
  let e := SimplexComplex.lowerSet_eq_Iic hl hne
  exact ⟨e.choose, fun i => (congrArg (fun S => i ∈ S) e.choose_spec).to_iff⟩

variable {A s}

instance : Subsingleton (Cut A s) where
  allEq c d := by
    have he : c.last = d.last := le_antisymm
      ((d.mem_iff c.last).mp ((c.mem_iff c.last).mpr le_rfl))
      ((c.mem_iff d.last).mp ((d.mem_iff d.last).mpr le_rfl))
    cases c
    cases d
    cases he
    rfl

/-- Clamp all later vertices to the last sieve vertex. -/
def Cut.clamp (c : Cut A s) : Fin (m+1) →o A where
  toFun i := ⟨s (min i c.last), (c.mem_iff _).mpr (min_le_right _ _)⟩
  monotone' := fun _ _ hij => s.monotone (min_le_min_right _ hij)

theorem Cut.clamp_of_mem (c : Cut A s) (i : Fin (m+1)) (hi : s i ∈ A) :
    (c.clamp i).val = s i := by
  change s (min i c.last) = s i
  rw [min_eq_left ((c.mem_iff i).mp hi)]

/-- Different cut choices, or precomposed simplices, agree on all sieve vertices. -/
theorem Cut.clamp_naturality {k : ℕ} {t : Fin (k+1) →o P}
    (c : Cut A s) (d : Cut A t) (u : Fin (m+1) →o Fin (k+1))
    (hu : ∀ i, t (u i) = s i) (i : Fin (m+1)) (hi : s i ∈ A) :
    c.clamp i = d.clamp (u i) := by
  apply Subtype.ext
  rw [c.clamp_of_mem i hi, d.clamp_of_mem (u i) ((hu i).symm ▸ hi), hu]

/-- The binary strict label carried by this actual oriental. -/
noncomputable def label (A : Set P) (hA : IsLowerSet A) {m : ℕ}
    (s : Fin (m+1) →o P) (h : NormalizedSimplexIdentities) :
    h.object m ⟶ StrictPoset.category (Fin 2) :=
  SimplexComplex.binaryLabel h ((sieveCharacteristic A hA).comp s)

/-- Every cell of the zero fibre is in the actual initial face determined by the cut. -/
theorem Cut.fiber_in_initial_face (h : NormalizedSimplexIdentities) (c : Cut A s)
    (x : labelFiber (label A hA s h) 0) :
    x.val ∈ Set.range
      (h.map (SimplexComplex.initialFace (Nat.le_of_lt_succ c.last.isLt)).toOrderHom).toFun := by
  have hx := (SimplexComplex.binaryLabel_fullCell_iff h
    ((sieveCharacteristic A hA).comp s) 0 x.val).mp x.property
  have hs : (SimplexComplex.objectIndex h false x.val).val ≤ c.last.val :=
    (c.mem_iff _).mp ((sieveCharacteristic_zero_iff A hA _).mp hx.1)
  have ht : (SimplexComplex.objectIndex h true x.val).val ≤ c.last.val :=
    (c.mem_iff _).mp ((sieveCharacteristic_zero_iff A hA _).mp hx.2)
  exact SimplexComplex.initialFace_full h (Nat.le_of_lt_succ c.last.isLt) x.val hs ht

end SieveSimplex
end Thomason.Construction

end

section

/-! # Clamping a poset simplex to its nonempty cosieve suffix -/

namespace Thomason.Construction

open CategoryTheory StrictOmegaCategory

noncomputable abbrev cosieveCharacteristic {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) : P →o Fin 2 := sieveCharacteristic Aᶜ hA.compl

@[simp] theorem cosieveCharacteristic_one_iff {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) (x : P) : cosieveCharacteristic A hA x = 1 ↔ x ∈ A := by
  classical
  by_cases hx : x ∈ A <;> simp [cosieveCharacteristic, sieveCharacteristic, hx]

namespace CosieveSimplex

variable {P : Type} [PartialOrder P] (A : Set P) (hA : IsUpperSet A)
  {m : ℕ} (s : Fin (m + 1) →o P)

structure Cut where
  first : Fin (m + 1)
  mem_iff (i : Fin (m + 1)) : s i ∈ A ↔ first ≤ i

noncomputable def cut (hne : ∃ i, s i ∈ A) : Cut A s := by
  have hu : IsUpperSet {i : Fin (m + 1) | s i ∈ A} :=
    fun _ _ hij hi => hA (s.monotone hij) hi
  let e := SimplexComplex.upperSet_eq_Ici hu hne
  exact ⟨e.choose, fun i => (congrArg (fun S => i ∈ S) e.choose_spec).to_iff⟩

variable {A s}

instance : Subsingleton (Cut A s) where
  allEq c d := by
    have he : c.first = d.first := le_antisymm
      ((c.mem_iff d.first).mp ((d.mem_iff d.first).mpr le_rfl))
      ((d.mem_iff c.first).mp ((c.mem_iff c.first).mpr le_rfl))
    cases c
    cases d
    cases he
    rfl

def Cut.clamp (c : Cut A s) : Fin (m + 1) →o A where
  toFun i := ⟨s (max i c.first), (c.mem_iff _).mpr (le_max_right _ _)⟩
  monotone' := fun _ _ hij => s.monotone (max_le_max_right _ hij)

theorem Cut.clamp_of_mem (c : Cut A s) (i : Fin (m + 1)) (hi : s i ∈ A) :
    (c.clamp i).val = s i := by
  change s (max i c.first) = s i
  rw [max_eq_left ((c.mem_iff i).mp hi)]

theorem Cut.clamp_naturality {k : ℕ} {t : Fin (k + 1) →o P}
    (c : Cut A s) (d : Cut A t) (u : Fin (m + 1) →o Fin (k + 1))
    (hu : ∀ i, t (u i) = s i) (i : Fin (m + 1)) (hi : s i ∈ A) :
    c.clamp i = d.clamp (u i) := by
  apply Subtype.ext
  rw [c.clamp_of_mem i hi, d.clamp_of_mem (u i) ((hu i).symm ▸ hi), hu]

noncomputable abbrev label (A : Set P) (hA : IsUpperSet A) {m : ℕ}
    (s : Fin (m + 1) →o P) (h : NormalizedSimplexIdentities) :
    h.object m ⟶ StrictPoset.category (Fin 2) :=
  SimplexComplex.binaryLabel h ((cosieveCharacteristic A hA).comp s)

theorem Cut.fiber_in_final_face (h : NormalizedSimplexIdentities) (c : Cut A s)
    (x : labelFiber (label A hA s h) 1) :
    x.val ∈ Set.range
      (h.map (SimplexComplex.finalFace (Nat.sub_le m c.first.val)).toOrderHom).toFun := by
  have hx := (SimplexComplex.binaryLabel_fullCell_iff h
    ((cosieveCharacteristic A hA).comp s) 1 x.val).mp x.property
  have hs : c.first.val ≤ (SimplexComplex.objectIndex h false x.val).val :=
    (c.mem_iff _).mp ((cosieveCharacteristic_one_iff A hA _).mp hx.1)
  have ht : c.first.val ≤ (SimplexComplex.objectIndex h true x.val).val :=
    (c.mem_iff _).mp ((cosieveCharacteristic_one_iff A hA _).mp hx.2)
  apply SimplexComplex.finalFace_full h (Nat.sub_le m c.first.val) x.val <;> omega

end CosieveSimplex

end Thomason.Construction

end

section

/-! # Compatible inverse maps on the sieve pieces of the oriental presentation -/

namespace Thomason.Construction

open CategoryTheory StrictOmegaCategory

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Agreement on an initial set of vertices gives agreement on every cell
of that full initial face. -/
theorem posetLeg_eq_on_initial {E : Type} [PartialOrder E] {m q : ℕ}
    (hqm : q ≤ m) (s t : Fin (m+1) →o E)
    (hst : ∀ i, i.val ≤ q → s i = t i) (x : h.object m)
    (hx : x ∈ Set.range (h.map (SimplexComplex.initialFace hqm).toOrderHom).toFun) :
    (h.posetLeg s).toFun x = (h.posetLeg t).toFun x := by
  obtain ⟨y, rfl⟩ := hx
  let e := (SimplexComplex.initialFace hqm).toOrderHom
  have he : s.comp e = t.comp e := by
    apply DFunLike.ext
    intro i
    exact hst (e i) (Nat.le_of_lt_succ i.isLt)
  have hs := congrArg (fun f : h.object q ⟶ h.categorification.obj (nerve E) => f.toFun y)
    (h.posetLeg_precomp s e)
  have ht := congrArg (fun f : h.object q ⟶ h.categorification.obj (nerve E) => f.toFun y)
    (h.posetLeg_precomp t e)
  exact hs.trans ((congrArg (fun f => (h.posetLeg f).toFun y) he).trans ht.symm)

end NormalizedSimplexIdentities

namespace SieveSimplex

variable {P : Type} [PartialOrder P] {A : Set P} (hA : IsLowerSet A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

omit [StrictColimitsInput] in
/-- Pulling an oriental label back along an ordinal operator pulls back its vertex list. -/
theorem label_precomp {l m : ℕ} (t : Fin (m+1) →o P)
    (u : Fin (l+1) →o Fin (m+1)) :
    h.map u ≫ label A hA t h = label A hA (t.comp u) h := by
  change h.map u ≫ (h.ordinalLabel m ≫ StrictPoset.map ((sieveCharacteristic A hA).comp t)) = _
  rw [← Category.assoc, h.ordinalLabel_naturality, Category.assoc]
  apply Hom.ext
  funext x
  rfl

/-- The inverse on the zero-labelled piece uses the clamped simplex in A. -/
noncomputable def Cut.back {m : ℕ} {s : Fin (m+1) →o P} (c : Cut A s) :
    labelFiber (label A hA s h) 0 ⟶ h.categorification.obj (nerve A) :=
  labelFiberInclusion (label A hA s h) 0 ≫ h.posetLeg c.clamp

/-- After the original sieve inclusion, the inverse is the original presentation leg. -/
theorem Cut.back_inclusion {m : ℕ} {s : Fin (m+1) →o P} (c : Cut A s) :
    c.back hA h ≫ h.posetMap (subposetInclusion A) =
      labelFiberInclusion (label A hA s h) 0 ≫ h.posetLeg s := by
  apply Hom.ext
  funext x
  have hp := congrArg (fun f : h.object m ⟶ h.categorification.obj (nerve P) => f.toFun x.val)
    (h.posetLeg_postcomp c.clamp (subposetInclusion A))
  change (h.posetMap (subposetInclusion A)).toFun ((h.posetLeg c.clamp).toFun x.val) =
    (h.posetLeg s).toFun x.val
  refine hp.trans ?_
  apply h.posetLeg_eq_on_initial (Nat.le_of_lt_succ c.last.isLt)
  · intro i hi
    exact c.clamp_of_mem i ((c.mem_iff i).mpr hi)
  · exact c.fiber_in_initial_face hA h x

/-- The inverse maps commute with every face and degeneracy operator. -/
theorem Cut.back_naturality {l m : ℕ} (t : Fin (m+1) →o P)
    (u : Fin (l+1) →o Fin (m+1)) (c : Cut A (t.comp u)) (d : Cut A t) :
    labelFiberMap (label A hA (t.comp u) h) (label A hA t h) 0 (h.map u)
      (label_precomp hA h t u) ≫ d.back hA h = c.back hA h := by
  apply Hom.ext
  funext x
  have hp := congrArg (fun f : h.object l ⟶ h.categorification.obj (nerve A) => f.toFun x.val)
    (h.posetLeg_precomp d.clamp u)
  change (h.posetLeg d.clamp).toFun ((h.map u).toFun x.val) =
    (h.posetLeg c.clamp).toFun x.val
  refine hp.trans ?_
  apply h.posetLeg_eq_on_initial (Nat.le_of_lt_succ c.last.isLt)
  · intro i hi
    exact (c.clamp_naturality d u (fun _ => rfl) i ((c.mem_iff i).mpr hi)).symm
  · exact c.fiber_in_initial_face hA h x

end SieveSimplex
end Thomason.Construction

end

section

/-! # Compatible inverses on the final pieces of poset simplexes -/

namespace Thomason.Construction

open CategoryTheory StrictOmegaCategory

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

theorem posetLeg_eq_on_final {E : Type} [PartialOrder E] {m q : ℕ}
    (hqm : q ≤ m) (s t : Fin (m + 1) →o E)
    (hst : ∀ i, m - q ≤ i.val → s i = t i) (x : h.object m)
    (hx : x ∈ Set.range (h.map (SimplexComplex.finalFace hqm).toOrderHom).toFun) :
    (h.posetLeg s).toFun x = (h.posetLeg t).toFun x := by
  obtain ⟨y, rfl⟩ := hx
  let e := (SimplexComplex.finalFace hqm).toOrderHom
  have he : s.comp e = t.comp e := by
    apply DFunLike.ext
    intro i
    exact hst (e i) (by change m - q ≤ m - q + i.val; omega)
  have hs := congrArg (fun f : h.object q ⟶ h.categorification.obj (nerve E) => f.toFun y)
    (h.posetLeg_precomp s e)
  have ht := congrArg (fun f : h.object q ⟶ h.categorification.obj (nerve E) => f.toFun y)
    (h.posetLeg_precomp t e)
  exact hs.trans ((congrArg (fun f => (h.posetLeg f).toFun y) he).trans ht.symm)

end NormalizedSimplexIdentities

namespace CosieveSimplex

variable {P : Type} [PartialOrder P] {A : Set P} (hA : IsUpperSet A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

omit [StrictColimitsInput] in
theorem label_precomp {l m : ℕ} (t : Fin (m + 1) →o P)
    (u : Fin (l + 1) →o Fin (m + 1)) :
    h.map u ≫ label A hA t h = label A hA (t.comp u) h :=
  SieveSimplex.label_precomp hA.compl h t u

noncomputable def Cut.back {m : ℕ} {s : Fin (m + 1) →o P} (c : Cut A s) :
    labelFiber (label A hA s h) 1 ⟶ h.categorification.obj (nerve A) :=
  labelFiberInclusion (label A hA s h) 1 ≫ h.posetLeg c.clamp

theorem Cut.back_inclusion {m : ℕ} {s : Fin (m + 1) →o P} (c : Cut A s) :
    c.back hA h ≫ h.posetMap (subposetInclusion A) =
      labelFiberInclusion (label A hA s h) 1 ≫ h.posetLeg s := by
  apply Hom.ext
  funext x
  have hp := congrArg (fun f : h.object m ⟶ h.categorification.obj (nerve P) => f.toFun x.val)
    (h.posetLeg_postcomp c.clamp (subposetInclusion A))
  change (h.posetMap (subposetInclusion A)).toFun ((h.posetLeg c.clamp).toFun x.val) =
    (h.posetLeg s).toFun x.val
  refine hp.trans ?_
  apply h.posetLeg_eq_on_final (Nat.sub_le m c.first.val)
  · intro i hi
    exact c.clamp_of_mem i ((c.mem_iff i).mpr (by change c.first.val ≤ i.val; omega))
  · exact c.fiber_in_final_face hA h x

theorem Cut.back_naturality {l m : ℕ} (t : Fin (m + 1) →o P)
    (u : Fin (l + 1) →o Fin (m + 1)) (c : Cut A (t.comp u)) (d : Cut A t) :
    labelFiberMap (label A hA (t.comp u) h) (label A hA t h) 1 (h.map u)
      (label_precomp hA h t u) ≫ d.back hA h = c.back hA h := by
  apply Hom.ext
  funext x
  have hp := congrArg (fun f : h.object l ⟶ h.categorification.obj (nerve A) => f.toFun x.val)
    (h.posetLeg_precomp d.clamp u)
  change (h.posetLeg d.clamp).toFun ((h.map u).toFun x.val) =
    (h.posetLeg c.clamp).toFun x.val
  refine hp.trans ?_
  apply h.posetLeg_eq_on_final (Nat.sub_le l c.first.val)
  · intro i hi
    exact (c.clamp_naturality d u (fun _ => rfl) i
      ((c.mem_iff i).mpr (by change c.first.val ≤ i.val; omega))).symm
  · exact c.fiber_in_final_face hA h x

end CosieveSimplex

end Thomason.Construction

end

section

/-! # The inverse simplex maps, including empty fibres -/

namespace Thomason.Construction.CosieveSimplex

open CategoryTheory StrictOmegaCategory

variable {P : Type} [PartialOrder P] (A : Set P) (hA : IsUpperSet A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

omit [StrictColimitsInput] in
/-- A simplex without a cosieve vertex has an empty full one fibre. -/
theorem emptyFiber {m : ℕ} (s : Fin (m+1) →o P) (hs : ¬∃ i, s i ∈ A) :
    IsEmpty (labelFiber (label A hA s h) 1) := by
  refine ⟨fun x => ?_⟩
  have hx := (SimplexComplex.binaryLabel_fullCell_iff h
    ((cosieveCharacteristic A hA).comp s) 1 x.val).mp x.property
  exact hs ⟨_, (cosieveCharacteristic_one_iff A hA _).mp hx.1⟩

/-- Empty fibres have the unique map into the categorified cosieve. -/
noncomputable def emptyBack {m : ℕ} (s : Fin (m+1) →o P) (hs : ¬∃ i, s i ∈ A) :
    labelFiber (label A hA s h) 1 ⟶ h.categorification.obj (nerve A) := by
  have := emptyFiber A hA h s hs
  exact
    { toFun := fun x => isEmptyElim x
      map_face := fun _ _ x => isEmptyElim x
      map_comp := fun _ x => isEmptyElim x }

/-- The inverse is defined on every simplex, including the empty-suffix case. -/
noncomputable def back {m : ℕ} (s : Fin (m+1) →o P) :
    labelFiber (label A hA s h) 1 ⟶ h.categorification.obj (nerve A) := by
  classical
  exact if hs : ∃ i, s i ∈ A then (cut A hA s hs).back hA h else emptyBack A hA h s hs

/-- On a nonempty suffix the inverse is independent of its chosen cut. -/
theorem back_eq_cut {m : ℕ} (s : Fin (m+1) →o P) (c : Cut A s) :
    back A hA h s = c.back hA h := by
  have hs : ∃ i, s i ∈ A := ⟨c.first, (c.mem_iff _).mpr le_rfl⟩
  rw [back, dite_eq_left hs, Subsingleton.elim (cut A hA s hs) c]

/-- The inverse is compatible with the original cosieve inclusion. -/
theorem back_inclusion {m : ℕ} (s : Fin (m+1) →o P) :
    back A hA h s ≫ h.posetMap (subposetInclusion A) =
      labelFiberInclusion (label A hA s h) 1 ≫ h.posetLeg s := by
  classical
  by_cases hs : ∃ i, s i ∈ A
  · rw [back_eq_cut A hA h s (cut A hA s hs)]
    exact (cut A hA s hs).back_inclusion hA h
  · have := emptyFiber A hA h s hs
    apply Hom.ext
    funext x
    exact isEmptyElim x

/-- All inverse maps commute with all ordinal operators. -/
theorem back_naturality {l m : ℕ} (t : Fin (m+1) →o P)
    (u : Fin (l+1) →o Fin (m+1)) :
    labelFiberMap (label A hA (t.comp u) h) (label A hA t h) 1 (h.map u)
      (label_precomp hA h t u) ≫ back A hA h t = back A hA h (t.comp u) := by
  classical
  by_cases hs : ∃ i, (t.comp u) i ∈ A
  · have ht : ∃ i, t i ∈ A := by obtain ⟨i, hi⟩ := hs; exact ⟨u i, hi⟩
    rw [back_eq_cut A hA h t (cut A hA t ht),
      back_eq_cut A hA h (t.comp u) (cut A hA (t.comp u) hs)]
    exact Cut.back_naturality hA h t u _ _
  · have := emptyFiber A hA h (t.comp u) hs
    apply Hom.ext
    funext x
    exact isEmptyElim x

/-- Equal vertex maps give equal inverse values on the same underlying cell. -/
theorem back_apply_congr {m : ℕ} {s t : Fin (m+1) →o P} (he : s = t)
    (x : labelFiber (label A hA s h) 1) (y : labelFiber (label A hA t h) 1)
    (hxy : x.val = y.val) :
    (back A hA h s).toFun x = (back A hA h t).toFun y := by
  subst t
  exact congrArg (back A hA h s).toFun (Subtype.ext hxy)

end Thomason.Construction.CosieveSimplex

end

section

/-! # The inverse simplex maps, including empty fibres -/

namespace Thomason.Construction.SieveSimplex

open CategoryTheory StrictOmegaCategory

variable {P : Type} [PartialOrder P] (A : Set P) (hA : IsLowerSet A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

omit [StrictColimitsInput] in
/-- A simplex without a sieve vertex has an empty full zero fibre. -/
theorem emptyFiber {m : ℕ} (s : Fin (m+1) →o P) (hs : ¬∃ i, s i ∈ A) :
    IsEmpty (labelFiber (label A hA s h) 0) := by
  refine ⟨fun x => ?_⟩
  have hx := (SimplexComplex.binaryLabel_fullCell_iff h
    ((sieveCharacteristic A hA).comp s) 0 x.val).mp x.property
  exact hs ⟨_, (sieveCharacteristic_zero_iff A hA _).mp hx.1⟩

/-- Empty fibres have the unique map into the categorified sieve. -/
noncomputable def emptyBack {m : ℕ} (s : Fin (m+1) →o P) (hs : ¬∃ i, s i ∈ A) :
    labelFiber (label A hA s h) 0 ⟶ h.categorification.obj (nerve A) := by
  have := emptyFiber A hA h s hs
  exact
    { toFun := fun x => isEmptyElim x
      map_face := fun _ _ x => isEmptyElim x
      map_comp := fun _ x => isEmptyElim x }

/-- The inverse is defined on every simplex, including the empty-prefix case. -/
noncomputable def back {m : ℕ} (s : Fin (m+1) →o P) :
    labelFiber (label A hA s h) 0 ⟶ h.categorification.obj (nerve A) := by
  classical
  exact if hs : ∃ i, s i ∈ A then (cut A hA s hs).back hA h else emptyBack A hA h s hs

/-- On a nonempty prefix the inverse is independent of its chosen cut. -/
theorem back_eq_cut {m : ℕ} (s : Fin (m+1) →o P) (c : Cut A s) :
    back A hA h s = c.back hA h := by
  have hs : ∃ i, s i ∈ A := ⟨c.last, (c.mem_iff _).mpr le_rfl⟩
  rw [back, dite_eq_left hs, Subsingleton.elim (cut A hA s hs) c]

/-- The inverse is compatible with the original sieve inclusion. -/
theorem back_inclusion {m : ℕ} (s : Fin (m+1) →o P) :
    back A hA h s ≫ h.posetMap (subposetInclusion A) =
      labelFiberInclusion (label A hA s h) 0 ≫ h.posetLeg s := by
  classical
  by_cases hs : ∃ i, s i ∈ A
  · rw [back_eq_cut A hA h s (cut A hA s hs)]
    exact (cut A hA s hs).back_inclusion hA h
  · have := emptyFiber A hA h s hs
    apply Hom.ext
    funext x
    exact isEmptyElim x

/-- All inverse maps commute with all ordinal operators. -/
theorem back_naturality {l m : ℕ} (t : Fin (m+1) →o P)
    (u : Fin (l+1) →o Fin (m+1)) :
    labelFiberMap (label A hA (t.comp u) h) (label A hA t h) 0 (h.map u)
      (label_precomp hA h t u) ≫ back A hA h t = back A hA h (t.comp u) := by
  classical
  by_cases hs : ∃ i, (t.comp u) i ∈ A
  · have ht : ∃ i, t i ∈ A := by obtain ⟨i, hi⟩ := hs; exact ⟨u i, hi⟩
    rw [back_eq_cut A hA h t (cut A hA t ht),
      back_eq_cut A hA h (t.comp u) (cut A hA (t.comp u) hs)]
    exact Cut.back_naturality hA h t u _ _
  · have := emptyFiber A hA h (t.comp u) hs
    apply Hom.ext
    funext x
    exact isEmptyElim x

/-- Equal vertex maps give equal inverse values on the same underlying cell. -/
theorem back_apply_congr {m : ℕ} {s t : Fin (m+1) →o P} (he : s = t)
    (x : labelFiber (label A hA s h) 0) (y : labelFiber (label A hA t h) 0)
    (hxy : x.val = y.val) :
    (back A hA h s).toFun x = (back A hA h t).toFun y := by
  subst t
  exact congrArg (back A hA h s).toFun (Subtype.ext hxy)

end Thomason.Construction.SieveSimplex

end

section

/-! # Extending a functor from the zero fibre into the terminal cone -/

namespace Thomason.Construction.StrictOmegaCategory.TerminalCone

open CategoryTheory

variable {X C : StrictOmegaCategory.{0}}
variable (p : X ⟶ StrictPoset.category (Fin 2)) (f : labelFiber p 0 ⟶ C)

def extendCell (x : X) : Cell C :=
  if hl : lastLabel p x = 0 then .old (f.toFun (zeroCell p x hl))
  else if hf : firstLabel p x = 0 then .arrow (f.toOneFunctor.obj (zeroSource p x hf))
  else .tip

theorem extendCell_zero (x : X) (hl : lastLabel p x = 0) :
    extendCell p f x = .old (f.toFun (zeroCell p x hl)) := by
  simp only [extendCell, dite_eq_left hl]

theorem extendCell_cross (x : X) (hf : firstLabel p x = 0) (hl : lastLabel p x ≠ 0) :
    extendCell p f x = .arrow (f.toOneFunctor.obj (zeroSource p x hf)) := by
  simp only [extendCell, dite_eq_right hl, dite_eq_left hf]

theorem extendCell_one (x : X) (hf : firstLabel p x ≠ 0) : extendCell p f x = .tip := by
  have hl : lastLabel p x ≠ 0 := by have ho := label_ordered p x; omega
  simp only [extendCell, dite_eq_right hl, dite_eq_right hf]

theorem zeroCell_face (a : Bool) (n : ℕ) (x : X) (hl : lastLabel p x = 0)
    (hface : lastLabel p (X.face a n x) = 0) :
    zeroCell p (X.face a n x) hface = (labelFiber p 0).face a n (zeroCell p x hl) :=
  Subtype.ext rfl

theorem zeroSource_face_succ (a : Bool) (n : ℕ) (x : X)
    (hf : firstLabel p x = 0) (hface : firstLabel p (X.face a (n+1) x) = 0) :
    zeroSource p (X.face a (n+1) x) hface = zeroSource p x hf := by
  apply Subtype.ext
  apply Subtype.ext
  exact (X.globular false a 0 (n+1) x).trans (ite_eq_left (Nat.zero_lt_succ n))

theorem extendCell_face (a : Bool) (n : ℕ) (x : X) :
    extendCell p f (X.face a n x) = face a n (extendCell p f x) := by
  by_cases hl : lastLabel p x = 0
  · have hf : firstLabel p x = 0 := by have ho := label_ordered p x; omega
    have hface : lastLabel p (X.face a n x) = 0 := by
      cases n <;> simp [hf, hl]
    rw [extendCell_zero p f _ hface, extendCell_zero p f x hl]
    exact congrArg Cell.old ((congrArg f.toFun (zeroCell_face p a n x hl hface)).trans
      (f.map_face a n (zeroCell p x hl)))
  · by_cases hf : firstLabel p x = 0
    · rw [extendCell_cross p f x hf hl]
      cases n with
      | zero =>
        cases a with
        | false =>
          rw [extendCell_zero p f _ (by simpa using hf)]
          rfl
        | true =>
          rw [extendCell_one p f _ (by simpa using hl)]
          rfl
      | succ n =>
        rw [extendCell_cross p f _ (by simpa using hf) (by simpa using hl)]
        exact congrArg (fun z => Cell.arrow (f.toOneFunctor.obj z))
          (zeroSource_face_succ p a n x hf _)
    · rw [extendCell_one p f x hf, extendCell_one p f _ (by
        cases n with
        | zero =>
          cases a
          · simpa using hf
          · simpa using hl
        | succ n => simpa using hf)]
      rfl

end Thomason.Construction.StrictOmegaCategory.TerminalCone

end

section

/-! # The zero-fibre extension preserves strict compositions -/

namespace Thomason.Construction.StrictOmegaCategory.TerminalCone

open CategoryTheory

variable {X C : StrictOmegaCategory.{0}}
variable (p : X ⟶ StrictPoset.category (Fin 2)) (f : labelFiber p 0 ⟶ C)

theorem zeroCell_comp (n : ℕ) (x y : X) (h : X.target n x = X.source n y)
    (hx : lastLabel p x = 0) (hy : lastLabel p y = 0)
    (hz : lastLabel p (X.comp n x y h) = 0) :
    zeroCell p (X.comp n x y h) hz = (labelFiber p 0).comp n
      (zeroCell p x hx) (zeroCell p y hy) (Subtype.ext h) := Subtype.ext rfl

theorem zeroSource_comp (n : ℕ) (x y : X) (h : X.target n x = X.source n y)
    (hx : firstLabel p x = 0) (hz : firstLabel p (X.comp n x y h) = 0) :
    zeroSource p (X.comp n x y h) hz = zeroSource p x hx := by
  apply Subtype.ext
  apply Subtype.ext
  cases n with
  | zero => exact X.source_comp 0 x y h
  | succ n => exact X.zero_face_comp_succ false n x y h

theorem map_zeroSource (x : X) (hf : firstLabel p x = 0) (hl : lastLabel p x = 0) :
    f.toOneFunctor.obj (zeroSource p x hf) = C.boundaryObject false (f.toFun (zeroCell p x hl)) :=
  Subtype.ext (f.map_face false 0 (zeroCell p x hl))

theorem extendCell_comp (n : ℕ) (x y : X) (h : X.target n x = X.source n y)
    (h' : face true n (extendCell p f x) = face false n (extendCell p f y)) :
    extendCell p f (X.comp n x y h) = comp n (extendCell p f x) (extendCell p f y) h' := by
  generalize ex : extendCell p f x = cx at h' ⊢
  generalize ey : extendCell p f y = cy at h' ⊢
  cases n with
  | zero =>
    have hc := label_composable_zero p x y h
    by_cases hly : lastLabel p y = 0
    · have hlx : lastLabel p x = 0 := by have ho := label_ordered p y; omega
      have hlz : lastLabel p (X.comp 0 x y h) = 0 := by simpa using hly
      rw [extendCell_zero p f x hlx] at ex
      rw [extendCell_zero p f y hly] at ey
      subst cx cy
      simp only [extendCell_zero p f _ hlz, comp]
      apply congrArg Cell.old
      exact (congrArg f.toFun (zeroCell_comp p 0 x y h hlx hly hlz)).trans
        (f.map_comp 0 (zeroCell p x hlx) (zeroCell p y hly) _ _)
    · by_cases hfx : firstLabel p x = 0
      · have hfz : firstLabel p (X.comp 0 x y h) = 0 := by simpa using hfx
        have hlz : lastLabel p (X.comp 0 x y h) ≠ 0 := by simpa using hly
        by_cases hlx : lastLabel p x = 0
        · have hfy : firstLabel p y = 0 := hc.symm.trans hlx
          rw [extendCell_zero p f x hlx] at ex
          rw [extendCell_cross p f y hfy hly] at ey
          subst cx cy
          simp only [extendCell_cross p f _ hfz hlz, comp]
          exact congrArg Cell.arrow ((congrArg f.toOneFunctor.obj
            (zeroSource_comp p 0 x y h hfx hfz)).trans (map_zeroSource p f x hfx hlx))
        · have hfy : firstLabel p y ≠ 0 := fun he => hlx (hc.trans he)
          rw [extendCell_cross p f x hfx hlx] at ex
          rw [extendCell_one p f y hfy] at ey
          subst cx cy
          simp only [extendCell_cross p f _ hfz hlz, comp]
          exact congrArg (fun z => Cell.arrow (f.toOneFunctor.obj z))
            (zeroSource_comp p 0 x y h hfx hfz)
      · have hfy : firstLabel p y ≠ 0 := by have ho := label_ordered p x; omega
        have hfz : firstLabel p (X.comp 0 x y h) ≠ 0 := by simpa using hfx
        rw [extendCell_one p f x hfx] at ex
        rw [extendCell_one p f y hfy] at ey
        subst cx cy
        simp only [extendCell_one p f _ hfz, comp]
  | succ n =>
    have hc := labels_composable_succ p n x y h
    by_cases hlx : lastLabel p x = 0
    · have hly : lastLabel p y = 0 := hc.2.symm.trans hlx
      have hlz : lastLabel p (X.comp (n+1) x y h) = 0 := by simpa using hlx
      rw [extendCell_zero p f x hlx] at ex
      rw [extendCell_zero p f y hly] at ey
      subst cx cy
      simp only [extendCell_zero p f _ hlz, comp]
      apply congrArg Cell.old
      exact (congrArg f.toFun (zeroCell_comp p (n+1) x y h hlx hly hlz)).trans
        (f.map_comp (n+1) (zeroCell p x hlx) (zeroCell p y hly) _ _)
    · by_cases hfx : firstLabel p x = 0
      · have hfy : firstLabel p y = 0 := hc.1.symm.trans hfx
        have hly : lastLabel p y ≠ 0 := fun he => hlx (hc.2.trans he)
        have hfz : firstLabel p (X.comp (n+1) x y h) = 0 := by simpa using hfx
        have hlz : lastLabel p (X.comp (n+1) x y h) ≠ 0 := by simpa using hlx
        rw [extendCell_cross p f x hfx hlx] at ex
        rw [extendCell_cross p f y hfy hly] at ey
        subst cx cy
        simp only [extendCell_cross p f _ hfz hlz, comp]
        exact congrArg (fun z => Cell.arrow (f.toOneFunctor.obj z))
          (zeroSource_comp p (n+1) x y h hfx hfz)
      · have hfy : firstLabel p y ≠ 0 := fun he => hfx (hc.1.trans he)
        have hfz : firstLabel p (X.comp (n+1) x y h) ≠ 0 := by simpa using hfx
        rw [extendCell_one p f x hfx] at ex
        rw [extendCell_one p f y hfy] at ey
        subst cx cy
        simp only [extendCell_one p f _ hfz, comp]

/-- The strict extension of a functor from the actual zero fibre. -/
def extend : X ⟶ category C where
  toFun := extendCell p f
  map_face := extendCell_face p f
  map_comp := extendCell_comp p f

end Thomason.Construction.StrictOmegaCategory.TerminalCone

end

section

/-! # The terminal cone's universal property over the walking arrow -/

namespace Thomason.Construction.StrictOmegaCategory.TerminalCone

open CategoryTheory

variable {X C : StrictOmegaCategory.{0}}
variable (p : X ⟶ StrictPoset.category (Fin 2))

theorem extend_label (f : labelFiber p 0 ⟶ C) : extend p f ≫ label C = p := by
  apply Hom.ext
  funext x
  change labelCell (extendCell p f x) = p.toFun x
  by_cases hl : lastLabel p x = 0
  · rw [extendCell_zero p f x hl]
    apply StrictPoset.Cell.ext
    · have ho := label_ordered p x
      change 0 = firstLabel p x
      omega
    · exact hl.symm
  · by_cases hf : firstLabel p x = 0
    · rw [extendCell_cross p f x hf hl]
      apply StrictPoset.Cell.ext
      · exact hf.symm
      · change 1 = lastLabel p x
        omega
    · rw [extendCell_one p f x hf]
      apply StrictPoset.Cell.ext
      · change 1 = firstLabel p x
        omega
      · change 1 = lastLabel p x
        omega

noncomputable def restrict (g : X ⟶ category C) (hg : g ≫ label C = p) :
    labelFiber p 0 ⟶ C :=
  labelFiberMap p (label C) 0 g hg ≫ (zeroFiberIso C).inv

theorem old_restrict (g : X ⟶ category C) (hg : g ≫ label C = p) (x : labelFiber p 0) :
    Cell.old ((restrict p g hg).toFun x) = g.toFun x.val := by
  have hi := congrArg (fun k : labelFiber (label C) 0 ⟶ labelFiber (label C) 0 =>
    (k.toFun ((labelFiberMap p (label C) 0 g hg).toFun x)).val)
    (zeroFiberIso C).inv_hom_id
  exact hi

theorem restrict_extend (f : labelFiber p 0 ⟶ C) :
    restrict p (extend p f) (extend_label p f) = f := by
  apply Hom.ext
  funext x
  apply Cell.old.inj
  have hx := (fullCell_label_iff p 0 x.val).mp x.property
  have hl : lastLabel p x.val = 0 := congrArg StrictPoset.Cell.last hx
  exact (old_restrict p (extend p f) (extend_label p f) x).trans
    (extendCell_zero p f x.val hl)

theorem extend_restrict (g : X ⟶ category C) (hg : g ≫ label C = p) :
    extend p (restrict p g hg) = g := by
  apply Hom.ext
  funext x
  have hp : labelCell (g.toFun x) = p.toFun x :=
    congrArg (fun k : X ⟶ StrictPoset.category (Fin 2) => k.toFun x) hg
  change extendCell p (restrict p g hg) x = g.toFun x
  cases he : g.toFun x with
  | old c =>
    have hl : lastLabel p x = 0 := by
      rw [he] at hp
      exact (congrArg StrictPoset.Cell.last hp).symm
    rw [extendCell_zero p _ x hl]
    exact (old_restrict p g hg (zeroCell p x hl)).trans he
  | tip =>
    have hf : firstLabel p x ≠ 0 := by
      rw [he] at hp
      have hi := congrArg StrictPoset.Cell.first hp
      change 1 = firstLabel p x at hi
      omega
    exact extendCell_one p _ x hf
  | arrow a =>
    have hf : firstLabel p x = 0 := by
      rw [he] at hp
      exact (congrArg StrictPoset.Cell.first hp).symm
    have hl : lastLabel p x ≠ 0 := by
      rw [he] at hp
      have hi := congrArg StrictPoset.Cell.last hp
      change 1 = lastLabel p x at hi
      omega
    rw [extendCell_cross p _ x hf hl]
    apply congrArg Cell.arrow
    apply Subtype.ext
    have hs := old_restrict p g hg (zeroCell p (X.face false 0 x) (by simpa using hf))
    have hm := g.map_face false 0 x
    rw [he] at hm
    exact Cell.old.inj (hs.trans hm)

end Thomason.Construction.StrictOmegaCategory.TerminalCone

end

end OAI
