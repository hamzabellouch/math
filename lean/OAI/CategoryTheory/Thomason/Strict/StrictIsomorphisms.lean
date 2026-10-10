import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeUniversal
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FinCases

namespace OAI

section

/-!
# The cosimplicial orientals

These are the strict realizations of the explicit normalized simplex complexes.
The only hypotheses are the two classical normalized-chain identities specified
below (Steiner, *Orientals*, 2007, Section 3 and Section 4 before Theorem 4.1).
Functoriality, including maps with degenerate images, is proved here.
-/

namespace Thomason.Construction

open CategoryTheory

/-- The classical normalized-chain identities. -/
structure NormalizedSimplexIdentities : Prop where
  squared (m : ℕ) : SimplexComplex.BoundarySquared m
  naturality {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    SimplexComplex.BoundaryNaturality f

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

noncomputable def object (m : ℕ) : StrictOmegaCategory :=
  SimplexComplex.oriental m (h.squared m)

noncomputable def map {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    h.object m ⟶ h.object n :=
  (SimplexComplex.directedMap (h.squared m) (h.squared n) f (h.naturality f)).realization

theorem map_id (m : ℕ) : h.map (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) =
    𝟙 (h.object m) := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply DirectedComplex.Cell.ext
  funext a p
  exact SimplexComplex.mapChains_id (x.table a p)

theorem map_comp {m n k : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (n + 1) →o Fin (k + 1)) : h.map (g.comp f) = h.map f ≫ h.map g := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply DirectedComplex.Cell.ext
  funext a p
  exact (SimplexComplex.mapChains_comp f g (x.table a p)).symm

/-- The actual oriental cosimplicial object. -/
noncomputable def cosimplicial : SimplexCategory ⥤ StrictOmegaCategory.{0} where
  obj m := h.object m.len
  map f := h.map f.toOrderHom
  map_id m := h.map_id m.len
  map_comp f g := h.map_comp f.toOrderHom g.toOrderHom

/-- There are no normalized p-simplices in an m-simplex when p > m. -/
theorem chains_eq_zero_above {m p : ℕ} (hmp : m < p) (x : SimplexComplex.Chains m p) :
    x = 0 := by
  apply Finsupp.ext
  intro s
  have hc := Fintype.card_le_of_injective s s.injective
  simp only [Fintype.card_fin] at hc
  omega

/-- The top source and target coincide because the next chain group vanishes. -/
theorem top_faces_equal (m : ℕ) (x : h.object m) : x.table false m = x.table true m := by
  have hx : x.table false (m + 1) = 0 := chains_eq_zero_above (by omega) _
  have hz : (SimplexComplex.directedComplex m (h.squared m)).differential m
      (x.table false (m + 1)) = 0 :=
    (congrArg ((SimplexComplex.directedComplex m (h.squared m)).differential m) hx).trans
      (map_zero _)
  exact (sub_eq_zero.mp ((x.boundary false m).symm.trans hz)).symm

/-- Each oriental has the expected finite dimension. This follows directly
from the normalized-chain construction, without a freeness hypothesis. -/
theorem isTruncated (m : ℕ) : (h.object m).IsTruncated m := by
  intro x
  have hf (a : Bool) : (h.object m).face a m x = x := by
    apply DirectedComplex.Cell.ext
    funext b p
    change x.cutTable a m b p = x.table b p
    unfold DirectedComplex.Cell.cutTable
    split_ifs with hp he
    · rfl
    · subst p
      cases a <;> cases b
      · rfl
      · exact h.top_faces_equal m x
      · exact (h.top_faces_equal m x).symm
      · rfl
    · exact (chains_eq_zero_above (by omega) _).symm
  exact ⟨hf false, hf true⟩

end NormalizedSimplexIdentities
end Thomason.Construction

end

section

/-!
# The Street nerve and its realization weak equivalences

The m-simplices are strict functors from the concrete m-th oriental.
The normalized chain identities define its simplicial operators.
-/

namespace Thomason.Construction

open CategoryTheory Opposite

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

/-- Restrict Yoneda to the actual oriental cosimplicial object. -/
noncomputable def streetNerve : StrictOmegaCategory.{0} ⥤ SSet.{0} :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj h.cosimplicial.op

@[simp]
theorem streetNerve_obj (C : StrictOmegaCategory.{0}) (m : SimplexCategory) :
    (h.streetNerve.obj C).obj (op m) = (h.object m.len ⟶ C) := rfl

@[simp]
theorem streetNerve_map_app {C D : StrictOmegaCategory.{0}} (f : C ⟶ D)
    (m : SimplexCategory) (x : h.object m.len ⟶ C) :
    (h.streetNerve.map f).app (op m) x = x ≫ f := rfl

/-- The same Street nerve on strict finite-dimensional categories. -/
noncomputable def finiteStreetNerve (n : ℕ) :
    StrictOmegaCategory.Truncated.{0} n ⥤ SSet.{0} :=
  StrictOmegaCategory.inclusion n ⋙ h.streetNerve

/-- The prescribed weak equivalences for strict omega-categories, defined
through their Street nerves and geometric realization. -/
noncomputable def streetWeakEquivalences : MorphismProperty StrictOmegaCategory.{0} :=
  realizationWeakEquivalences.inverseImage h.streetNerve

/-- The Street comparison uses the two-out-of-three property for realization
weak equivalences and the canonical extension equivalence of
Goerss--Jardine III.4.6. -/
theorem streetWeakEquivalences_eq_ex_twice
    [realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty]
    (hj : ∀ X, realizationWeakEquivalences.{0} (canonicalExtension.app X)) :
    h.streetWeakEquivalences =
      realizationWeakEquivalences.inverseImage (h.streetNerve ⋙ SSet.ex ⋙ SSet.ex) :=
  canonical_nerve_weak_equivalences_eq realizationWeakEquivalences h.streetNerve hj

/-- This equality is uniform in every finite dimension. -/
theorem finiteStreetWeakEquivalences_eq_ex_twice (n : ℕ)
    [realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty]
    (hj : ∀ X, realizationWeakEquivalences.{0} (canonicalExtension.app X)) :
    realizationWeakEquivalences.inverseImage (h.finiteStreetNerve n) =
      realizationWeakEquivalences.inverseImage (h.finiteStreetNerve n ⋙ SSet.ex ⋙ SSet.ex) :=
  canonical_nerve_weak_equivalences_eq realizationWeakEquivalences (h.finiteStreetNerve n) hj

end NormalizedSimplexIdentities
end Thomason.Construction

end

section

/-! # Iterated interchange for matched lists

This is the list form of strict interchange used to normalize generated
expressions: two strings composed in a higher dimension can be composed
term by term in a lower dimension.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

/-- A pair with its actual lower-dimensional matching equation. -/
def MatchedPair (C : StrictOmegaCategory.{0}) (m : ℕ) :=
  {p : C × C // C.target m p.1 = C.source m p.2}

namespace MatchedPair

variable {C : StrictOmegaCategory.{0}} {m : ℕ}

def left (p : MatchedPair C m) : C := p.val.1
def right (p : MatchedPair C m) : C := p.val.2
def composite (p : MatchedPair C m) : C := C.comp m p.left p.right p.property

end MatchedPair

private theorem compositeList_singleton_eq {C : StrictOmegaCategory.{0}} {r : ℕ}
    {a x : C} (h : CompositeList C r [a] x) : x = a := by
  cases h with
  | singleton => rfl
  | cons a htail hmatch => exact False.elim (htail.nonempty rfl)

/-- Strict interchange applied simultaneously along two matching strings. -/
theorem compositeList_exchange {C : StrictOmegaCategory.{0}} {m r : ℕ}
    (hmr : m < r) (ps : List (MatchedPair C m)) {x y : C}
    (hx : CompositeList C r (ps.map MatchedPair.left) x)
    (hy : CompositeList C r (ps.map MatchedPair.right) y)
    (hxy : C.target m x = C.source m y) :
    CompositeList C r (ps.map MatchedPair.composite) (C.comp m x y hxy) := by
  induction ps generalizing x y with
  | nil => exact False.elim (hx.nonempty rfl)
  | cons p ps ih =>
    cases ps with
    | nil =>
      have hxx := compositeList_singleton_eq hx
      have hyy := compositeList_singleton_eq hy
      subst x
      subst y
      exact .singleton p.composite
    | cons q qs =>
      cases hx with
      | @cons x0 xs x1 hxt hxx =>
        cases hy with
        | @cons y0 ys y1 hyt hyy =>
          have htail : C.target m x1 = C.source m y1 :=
            (C.lower_faces_equal true hmr _ _ hxx).symm.trans
              (p.property.trans (C.lower_faces_equal false hmr _ _ hyy))
          have ht := ih hxt hyt htail
          have hp : C.target m p.left = C.source m p.right := p.property
          have hh : C.target m (C.target r p.left) = C.source m (C.target r p.right) := by
            simpa only [target, source, C.globular, hmr, ite_true,
              MatchedPair.left, MatchedPair.right] using p.property
          have hl : C.target m (C.source r x1) = C.source m (C.source r y1) := by
            simpa only [target, source, C.globular, hmr, ite_true] using htail
          have hcross : C.target r p.composite = C.source r (C.comp m _ _ htail) := by
            change C.face true r (C.comp m p.left p.right hp) =
              C.face false r (C.comp m x1 y1 htail)
            rw [C.face_comp true r m hmr p.left p.right hp hh,
              C.face_comp false r m hmr x1 y1 htail hl]
            simp only [hxx, hyy]
          have hres := CompositeList.cons p.composite ht hcross
          change CompositeList C r (p.composite :: List.map MatchedPair.composite (q :: qs))
            (C.comp r (C.comp m p.left p.right hp) (C.comp m x1 y1 htail) hcross) at hres
          rw [C.interchange m r hmr p.left p.right x1 y1 hp htail hxx hyy hcross hxy] at hres
          exact hres

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Padding strict composition strings by their endpoint identities

These are the literal padded strings used by the generated-expression
normalization argument. Every matching equation is retained.
-/

namespace Thomason.Construction.StrictOmegaCategory.CompositeList

variable {C : StrictOmegaCategory.{0}} {r : ℕ} {xs : List C} {x : C}

/-- Appending any number of target identities retains the same composite. -/
theorem append_targets (h : CompositeList C r xs x) (k : ℕ) :
    CompositeList C r (xs ++ List.replicate k (C.target r x)) x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hm : C.target r x = C.source r (C.target r x) :=
      (C.face_face_same false true r x).symm
    have hh := ih.append (.singleton (C.target r x)) hm
    rw [C.right_unit r x hm] at hh
    simpa only [List.replicate_succ', List.append_assoc] using hh

/-- Prepending any number of source identities retains the same composite. -/
theorem prepend_sources (h : CompositeList C r xs x) (k : ℕ) :
    CompositeList C r (List.replicate k (C.source r x) ++ xs) x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hm : C.target r (C.source r x) = C.source r x :=
      C.face_face_same true false r x
    have hh := CompositeList.cons (C.source r x) ih hm
    rw [C.left_unit r x hm] at hh
    simpa only [List.replicate_succ, List.cons_append] using hh

/-- A common dimension bound is preserved by every nonempty strict string. -/
theorem dimensionLE (h : CompositeList C r xs x) (n : ℕ)
    (hd : ∀ y ∈ xs, C.DimensionLE n y) : C.DimensionLE n x := by
  induction h with
  | singleton x => exact hd x (by simp)
  | @cons y ys z hz hyz ih =>
    apply C.dimensionLE_comp_all (hd y (by simp))
    exact ih (fun w hw => hd w (by simp [hw]))

end Thomason.Construction.StrictOmegaCategory.CompositeList

end

section

/-! # Single-stage representatives for filtered strict diagrams

The candidate underlying carrier is the ordinary filtered colimit of the
cell sets. Faces descend to it, finite dimension is preserved, and matching
boundaries or a specified dimension bound can be realized at one stage.
These are the concrete inputs for constructing its strict compositions.
-/

namespace Thomason.Construction.StrictOmegaCategory.FilteredColimit

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory

/-- The underlying cells, with every strict functor acting by its actual function. -/
abbrev cells : StrictOmegaCategory.{0} ⥤ Type where
  obj C := C.Cell
  map f := ↾f.toFun

variable {J : Type} [Category.{0} J] (F : J ⥤ StrictOmegaCategory.{0})

abbrev cellDiagram : J ⥤ Type := F ⋙ cells

noncomputable abbrev Carrier : Type := colimit (cellDiagram F)

noncomputable def ι (j : J) (x : F.obj j) : Carrier F :=
  colimit.ι (cellDiagram F) j x

@[simp] theorem ι_map {j k : J} (f : j ⟶ k) (x : F.obj j) :
    ι F k ((F.map f).toFun x) = ι F j x :=
  congr_hom (colimit.w (cellDiagram F) f) x

theorem exists_representative (x : Carrier F) :
    ∃ (j : J) (y : F.obj j), ι F j y = x :=
  Types.jointly_surjective' x

variable [IsFiltered J]

/-- Equality of original cells is witnessed at a common later stage. -/
theorem ι_eq_iff {j k : J} (x : F.obj j) (y : F.obj k) :
    ι F j x = ι F k y ↔
      ∃ (l : J) (f : j ⟶ l) (g : k ⟶ l), (F.map f).toFun x = (F.map g).toFun y :=
  Types.FilteredColimit.colimit_eq_iff (cellDiagram F)

theorem ι_eq_iff_same_stage {j : J} (x y : F.obj j) :
    ι F j x = ι F j y ↔ ∃ (k : J) (f : j ⟶ k),
      (F.map f).toFun x = (F.map f).toFun y :=
  Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (cellDiagram F)) x y

/-- Two equalities at a stage can be made literal at the same later stage. -/
theorem eventually_eq₂ {j : J} (x₁ y₁ x₂ y₂ : F.obj j)
    (h₁ : ι F j x₁ = ι F j y₁) (h₂ : ι F j x₂ = ι F j y₂) :
    ∃ (k : J) (f : j ⟶ k),
      (F.map f).toFun x₁ = (F.map f).toFun y₁ ∧
      (F.map f).toFun x₂ = (F.map f).toFun y₂ := by
  obtain ⟨k₁, f₁, hf₁⟩ := (ι_eq_iff_same_stage F x₁ y₁).mp h₁
  obtain ⟨k₂, f₂, hf₂⟩ := (ι_eq_iff_same_stage F x₂ y₂).mp h₂
  obtain ⟨k, g₁, g₂, hg⟩ := IsFiltered.span f₁ f₂
  refine ⟨k, f₁ ≫ g₁, ?_, ?_⟩
  · rw [F.map_comp]
    exact congrArg (F.map g₁).toFun hf₁
  · rw [hg]
    rw [F.map_comp]
    exact congrArg (F.map g₂).toFun hf₂

/-- A pair of colimit cells has representatives in one common stage. -/
theorem exists_representatives₂ (x y : Carrier F) :
    ∃ (j : J) (a b : F.obj j), ι F j a = x ∧ ι F j b = y :=
  Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (colimit.isColimit (cellDiagram F)) x y

noncomputable def faceCocone (a : Bool) (n : ℕ) : Cocone (cellDiagram F) where
  pt := Carrier F
  ι := {
    app j := ↾fun x => ι F j ((F.obj j).face a n x)
    naturality j k f := by
      ext x
      change ι F k ((F.obj k).face a n ((F.map f).toFun x)) =
        ι F j ((F.obj j).face a n x)
      rw [← (F.map f).map_face, ι_map] }

noncomputable def face (a : Bool) (n : ℕ) : Carrier F → Carrier F :=
  colimit.desc (cellDiagram F) (faceCocone F a n)

omit [IsFiltered J] in
@[simp] theorem face_ι (a : Bool) (n : ℕ) (j : J) (x : F.obj j) :
    face F a n (ι F j x) = ι F j ((F.obj j).face a n x) :=
  congr_hom (colimit.ι_desc (faceCocone F a n) j) x

omit [IsFiltered J] in
theorem globular (a b : Bool) (m n : ℕ) (x : Carrier F) :
    face F a m (face F b n x) = if m < n then face F a m x else face F b n x := by
  obtain ⟨j, x, rfl⟩ := exists_representative F x
  simp only [face_ι]
  rw [(F.obj j).globular]
  split_ifs <;> rfl

omit [IsFiltered J] in
theorem finite_dimension (x : Carrier F) :
    ∃ n, face F false n x = x ∧ face F true n x = x := by
  obtain ⟨j, x, rfl⟩ := exists_representative F x
  obtain ⟨n, hs, ht⟩ := (F.obj j).finite_dimension x
  exact ⟨n, by rw [face_ι, hs], by rw [face_ι, ht]⟩

/-- A dimension bound in the colimit becomes a literal bound on a later representative. -/
theorem eventually_dimensionLE {j : J} (n : ℕ) (x : F.obj j)
    (hs : face F false n (ι F j x) = ι F j x)
    (ht : face F true n (ι F j x) = ι F j x) :
    ∃ (k : J) (f : j ⟶ k), (F.obj k).DimensionLE n ((F.map f).toFun x) := by
  rw [face_ι] at hs ht
  obtain ⟨k, f, hf₀, hf₁⟩ := eventually_eq₂ F _ _ _ _ hs ht
  refine ⟨k, f, ?_, ?_⟩
  · exact ((F.map f).map_face false n x).symm.trans hf₀
  · exact ((F.map f).map_face true n x).symm.trans hf₁

/-- Matching colimit boundaries have representatives with matching boundaries
in a single original strict category. -/
theorem exists_composable_representatives (n : ℕ) (x y : Carrier F)
    (h : face F true n x = face F false n y) :
    ∃ (j : J) (a b : F.obj j),
      (F.obj j).target n a = (F.obj j).source n b ∧ ι F j a = x ∧ ι F j b = y := by
  obtain ⟨j, a, b, ha, hb⟩ := exists_representatives₂ F x y
  rw [← ha, ← hb, face_ι, face_ι] at h
  obtain ⟨k, f, hf⟩ := (ι_eq_iff_same_stage F _ _).mp h
  refine ⟨k, (F.map f).toFun a, (F.map f).toFun b, ?_, ?_, ?_⟩
  · exact ((F.map f).map_face true n a).symm.trans
      (hf.trans ((F.map f).map_face false n b))
  · exact (ι_map F f a).trans ha
  · exact (ι_map F f b).trans hb

end Thomason.Construction.StrictOmegaCategory.FilteredColimit

end

section

/-! # Simultaneous finite-stage data in a filtered strict diagram -/

namespace Thomason.Construction.StrictOmegaCategory.FilteredColimit

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Category.{0} J] (F : J ⥤ StrictOmegaCategory.{0}) [IsFiltered J]

/-- Every finite family of colimit cells is represented at one original stage. -/
theorem exists_representatives_fin (m : ℕ) (s : Fin m → Carrier F) :
    ∃ (j : J) (v : Fin m → F.obj j), ∀ a, ι F j (v a) = s a := by
  induction m with
  | zero =>
    let j : J := Classical.choice IsFiltered.nonempty
    exact ⟨j, Fin.elim0, fun a => Fin.elim0 a⟩
  | succ m ih =>
    obtain ⟨j, x, hx⟩ := exists_representative F (s 0)
    obtain ⟨k, y, hy⟩ := ih (fun a => s a.succ)
    let l := IsFiltered.max j k
    let v : Fin (m + 1) → F.obj l := Fin.cases
      ((F.map (IsFiltered.leftToMax j k)).toFun x)
      (fun a => (F.map (IsFiltered.rightToMax j k)).toFun (y a))
    refine ⟨l, v, ?_⟩
    intro a
    refine Fin.cases ?_ (fun b => ?_) a
    · exact (ι_map F _ x).trans hx
    · exact (ι_map F _ (y b)).trans (hy b)

/-- Any finite list of colimit equalities holds literally after one map. -/
theorem eventually_eq_fin {j : J} (m : ℕ) (x y : Fin m → F.obj j)
    (h : ∀ a, ι F j (x a) = ι F j (y a)) :
    ∃ (k : J) (f : j ⟶ k), ∀ a, (F.map f).toFun (x a) = (F.map f).toFun (y a) := by
  induction m with
  | zero => exact ⟨j, 𝟙 j, fun a => Fin.elim0 a⟩
  | succ m ih =>
    obtain ⟨k₁, f₁, hf₁⟩ := (ι_eq_iff_same_stage F (x 0) (y 0)).mp (h 0)
    obtain ⟨k₂, f₂, hf₂⟩ := ih (fun a => x a.succ) (fun a => y a.succ)
      (fun a => h a.succ)
    obtain ⟨k, g₁, g₂, hg⟩ := IsFiltered.span f₁ f₂
    refine ⟨k, f₁ ≫ g₁, ?_⟩
    intro a
    refine Fin.cases ?_ (fun b => ?_) a
    · rw [F.map_comp]
      exact congrArg (F.map g₁).toFun hf₁
    · rw [hg, F.map_comp]
      exact congrArg (F.map g₂).toFun (hf₂ b)

/-- Two finite lists from different stages are identified by two maps to
one later stage exactly when all their colimit images agree. -/
theorem eventually_eq_fin_different {j k : J} (m : ℕ)
    (x : Fin m → F.obj j) (y : Fin m → F.obj k)
    (h : ∀ a, ι F j (x a) = ι F k (y a)) :
    ∃ (l : J) (f : j ⟶ l) (g : k ⟶ l),
      ∀ a, (F.map f).toFun (x a) = (F.map g).toFun (y a) := by
  let l := IsFiltered.max j k
  let f : j ⟶ l := IsFiltered.leftToMax j k
  let g : k ⟶ l := IsFiltered.rightToMax j k
  obtain ⟨q, u, hu⟩ := eventually_eq_fin F m
    (fun a => (F.map f).toFun (x a)) (fun a => (F.map g).toFun (y a))
    (fun a => (ι_map F f (x a)).trans ((h a).trans (ι_map F g (y a)).symm))
  refine ⟨q, f ≫ u, g ≫ u, ?_⟩
  intro a
  rw [F.map_comp, F.map_comp]
  exact hu a

/-- Any finite list of matching-boundary conditions can be imposed at the
same stage as a finite family of representatives. -/
theorem exists_representatives_with_faces (m r : ℕ) (x : Fin m → Carrier F)
    (left right : Fin r → Fin m) (dim : Fin r → ℕ)
    (h : ∀ a, face F true (dim a) (x (left a)) =
      face F false (dim a) (x (right a))) :
    ∃ (j : J) (v : Fin m → F.obj j), (∀ a, ι F j (v a) = x a) ∧
      ∀ a, (F.obj j).target (dim a) (v (left a)) =
        (F.obj j).source (dim a) (v (right a)) := by
  obtain ⟨j, v, hv⟩ := exists_representatives_fin F m x
  have he (a : Fin r) :
      ι F j ((F.obj j).target (dim a) (v (left a))) =
        ι F j ((F.obj j).source (dim a) (v (right a))) := by
    rw [← face_ι, ← face_ι, hv, hv]
    exact h a
  obtain ⟨k, f, hf⟩ := eventually_eq_fin F r _ _ he
  refine ⟨k, fun a => (F.map f).toFun (v a), ?_, ?_⟩
  · intro a
    exact (ι_map F f (v a)).trans (hv a)
  · intro a
    exact ((F.map f).map_face true (dim a) (v (left a))).symm.trans
      ((hf a).trans ((F.map f).map_face false (dim a) (v (right a))))

end Thomason.Construction.StrictOmegaCategory.FilteredColimit

end

section

/-! # Compositions in the filtered colimit cell set

Matching boundaries are realized in a single stage. Simultaneous eventual
equality proves that the resulting composite is independent of that stage.
-/

namespace Thomason.Construction.StrictOmegaCategory.FilteredColimit

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Category.{0} J] (F : J ⥤ StrictOmegaCategory.{0}) [IsFiltered J]

omit [IsFiltered J] in
theorem map_matching {j k : J} (f : j ⟶ k) (n : ℕ) (x y : F.obj j)
    (h : (F.obj j).target n x = (F.obj j).source n y) :
    (F.obj k).target n ((F.map f).toFun x) =
      (F.obj k).source n ((F.map f).toFun y) :=
  ((F.map f).map_face true n x).symm.trans
    ((congrArg (F.map f).toFun h).trans ((F.map f).map_face false n y))

/-- Composites of two representatives of the same matching pair have the
same image in the ordinary cell colimit. -/
theorem composite_representatives_eq {j k : J} (n : ℕ)
    (x y : F.obj j) (x' y' : F.obj k)
    (h : (F.obj j).target n x = (F.obj j).source n y)
    (h' : (F.obj k).target n x' = (F.obj k).source n y')
    (hx : ι F j x = ι F k x') (hy : ι F j y = ι F k y') :
    ι F j ((F.obj j).comp n x y h) = ι F k ((F.obj k).comp n x' y' h') := by
  obtain ⟨l, f, g, he⟩ := eventually_eq_fin_different F 2
    (Fin.cases x (fun _ => y)) (Fin.cases x' (fun _ => y'))
    (Fin.cases hx (fun _ => hy))
  have hx' : (F.map f).toFun x = (F.map g).toFun x' := he 0
  have hy' : (F.map f).toFun y = (F.map g).toFun y' := he 1
  calc
    _ = ι F l ((F.map f).toFun ((F.obj j).comp n x y h)) := (ι_map F f _).symm
    _ = ι F l ((F.obj l).comp n ((F.map f).toFun x) ((F.map f).toFun y)
        (map_matching F f n x y h)) :=
      congrArg (ι F l) ((F.map f).map_comp n x y h _)
    _ = ι F l ((F.obj l).comp n ((F.map g).toFun x') ((F.map g).toFun y')
        (map_matching F g n x' y' h')) := by simp only [hx', hy']
    _ = ι F l ((F.map g).toFun ((F.obj k).comp n x' y' h')) :=
      congrArg (ι F l) ((F.map g).map_comp n x' y' h' _).symm
    _ = _ := ι_map F g _

structure CompositionRepresentative (n : ℕ) (x y : Carrier F) where
  stage : J
  left : F.obj stage
  right : F.obj stage
  matching : (F.obj stage).target n left = (F.obj stage).source n right
  left_eq : ι F stage left = x
  right_eq : ι F stage right = y

noncomputable def compositionRepresentative (n : ℕ) (x y : Carrier F)
    (h : face F true n x = face F false n y) : CompositionRepresentative F n x y :=
  Classical.choice (by
    obtain ⟨j, a, b, hab, ha, hb⟩ := exists_composable_representatives F n x y h
    exact ⟨⟨j, a, b, hab, ha, hb⟩⟩)

noncomputable def comp (n : ℕ) (x y : Carrier F)
    (h : face F true n x = face F false n y) : Carrier F :=
  let r := compositionRepresentative F n x y h
  ι F r.stage ((F.obj r.stage).comp n r.left r.right r.matching)

/-- The colimit composite agrees with every composable original pair. -/
theorem comp_ι (n : ℕ) (j : J) (x y : F.obj j)
    (h : (F.obj j).target n x = (F.obj j).source n y)
    (h' : face F true n (ι F j x) = face F false n (ι F j y)) :
    comp F n (ι F j x) (ι F j y) h' = ι F j ((F.obj j).comp n x y h) := by
  let r := compositionRepresentative F n (ι F j x) (ι F j y) h'
  exact composite_representatives_eq F n r.left r.right x y r.matching h
    r.left_eq r.right_eq

end Thomason.Construction.StrictOmegaCategory.FilteredColimit

end

section

/-! # Strict laws on the filtered cell colimit

Finite simultaneous representatives reduce every law to its literal
counterpart at one stage of the original strict diagram.
-/

namespace Thomason.Construction.StrictOmegaCategory.FilteredColimit

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Category.{0} J] (F : J ⥤ StrictOmegaCategory.{0}) [IsFiltered J]

theorem source_comp (n : ℕ) (x y : Carrier F)
    (h : face F true n x = face F false n y) :
    face F false n (comp F n x y h) = face F false n x := by
  obtain ⟨j, a, b, hab, rfl, rfl⟩ := exists_composable_representatives F n x y h
  rw [comp_ι F n j a b hab, face_ι, (F.obj j).source_comp, face_ι]

theorem target_comp (n : ℕ) (x y : Carrier F)
    (h : face F true n x = face F false n y) :
    face F true n (comp F n x y h) = face F true n y := by
  obtain ⟨j, a, b, hab, rfl, rfl⟩ := exists_composable_representatives F n x y h
  rw [comp_ι F n j a b hab, face_ι, (F.obj j).target_comp, face_ι]

theorem face_comp (a : Bool) (m n : ℕ) (hnm : n < m) (x y : Carrier F)
    (h : face F true n x = face F false n y)
    (h' : face F true n (face F a m x) = face F false n (face F a m y)) :
    face F a m (comp F n x y h) = comp F n (face F a m x) (face F a m y) h' := by
  obtain ⟨j, x, y, hxy, rfl, rfl⟩ := exists_composable_representatives F n x y h
  have hxy' : (F.obj j).target n ((F.obj j).face a m x) =
      (F.obj j).source n ((F.obj j).face a m y) := by
    simpa only [(F.obj j).globular, ite_eq_left hnm] using hxy
  simp only [comp_ι F n j x y hxy, face_ι,
    comp_ι F n j _ _ hxy', (F.obj j).face_comp a m n hnm x y hxy hxy']

theorem left_unit (n : ℕ) (x : Carrier F)
    (h : face F true n (face F false n x) = face F false n x) :
    comp F n (face F false n x) x h = x := by
  obtain ⟨j, x, rfl⟩ := exists_representative F x
  have hs := (F.obj j).face_face_same true false n x
  simp only [face_ι, comp_ι F n j _ _ hs, (F.obj j).left_unit]

theorem right_unit (n : ℕ) (x : Carrier F)
    (h : face F true n x = face F false n (face F true n x)) :
    comp F n x (face F true n x) h = x := by
  obtain ⟨j, x, rfl⟩ := exists_representative F x
  have hs := ((F.obj j).face_face_same false true n x).symm
  simp only [face_ι, comp_ι F n j _ _ hs, (F.obj j).right_unit]

theorem assoc (n : ℕ) (x y z : Carrier F)
    (hxy : face F true n x = face F false n y)
    (hyz : face F true n y = face F false n z)
    (hl : face F true n (comp F n x y hxy) = face F false n z)
    (hr : face F true n x = face F false n (comp F n y z hyz)) :
    comp F n (comp F n x y hxy) z hl = comp F n x (comp F n y z hyz) hr := by
  obtain ⟨j, v, hv, hm⟩ := exists_representatives_with_faces F 3 2 ![x, y, z]
    ![0, 1] ![1, 2] (fun _ => n) (by intro a; fin_cases a <;> assumption)
  have hx : ι F j (v 0) = x := hv 0
  have hy : ι F j (v 1) = y := hv 1
  have hz : ι F j (v 2) = z := hv 2
  subst x y z
  have hab : (F.obj j).target n (v 0) = (F.obj j).source n (v 1) := hm 0
  have hbc : (F.obj j).target n (v 1) = (F.obj j).source n (v 2) := hm 1
  have hl' : (F.obj j).target n ((F.obj j).comp n (v 0) (v 1) hab) =
      (F.obj j).source n (v 2) := ((F.obj j).target_comp _ _ _ _).trans hbc
  have hr' : (F.obj j).target n (v 0) =
      (F.obj j).source n ((F.obj j).comp n (v 1) (v 2) hbc) :=
    hab.trans ((F.obj j).source_comp _ _ _ _).symm
  simp only [comp_ι F n j _ _ hab, comp_ι F n j _ _ hbc,
    comp_ι F n j _ _ hl', comp_ι F n j _ _ hr']
  exact congrArg (ι F j) ((F.obj j).assoc n _ _ _ hab hbc hl' hr')

/-- Below a composite's composition level, either boundary agrees with
the corresponding boundary of its first factor. -/
theorem lower_face_comp (C : StrictOmegaCategory.{0}) (a : Bool) (m n : ℕ)
    (hmn : m < n) (x y : C) (h : C.target n x = C.source n y) :
    C.face a m (C.comp n x y h) = C.face a m x := by
  have he := C.globular a false m n (C.comp n x y h)
  rw [ite_eq_left hmn, C.source_comp, C.globular, ite_eq_left hmn] at he
  exact he.symm

theorem interchange (m n : ℕ) (hmn : m < n) (a b c d : Carrier F)
    (hab : face F true m a = face F false m b)
    (hcd : face F true m c = face F false m d)
    (hac : face F true n a = face F false n c)
    (hbd : face F true n b = face F false n d)
    (hl : face F true n (comp F m a b hab) = face F false n (comp F m c d hcd))
    (hr : face F true m (comp F n a c hac) = face F false m (comp F n b d hbd)) :
    comp F n (comp F m a b hab) (comp F m c d hcd) hl =
      comp F m (comp F n a c hac) (comp F n b d hbd) hr := by
  obtain ⟨j, v, hv, hm⟩ := exists_representatives_with_faces F 4 4 ![a, b, c, d]
    ![0, 2, 0, 1] ![1, 3, 2, 3] ![m, m, n, n]
    (by intro k; fin_cases k <;> assumption)
  have ha : ι F j (v 0) = a := hv 0
  have hb : ι F j (v 1) = b := hv 1
  have hc : ι F j (v 2) = c := hv 2
  have hd : ι F j (v 3) = d := hv 3
  subst a b c d
  have hab' : (F.obj j).target m (v 0) = (F.obj j).source m (v 1) := hm 0
  have hcd' : (F.obj j).target m (v 2) = (F.obj j).source m (v 3) := hm 1
  have hac' : (F.obj j).target n (v 0) = (F.obj j).source n (v 2) := hm 2
  have hbd' : (F.obj j).target n (v 1) = (F.obj j).source n (v 3) := hm 3
  have ht : (F.obj j).target m ((F.obj j).target n (v 0)) =
      (F.obj j).source m ((F.obj j).target n (v 1)) := by
    simpa only [(F.obj j).globular, ite_eq_left hmn] using hab'
  have hs : (F.obj j).target m ((F.obj j).source n (v 2)) =
      (F.obj j).source m ((F.obj j).source n (v 3)) := by
    simpa only [(F.obj j).globular, ite_eq_left hmn] using hcd'
  have hl' : (F.obj j).target n ((F.obj j).comp m (v 0) (v 1) hab') =
      (F.obj j).source n ((F.obj j).comp m (v 2) (v 3) hcd') := by
    change (F.obj j).face true n ((F.obj j).comp m (v 0) (v 1) hab') =
      (F.obj j).face false n ((F.obj j).comp m (v 2) (v 3) hcd')
    rw [(F.obj j).face_comp true n m hmn _ _ hab' ht,
      (F.obj j).face_comp false n m hmn _ _ hcd' hs]
    simp only [hac', hbd']
  have hr' : (F.obj j).target m ((F.obj j).comp n (v 0) (v 2) hac') =
      (F.obj j).source m ((F.obj j).comp n (v 1) (v 3) hbd') := by
    change (F.obj j).face true m ((F.obj j).comp n (v 0) (v 2) hac') =
      (F.obj j).face false m ((F.obj j).comp n (v 1) (v 3) hbd')
    rw [lower_face_comp (F.obj j) true m n hmn,
      lower_face_comp (F.obj j) false m n hmn]
    exact hab'
  simp only [comp_ι F m j _ _ hab', comp_ι F m j _ _ hcd',
    comp_ι F n j _ _ hac', comp_ι F n j _ _ hbd',
    comp_ι F n j _ _ hl', comp_ι F m j _ _ hr']
  exact congrArg (ι F j) ((F.obj j).interchange m n hmn _ _ _ _
    hab' hcd' hac' hbd' hl' hr')

/-- The ordinary filtered cell colimit, equipped with its constructed
strict operations and all the original strict laws. -/
noncomputable def category : StrictOmegaCategory.{0} where
  Cell := Carrier F
  face := face F
  globular := globular F
  comp := comp F
  source_comp := source_comp F
  target_comp := target_comp F
  face_comp := face_comp F
  left_unit := left_unit F
  right_unit := right_unit F
  assoc := assoc F
  interchange := interchange F
  finite_dimension := finite_dimension F

end Thomason.Construction.StrictOmegaCategory.FilteredColimit

end

section

/-! # The filtered cell construction is a strict colimit

Its universal map is the ordinary colimit map of the underlying cell sets.
Thus the constructed colimit preserves the original representatives and
proves filtered-colimit preservation of the cell functor.
-/

namespace Thomason.Construction.StrictOmegaCategory.FilteredColimit

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory

variable {J : Type} [Category.{0} J] (F : J ⥤ StrictOmegaCategory.{0}) [IsFiltered J]

noncomputable def leg (j : J) : F.obj j ⟶ category F where
  toFun := ι F j
  map_face a n x := (face_ι F a n j x).symm
  map_comp n x y h h' := (comp_ι F n j x y h h').symm

noncomputable def cocone : Cocone F where
  pt := category F
  ι := {
    app := leg F
    naturality j k f := by
      apply Hom.ext
      funext x
      exact ι_map F f x }

noncomputable def descFunction (s : Cocone F) : Carrier F → s.pt :=
  colimit.desc (cellDiagram F) (cells.mapCocone s)

omit [IsFiltered J] in
@[simp] theorem descFunction_ι (s : Cocone F) (j : J) (x : F.obj j) :
    descFunction F s (ι F j x) = (s.ι.app j).toFun x :=
  congr_hom (colimit.ι_desc (cells.mapCocone s) j) x

noncomputable def desc (s : Cocone F) : category F ⟶ s.pt where
  toFun := descFunction F s
  map_face a n x := by
    obtain ⟨j, x, rfl⟩ := exists_representative F x
    change descFunction F s (face F a n (ι F j x)) =
      s.pt.face a n (descFunction F s (ι F j x))
    rw [face_ι, descFunction_ι, descFunction_ι]
    exact (s.ι.app j).map_face a n x
  map_comp n x y h h' := by
    obtain ⟨j, x, y, hxy, rfl, rfl⟩ := exists_composable_representatives F n x y h
    change descFunction F s (comp F n (ι F j x) (ι F j y) h) =
      s.pt.comp n (descFunction F s (ι F j x)) (descFunction F s (ι F j y)) h'
    refine (congrArg (descFunction F s) (comp_ι F n j x y hxy h)).trans ?_
    simp only [descFunction_ι]
    exact (s.ι.app j).map_comp n x y hxy _

noncomputable def isColimit : IsColimit (cocone F) where
  desc := desc F
  fac s j := by
    apply Hom.ext
    funext x
    exact descFunction_ι F s j x
  uniq s m hm := by
    apply Hom.ext
    funext x
    obtain ⟨j, x, rfl⟩ := exists_representative F x
    exact (congrArg (fun f : F.obj j ⟶ s.pt => f.toFun x) (hm j)).trans
      (descFunction_ι F s j x).symm

/-- Forgetting to cells preserves the constructed filtered colimit exactly. -/
noncomputable def cellsIsColimit : IsColimit (cells.mapCocone (cocone F)) :=
  colimit.isColimit (cellDiagram F)

/-- The actual underlying-cell functor preserves every small filtered colimit. -/
instance cells_preservesFilteredColimitsOfShape : PreservesColimitsOfShape J cells where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone
    (isColimit F) (cellsIsColimit F)

/-- Every cell of any strict colimit of the filtered diagram comes from a stage. -/
theorem cocone_cell_representative {s : Cocone F} (hs : IsColimit s) (x : s.pt) :
    ∃ (j : J) (y : F.obj j), (s.ι.app j).toFun y = x :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves cells hs) x

/-- Equality in any strict filtered colimit is exactly eventual stage equality. -/
theorem cocone_cell_eq_iff {s : Cocone F} (hs : IsColimit s)
    {i j : J} (x : F.obj i) (y : F.obj j) :
    (s.ι.app i).toFun x = (s.ι.app j).toFun y ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
        (F.map f).toFun x = (F.map g).toFun y :=
  Types.FilteredColimit.isColimit_eq_iff (cellDiagram F)
    (isColimitOfPreserves cells hs)

/-- A dimension bound on the image of an original cell holds at some later stage. -/
theorem cocone_eventually_dimensionLE {s : Cocone F} (hs : IsColimit s)
    {j : J} (n : ℕ) (x : F.obj j) (hx : s.pt.DimensionLE n ((s.ι.app j).toFun x)) :
    ∃ (k : J) (f : j ⟶ k), (F.obj k).DimensionLE n ((F.map f).toFun x) := by
  have he₀ : (s.ι.app j).toFun ((F.obj j).source n x) = (s.ι.app j).toFun x :=
    ((s.ι.app j).map_face false n x).trans hx.1
  have he₁ : (s.ι.app j).toFun ((F.obj j).target n x) = (s.ι.app j).toFun x :=
    ((s.ι.app j).map_face true n x).trans hx.2
  obtain ⟨k₀, f₀, hf₀⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves cells hs) _ _).mp he₀
  obtain ⟨k₁, f₁, hf₁⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves cells hs) _ _).mp he₁
  obtain ⟨k, g₀, g₁, hg⟩ := IsFiltered.span f₀ f₁
  have h₀ : (F.map (f₀ ≫ g₀)).toFun ((F.obj j).source n x) =
      (F.map (f₀ ≫ g₀)).toFun x := by
    rw [F.map_comp]
    exact congrArg (F.map g₀).toFun hf₀
  have h₁ : (F.map (f₀ ≫ g₀)).toFun ((F.obj j).target n x) =
      (F.map (f₀ ≫ g₀)).toFun x := by
    rw [hg, F.map_comp]
    exact congrArg (F.map g₁).toFun hf₁
  refine ⟨k, f₀ ≫ g₀, ?_, ?_⟩
  · exact ((F.map (f₀ ≫ g₀)).map_face false n x).symm.trans h₀
  · exact ((F.map (f₀ ≫ g₀)).map_face true n x).symm.trans h₁

/-- Bounded cells in a filtered colimit have bounded original representatives. -/
theorem cocone_bounded_representative {s : Cocone F} (hs : IsColimit s)
    (n : ℕ) (x : s.pt) (hx : s.pt.DimensionLE n x) :
    ∃ (j : J) (y : F.obj j), (F.obj j).DimensionLE n y ∧ (s.ι.app j).toFun y = x := by
  obtain ⟨j, y, rfl⟩ := cocone_cell_representative F hs x
  obtain ⟨k, f, hf⟩ := cocone_eventually_dimensionLE F hs n y hx
  refine ⟨k, (F.map f).toFun y, hf, ?_⟩
  exact congrArg (fun g : F.obj j ⟶ s.pt => g.toFun y) (s.w f)

end Thomason.Construction.StrictOmegaCategory.FilteredColimit

end

section

/-! # Bounded-cell functors preserve filtered colimits -/

namespace Thomason.Construction.StrictOmegaCategory.FilteredColimit

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory

/-- The cells fixed by both n-dimensional boundary maps. -/
def boundedCells (n : ℕ) : StrictOmegaCategory.{0} ⥤ Type where
  obj C := {x : C // C.DimensionLE n x}
  map f := ↾fun x => ⟨f.toFun x.val, f.dimensionLE x.property⟩

variable {J : Type} [Category.{0} J] [IsFiltered J]
    {F : J ⥤ StrictOmegaCategory.{0}} {s : Cocone F}

/-- A filtered strict colimit is a colimit on each bounded-cell set. -/
noncomputable def boundedCellsIsColimit (n : ℕ) (hs : IsColimit s) :
    IsColimit ((boundedCells n).mapCocone s) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨j, y, hy, hxy⟩ := cocone_bounded_representative F hs n x.val x.property
    exact ⟨j, ⟨y, hy⟩, (Subtype.ext hxy).symm⟩
  · intro j x y hxy
    have he : (s.ι.app j).toFun x.val = (s.ι.app j).toFun y.val :=
      congrArg Subtype.val hxy
    obtain ⟨k, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves cells hs) x.val y.val).mp he
    exact ⟨k, f, Subtype.ext hf⟩

instance boundedCells_preservesFilteredColimitsOfShape (n : ℕ) :
    PreservesColimitsOfShape J (boundedCells n) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone
    (isColimit F) (boundedCellsIsColimit n (isColimit F))

/-- The free globe represents this bounded-cell functor, naturally. -/
def globeCoyonedaIso (n : ℕ) :
    coyoneda.obj (Opposite.op (Globe.category n)) ≅ boundedCells n :=
  NatIso.ofComponents (fun C => (Globe.homEquiv C n).toIso) (by
    intro C D f
    ext g
    apply Subtype.ext
    rfl)

/-- Mapping out of a globe commutes with every small filtered colimit. -/
instance globeCoyoneda_preservesFilteredColimitsOfShape (n : ℕ) :
    PreservesColimitsOfShape J (coyoneda.obj (Opposite.op (Globe.category n))) :=
  preservesColimitsOfShape_of_natIso (globeCoyonedaIso n).symm

end Thomason.Construction.StrictOmegaCategory.FilteredColimit

end

section

/-! # Strict isomorphisms from bijections of actual cells -/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

/-- A cellwise bijective strict functor has a strict inverse. -/
noncomputable def isoOfBijective {C D : StrictOmegaCategory.{0}} (f : C ⟶ D)
    (hf : Function.Bijective f.toFun) : C ≅ D := by
  let e : C ≃ D := Equiv.ofBijective f.toFun hf
  have hfg (y : D) : f.toFun (e.symm y) = y := e.apply_symm_apply y
  let g : D ⟶ C :=
    { toFun := e.symm
      map_face := by
        intro a n y
        apply hf.1
        exact (hfg (D.face a n y)).trans
          ((congrArg (D.face a n) (hfg y).symm).trans (f.map_face a n (e.symm y)).symm)
      map_comp := by
        intro n x y hxy h'
        apply hf.1
        have hD : D.target n (f.toFun (e.symm x)) = D.source n (f.toFun (e.symm y)) := by
          rw [hfg, hfg]
          exact hxy
        have ht : f.toFun (C.comp n (e.symm x) (e.symm y) h') = D.comp n x y hxy := by
          simpa only [hfg] using f.map_comp n (e.symm x) (e.symm y) h' hD
        exact (hfg (D.comp n x y hxy)).trans ht.symm }
  exact
    { hom := f
      inv := g
      hom_inv_id := by
        apply Hom.ext
        funext x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply Hom.ext
        funext y
        exact hfg y }

end Thomason.Construction.StrictOmegaCategory

end

end OAI
