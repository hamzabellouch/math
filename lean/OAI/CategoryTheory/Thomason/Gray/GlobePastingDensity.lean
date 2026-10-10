import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeFaces
import OAI.CategoryTheory.Thomason.Gray.StrictAbelianization
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Data.Fintype.EquivFin

namespace OAI

section

/-! # Finite-dimensional cells in the globe mapping family

For a functor on strict categories, maps from the images of the globes
form a reflexive globular family. Identity extensions are injective, and
their filtered union has actual finite-dimensional cells and globular
faces. This is the underlying cell construction for the right interval
internal hom; composition is constructed separately from cylinder gluing.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory

namespace Globe

/-- Extend the universal n-cell to an m-dimensional identity cell. -/
def lower (m n : ℕ) (h : n ≤ m) : category m ⟶ category n :=
  lift (category n) Cell.top ((category n).dimensionLE_mono h (category_truncated n Cell.top))

@[simp] theorem lower_top (m n : ℕ) (h : n ≤ m) :
    (lower m n h).toFun Cell.top = Cell.top := rfl

@[simp] theorem lower_self (n : ℕ) (h : n ≤ n) : lower n n h = 𝟙 (category n) := by
  apply hom_ext
  rfl

theorem lower_comp {l m n : ℕ} (hml : m ≤ l) (hnm : n ≤ m) :
    lower l m hml ≫ lower m n hnm = lower l n (hnm.trans hml) := by
  apply hom_ext
  rfl

theorem faceMap_lower (a : Bool) (r : ℕ) {m n : ℕ} (h : n ≤ m) :
    faceMap a r m ≫ lower m n h = faceMap a r n := by
  apply hom_ext
  exact (lower m n h).map_face a r Cell.top

theorem faceMap_eq_lower (a : Bool) {m n : ℕ} (h : n ≤ m) :
    faceMap a m n = lower m n h := by
  apply hom_ext
  cases a
  · exact ((category n).dimensionLE_mono h (category_truncated n Cell.top)).1
  · exact ((category n).dimensionLE_mono h (category_truncated n Cell.top)).2

theorem faceMap_lower_retraction (a : Bool) {m n : ℕ} (h : n ≤ m) :
    faceMap a n m ≫ lower m n h = 𝟙 (category n) := by
  rw [faceMap_lower, faceMap_self]

end Globe

namespace GlobeMappingCells

noncomputable section

variable (F : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0})
  (D : StrictOmegaCategory.{0})

/-- The identity-extension diagram of maps from the actual globe images. -/
def diagram : ℕ ⥤ Type where
  obj n := F.obj (Globe.category n) ⟶ D
  map {n m} h := ↾fun f => F.map (Globe.lower m n (leOfHom h)) ≫ f
  map_id n := by
    ext f
    change F.map (Globe.lower n n _) ≫ f = f
    rw [Globe.lower_self, F.map_id, Category.id_comp]
  map_comp {l m n} h j := by
    ext f
    change F.map (Globe.lower n l _) ≫ f =
      F.map (Globe.lower n m _) ≫ (F.map (Globe.lower m l _) ≫ f)
    rw [← Category.assoc, ← F.map_comp, Globe.lower_comp]

abbrev Carrier : Type := colimit (diagram F D)

def ι (n : ℕ) (f : F.obj (Globe.category n) ⟶ D) : Carrier F D :=
  colimit.ι (diagram F D) n f

theorem ι_lower {n m : ℕ} (h : n ≤ m) (f : F.obj (Globe.category n) ⟶ D) :
    ι F D m (F.map (Globe.lower m n h) ≫ f) = ι F D n f :=
  congr_hom (colimit.w (diagram F D) (homOfLE h)) f

theorem exists_representative (x : Carrier F D) :
    ∃ (n : ℕ) (f : F.obj (Globe.category n) ⟶ D), ι F D n f = x :=
  Types.jointly_surjective' x

/-- Every finite-level mapping set embeds into the identity-extension union. -/
theorem ι_injective (n : ℕ) : Function.Injective (ι F D n) := by
  intro f g hfg
  obtain ⟨m, j, hj⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (colimit.isColimit (diagram F D)) f g).mp hfg
  have h : F.map (Globe.lower m n (leOfHom j)) ≫ f =
      F.map (Globe.lower m n (leOfHom j)) ≫ g := hj
  have hh := congrArg (fun q => F.map (Globe.faceMap false n m) ≫ q) h
  simpa only [← Category.assoc, ← F.map_comp, Globe.faceMap_lower_retraction,
    F.map_id, Category.id_comp] using hh

def faceCocone (a : Bool) (r : ℕ) : Cocone (diagram F D) where
  pt := Carrier F D
  ι := {
    app n := ↾fun f => ι F D r (F.map (Globe.faceMap a r n) ≫ f)
    naturality n m j := by
      ext f
      change F.obj (Globe.category n) ⟶ D at f
      change ι F D r (F.map (Globe.faceMap a r m) ≫
        (F.map (Globe.lower m n (leOfHom j)) ≫ f)) =
          ι F D r (F.map (Globe.faceMap a r n) ≫ f)
      rw [← Category.assoc, ← F.map_comp, Globe.faceMap_lower] }

def face (a : Bool) (r : ℕ) : Carrier F D → Carrier F D :=
  colimit.desc (diagram F D) (faceCocone F D a r)

@[simp] theorem face_ι (a : Bool) (r n : ℕ) (f : F.obj (Globe.category n) ⟶ D) :
    face F D a r (ι F D n f) = ι F D r (F.map (Globe.faceMap a r n) ≫ f) :=
  congr_hom (colimit.ι_desc (faceCocone F D a r) n) f

theorem face_ι_of_le (a : Bool) {r n : ℕ} (hnr : n ≤ r)
    (f : F.obj (Globe.category n) ⟶ D) : face F D a r (ι F D n f) = ι F D n f := by
  rw [face_ι, Globe.faceMap_eq_lower a hnr]
  exact ι_lower F D hnr f

/-- The globular law holds before any composition operation is imposed. -/
theorem globular (a b : Bool) (r s : ℕ) (x : Carrier F D) :
    face F D a r (face F D b s x) =
      if r < s then face F D a r x else face F D b s x := by
  obtain ⟨n, f, rfl⟩ := exists_representative F D x
  by_cases hrs : r < s
  · simp only [hrs, ite_true, face_ι, ← Category.assoc, ← F.map_comp,
      Globe.faceMap_comp a b r s n hrs]
  · rw [ite_eq_right hrs, face_ι, face_ι_of_le F D a (Nat.le_of_not_gt hrs)]

/-- Every mapping-family cell has a finite dimension bound. -/
theorem finite_dimension (x : Carrier F D) :
    ∃ n, face F D false n x = x ∧ face F D true n x = x := by
  obtain ⟨n, f, rfl⟩ := exists_representative F D x
  exact ⟨n, face_ι_of_le F D false le_rfl f, face_ι_of_le F D true le_rfl f⟩

/-- Equality of r-faces is the literal equality of the restricted globe maps. -/
theorem faces_eq_iff (a b : Bool) (r n m : ℕ)
    (f : F.obj (Globe.category n) ⟶ D) (g : F.obj (Globe.category m) ⟶ D) :
    face F D a r (ι F D n f) = face F D b r (ι F D m g) ↔
      F.map (Globe.faceMap a r n) ≫ f = F.map (Globe.faceMap b r m) ≫ g := by
  rw [face_ι, face_ι]
  exact (ι_injective F D r).eq_iff

/-- The literal finite-dimensional condition on the mapping-family carrier. -/
def Bounded (n : ℕ) (x : Carrier F D) : Prop :=
  face F D false n x = x ∧ face F D true n x = x

theorem bounded_ι (n : ℕ) (f : F.obj (Globe.category n) ⟶ D) :
    Bounded F D n (ι F D n f) :=
  ⟨face_ι_of_le F D false le_rfl f, face_ι_of_le F D true le_rfl f⟩

/-- A bounded cell is represented at its exact bound, not just a larger stage. -/
theorem bounded_iff_representative (n : ℕ) (x : Carrier F D) :
    Bounded F D n x ↔ ∃ f : F.obj (Globe.category n) ⟶ D, ι F D n f = x := by
  constructor
  · intro hx
    obtain ⟨m, f, rfl⟩ := exists_representative F D x
    exact ⟨F.map (Globe.faceMap false n m) ≫ f, (face_ι F D false n m f).symm.trans hx.1⟩
  · rintro ⟨f, rfl⟩
    exact bounded_ι F D n f

/-- Evaluation on an n-globe exactly represents the bounded mapping cells. -/
def boundedEquiv (n : ℕ) :
    (F.obj (Globe.category n) ⟶ D) ≃ {x : Carrier F D // Bounded F D n x} where
  toFun f := ⟨ι F D n f, bounded_ι F D n f⟩
  invFun x := Classical.choose ((bounded_iff_representative F D n x.val).mp x.property)
  left_inv f := (ι_injective F D n)
    (Classical.choose_spec ((bounded_iff_representative F D n (ι F D n f)).mp
      (bounded_ι F D n f)))
  right_inv x := Subtype.ext
    (Classical.choose_spec ((bounded_iff_representative F D n x.val).mp x.property))

variable {D} {E : StrictOmegaCategory.{0}}

def mapCocone (u : D ⟶ E) : Cocone (diagram F D) where
  pt := Carrier F E
  ι := {
    app n := ↾fun f => ι F E n (f ≫ u)
    naturality n m j := by
      ext f
      change F.obj (Globe.category n) ⟶ D at f
      change ι F E m ((F.map (Globe.lower m n (leOfHom j)) ≫ f) ≫ u) =
        ι F E n (f ≫ u)
      rw [Category.assoc, ι_lower] }

/-- Postcompose every finite globe map by an actual strict functor. -/
def map (u : D ⟶ E) : Carrier F D → Carrier F E :=
  colimit.desc (diagram F D) (mapCocone F u)

@[simp] theorem map_ι (u : D ⟶ E) (n : ℕ) (f : F.obj (Globe.category n) ⟶ D) :
    map F u (ι F D n f) = ι F E n (f ≫ u) :=
  congr_hom (colimit.ι_desc (mapCocone F u) n) f

theorem map_face (u : D ⟶ E) (a : Bool) (n : ℕ) (x : Carrier F D) :
    map F u (face F D a n x) = face F E a n (map F u x) := by
  obtain ⟨m, f, rfl⟩ := exists_representative F D x
  simp only [face_ι, map_ι, Category.assoc]

theorem map_id (x : Carrier F D) : map F (𝟙 D) x = x := by
  obtain ⟨n, f, rfl⟩ := exists_representative F D x
  simp only [map_ι, Category.comp_id]

theorem map_comp {E' : StrictOmegaCategory.{0}} (u : D ⟶ E) (v : E ⟶ E')
    (x : Carrier F D) : map F (u ≫ v) x = map F v (map F u x) := by
  obtain ⟨n, f, rfl⟩ := exists_representative F D x
  simp only [map_ι, Category.assoc]

end
end GlobeMappingCells
end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Common finite bounds for actual globe-mapping cells -/

namespace Thomason.Construction.StrictOmegaCategory.GlobeMappingCells

open CategoryTheory

noncomputable section

variable (F : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0})
  (D : StrictOmegaCategory.{0})

theorem exists_representative_above (x : Carrier F D) (N : ℕ) :
    ∃ (n : ℕ), N ≤ n ∧ ∃ f : F.obj (Globe.category n) ⟶ D, ι F D n f = x := by
  obtain ⟨m, f, hf⟩ := exists_representative F D x
  refine ⟨max N m, Nat.le_max_left _ _, F.map (Globe.lower (max N m) m
    (Nat.le_max_right _ _)) ≫ f, ?_⟩
  exact (ι_lower F D (Nat.le_max_right N m) f).trans hf

/-- A pair of cells has representatives at one bound above any prescribed level. -/
theorem exists_representatives₂_above (x y : Carrier F D) (N : ℕ) :
    ∃ (n : ℕ), N ≤ n ∧ ∃ f g : F.obj (Globe.category n) ⟶ D,
      ι F D n f = x ∧ ι F D n g = y := by
  obtain ⟨l, hl, f, hf⟩ := exists_representative_above F D x N
  obtain ⟨m, hm, g, hg⟩ := exists_representative_above F D y N
  refine ⟨max l m, hl.trans (Nat.le_max_left _ _),
    F.map (Globe.lower (max l m) l (Nat.le_max_left _ _)) ≫ f,
    F.map (Globe.lower (max l m) m (Nat.le_max_right _ _)) ≫ g,
    (ι_lower F D (Nat.le_max_left l m) f).trans hf,
    (ι_lower F D (Nat.le_max_right l m) g).trans hg⟩

/-- Matching faces remain a literal equation at every common representative level. -/
theorem matching_representatives {n k : ℕ} (x y : Carrier F D)
    (h : face F D true k x = face F D false k y)
    (f g : F.obj (Globe.category n) ⟶ D)
    (hf : ι F D n f = x) (hg : ι F D n g = y) :
    F.map (Globe.faceMap true k n) ≫ f = F.map (Globe.faceMap false k n) ≫ g := by
  apply (faces_eq_iff F D true false k n n f g).mp
  exact (congrArg (face F D true k) hf).trans
    (h.trans (congrArg (face F D false k) hg).symm)

end
end Thomason.Construction.StrictOmegaCategory.GlobeMappingCells

end

section

/-! # A common finite bound for finite families of mapping cells -/

namespace Thomason.Construction.StrictOmegaCategory.GlobeMappingCells

open CategoryTheory

noncomputable section

variable (F : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0}) (D : StrictOmegaCategory.{0})

/-- Choose simultaneous finite representatives, retaining any required
lower bound. This supplies the three and four cells used in the strict laws. -/
theorem exists_representatives_fin_above (m : ℕ) (x : Fin m → Carrier F D) (N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ f : Fin m → (F.obj (Globe.category n) ⟶ D),
      ∀ i, ι F D n (f i) = x i := by
  induction m generalizing N with
  | zero =>
      exact ⟨N, le_rfl, Fin.elim0, fun i => Fin.elim0 i⟩
  | succ m ih =>
      obtain ⟨n, hn, f, hf⟩ := ih (fun i => x i.succ) N
      obtain ⟨r, hr, g, hg⟩ := exists_representative_above F D (x 0) n
      refine ⟨r, hn.trans hr, Fin.cases g (fun i => F.map (Globe.lower r n hr) ≫ f i), ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hg
      · exact (ι_lower F D hr (f j)).trans (hf j)

/-- Reindex the common bound by a finite parameter set, such as the four
positions in an interchange square. -/
theorem exists_representatives_finite_above {I : Type} [Finite I]
    (x : I → Carrier F D) (N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ f : I → (F.obj (Globe.category n) ⟶ D),
      ∀ i, ι F D n (f i) = x i := by
  let _ := Fintype.ofFinite I
  let e := Fintype.equivFin I
  obtain ⟨n, hn, f, hf⟩ := exists_representatives_fin_above F D (Fintype.card I)
    (fun j => x (e.symm j)) N
  refine ⟨n, hn, fun i => f (e i), fun i => ?_⟩
  simpa only [Equiv.symm_apply_apply] using hf (e i)

end
end Thomason.Construction.StrictOmegaCategory.GlobeMappingCells

end

section

/-! # Evaluation induced by a natural map into the globe model

In particular the two actual interval endpoints evaluate mapping cells
in their target. The definition respects finite representatives and all
faces before an internal-hom category has been assembled.
-/

namespace Thomason.Construction.StrictOmegaCategory.GlobeMappingCells

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory

noncomputable section

variable {F : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0}}
    (η : 𝟭 StrictOmegaCategory.{0} ⟶ F) (D : StrictOmegaCategory.{0})

def evaluationCocone : Cocone (diagram F D) where
  pt := D
  ι := {
    app n := ↾fun f => f.toFun ((η.app (Globe.category n)).toFun Globe.Cell.top)
    naturality n m j := by
      ext f
      change F.obj (Globe.category n) ⟶ D at f
      change f.toFun ((F.map (Globe.lower m n (leOfHom j))).toFun
        ((η.app (Globe.category m)).toFun Globe.Cell.top)) =
          f.toFun ((η.app (Globe.category n)).toFun Globe.Cell.top)
      exact congrArg f.toFun
        (congrArg (fun q : Globe.category m ⟶ F.obj (Globe.category n) =>
          q.toFun Globe.Cell.top) (η.naturality (Globe.lower m n (leOfHom j)))).symm }

def naturalEvaluation : Carrier F D → D := colimit.desc (diagram F D) (evaluationCocone η D)

@[simp] theorem naturalEvaluation_ι (n : ℕ) (f : F.obj (Globe.category n) ⟶ D) :
    naturalEvaluation η D (ι F D n f) = f.toFun ((η.app (Globe.category n)).toFun Globe.Cell.top) :=
  congr_hom (colimit.ι_desc (evaluationCocone η D) n) f

theorem naturalEvaluation_face (a : Bool) (r : ℕ) (x : Carrier F D) :
    naturalEvaluation η D (face F D a r x) = D.face a r (naturalEvaluation η D x) := by
  obtain ⟨n, f, rfl⟩ := exists_representative F D x
  rw [face_ι, naturalEvaluation_ι, naturalEvaluation_ι]
  have he := congrArg (fun q : Globe.category r ⟶ F.obj (Globe.category n) =>
    q.toFun Globe.Cell.top) (η.naturality (Globe.faceMap a r n))
  change f.toFun ((F.map (Globe.faceMap a r n)).toFun
      ((η.app (Globe.category r)).toFun Globe.Cell.top)) = _
  exact (congrArg f.toFun he.symm).trans
    ((congrArg f.toFun ((η.app (Globe.category n)).map_face a r Globe.Cell.top)).trans
      (f.map_face a r ((η.app (Globe.category n)).toFun Globe.Cell.top)))

variable {D} {E : StrictOmegaCategory.{0}}

theorem naturalEvaluation_map (u : D ⟶ E) (x : Carrier F D) :
    naturalEvaluation η E (map F u x) = u.toFun (naturalEvaluation η D x) := by
  obtain ⟨n, f, rfl⟩ := exists_representative F D x
  rw [map_ι, naturalEvaluation_ι, naturalEvaluation_ι]
  rfl

end
end Thomason.Construction.StrictOmegaCategory.GlobeMappingCells

end

section

/-! # Naturality for every strict map between free globes

The finite mapping representatives agree with evaluation on all globe
cells, including identities in arbitrarily larger dimensions. This is
the globe-level representability bridge used by the right adjunction.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

namespace Globe

theorem hom_top_dimension_le {n m : ℕ} (s : category n ⟶ category m) :
    dimension (s.toFun Cell.top) ≤ n := by
  have h : face false n (s.toFun Cell.top) = s.toFun Cell.top :=
    (s.dimensionLE (category_truncated n Cell.top)).1
  have hd := congrArg dimension h
  have hh : min n (dimension (s.toFun Cell.top)) = dimension (s.toFun Cell.top) :=
    (dimension_face false n (s.toFun Cell.top)).symm.trans hd
  omega

end Globe

namespace GlobeMappingCells

noncomputable section

variable (F : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0}) (D : StrictOmegaCategory.{0})

/-- Evaluate a bounded mapping representative on a cell of its source globe. -/
def evaluateCell {m : ℕ} (f : F.obj (Globe.category m) ⟶ D) : Globe.Cell m → Carrier F D
  | .top => ι F D m f
  | .boundary a r => face F D a r (ι F D m f)

/-- Naturality includes every strict globe map, not only the chosen face maps. -/
theorem globe_naturality {n m : ℕ} (s : Globe.category n ⟶ Globe.category m)
    (f : F.obj (Globe.category m) ⟶ D) :
    ι F D n (F.map s ≫ f) = evaluateCell F D f (s.toFun Globe.Cell.top) := by
  have hd := Globe.hom_top_dimension_le s
  cases ht : s.toFun Globe.Cell.top with
  | top =>
      have hmn : m ≤ n := by simpa only [ht, Globe.dimension] using hd
      have hs : s = Globe.lower n m hmn := by
        apply Globe.hom_ext
        exact ht
      rw [hs, ι_lower]
      rfl
  | boundary a r =>
      have hrn : (r : ℕ) ≤ n := by simpa only [ht, Globe.dimension] using hd
      have hs : s = Globe.lower n r hrn ≫ Globe.faceMap a r m := by
        apply Globe.hom_ext
        change s.toFun Globe.Cell.top = (Globe.category m).face a r Globe.Cell.top
        rw [ht]
        change Globe.Cell.boundary a r = @Globe.face m a r Globe.Cell.top
        unfold Globe.face
        split_ifs with h
        · simp only [Globe.dimension] at h
          omega
        · rfl
      rw [hs, F.map_comp, Category.assoc, ι_lower]
      change ι F D r (F.map (Globe.faceMap a r m) ≫ f) =
        face F D a r (ι F D m f)
      exact (face_ι F D a r m f).symm

end
end GlobeMappingCells
end Thomason.Construction.StrictOmegaCategory

end

section

/-! # The globe comparison and actual Street weak equivalences

The identified positive globe gives isomorphisms of the actual Street
nerves, hence homeomorphisms of their geometric realizations. Changing
between free-globe and positive-chain presentations preserves and reflects
the prescribed weak equivalences, including all strict face maps.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open CategoryTheory

noncomputable section

variable (h : NormalizedSimplexIdentities)

def globeNerveIso (n : ℕ) :
    h.streetNerve.obj (StrictOmegaCategory.Globe.category n) ≅
      h.streetNerve.obj (complex n).realization :=
  h.streetNerve.mapIso (globeIso n)

def globeRealizationHomeomorph (n : ℕ) :
    SSet.toTop.obj (h.streetNerve.obj (StrictOmegaCategory.Globe.category n)) ≃ₜ
      SSet.toTop.obj (h.streetNerve.obj (complex n).realization) :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (globeNerveIso h n))

/-- The canonical comparison satisfies actual component and homotopy-group
weak equivalence, with no Kan--Quillen or Gray hypothesis. -/
theorem fromGlobe_weak (n : ℕ) : h.streetWeakEquivalences (fromGlobe n) := by
  let : IsIso (fromGlobe n) := by
    change IsIso (globeIso n).hom
    infer_instance
  change realizationWeakEquivalences (h.streetNerve.map (fromGlobe n))
  exact MorphismProperty.of_isIso realizationWeakEquivalences _

/-- Conjugating a map by the globe identifications preserves and reflects
Street weak equivalences of its actual geometric realization. -/
theorem globe_conjugate_weak_iff {m n : ℕ}
    (f : (complex m).realization ⟶ (complex n).realization) :
    h.streetWeakEquivalences ((globeIso m).hom ≫ f ≫ (globeIso n).inv) ↔
      h.streetWeakEquivalences f := by
  let P : MorphismProperty StrictOmegaCategory.{0} :=
    realizationWeakEquivalences.inverseImage h.streetNerve
  have : P.RespectsIso := by dsimp [P]; infer_instance
  exact (P.cancel_left_of_respectsIso (globeIso m).hom (f ≫ (globeIso n).inv)).trans
    (P.cancel_right_of_respectsIso f (globeIso n).inv)

/-- The signed face maps have exactly the same actual weak-equivalence
status in the free strict and positive-chain presentations. -/
theorem faceMap_weak_iff (a : Bool) (m n : ℕ) :
    h.streetWeakEquivalences (faceMap a m n).realization ↔
      h.streetWeakEquivalences (StrictOmegaCategory.Globe.faceMap a m n) := by
  have he : StrictOmegaCategory.Globe.faceMap a m n =
      (globeIso m).hom ≫ (faceMap a m n).realization ≫ (globeIso n).inv := by
    have he := congrArg (fun q => q ≫ (globeIso n).inv) (fromGlobe_faceMap a m n)
    change (StrictOmegaCategory.Globe.faceMap a m n ≫ (globeIso n).hom) ≫
      (globeIso n).inv = ((globeIso m).hom ≫ (faceMap a m n).realization) ≫
        (globeIso n).inv at he
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he
  rw [he]
  exact (globe_conjugate_weak_iff h _).symm

end

end Thomason.Construction.DirectedGlobeComplex

end

section

/-! # Actual Street comparison for the strict-chain unit on globes

The newly constructed lambda-nu unit is an isomorphism on every strict
globe. Hence it induces an isomorphism of Street nerves and a homeomorphism
of their actual realizations; its weak-equivalence status is unconditional.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open CategoryTheory

noncomputable section

/-- The unit comparison is an actual strict isomorphism on each globe. -/
def globeUnitIso (n : ℕ) : StrictOmegaCategory.Globe.category n ≅
    (StrictOmegaCategory.Abelianization.complex (StrictOmegaCategory.Globe.category n)).realization :=
  globeIso n ≪≫ (DirectedComplex.realizationFunctor.mapIso (abelianizationIso n)).symm

theorem globeUnitIso_hom (n : ℕ) : (globeUnitIso n).hom =
    StrictOmegaCategory.Abelianization.unit (StrictOmegaCategory.Globe.category n) := by
  apply (cancel_mono (DirectedComplex.realizationFunctor.map (abelianizationIso n).hom)).mp
  have he := StrictOmegaCategory.Abelianization.unit_evaluate (fromGlobe n)
  calc
    _ = (globeIso n).hom := by
      let e : (StrictOmegaCategory.Abelianization.complex
          (StrictOmegaCategory.Globe.category n)).realization ≅ (complex n).realization :=
        DirectedComplex.realizationFunctor.mapIso (abelianizationIso n)
      change ((globeIso n).hom ≫ e.inv) ≫ e.hom = (globeIso n).hom
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := he.symm

/-- The unit induces a literal isomorphism of the actual Street nerves. -/
def globeUnitNerveIso (h : NormalizedSimplexIdentities) (n : ℕ) :
    h.streetNerve.obj (StrictOmegaCategory.Globe.category n) ≅
      h.streetNerve.obj
        (StrictOmegaCategory.Abelianization.complex (StrictOmegaCategory.Globe.category n)).realization :=
  h.streetNerve.mapIso (globeUnitIso n)

def globeUnitRealizationHomeomorph (h : NormalizedSimplexIdentities) (n : ℕ) :
    SSet.toTop.obj (h.streetNerve.obj (StrictOmegaCategory.Globe.category n)) ≃ₜ
      SSet.toTop.obj (h.streetNerve.obj
        (StrictOmegaCategory.Abelianization.complex (StrictOmegaCategory.Globe.category n)).realization) :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (globeUnitNerveIso h n))

theorem globe_unit_weak (h : NormalizedSimplexIdentities) (n : ℕ) :
    h.streetWeakEquivalences
      (StrictOmegaCategory.Abelianization.unit (StrictOmegaCategory.Globe.category n)) := by
  let : IsIso (StrictOmegaCategory.Abelianization.unit (StrictOmegaCategory.Globe.category n)) := by
    rw [← globeUnitIso_hom]
    infer_instance
  change realizationWeakEquivalences (h.streetNerve.map _)
  exact MorphismProperty.of_isIso realizationWeakEquivalences _

end

end Thomason.Construction.DirectedGlobeComplex

end

section

/-! # Detecting internal-hom truncation on concrete cylinder globes

The old globe evaluation criterion is rewritten as an equality of strict
functors. Adjunction then moves that test to the actual cylinder of each
finite globe. No truncation conclusion is assumed in the test.
-/

namespace Thomason.Construction

open CategoryTheory

namespace StrictOmegaCategory.Globe

/-- Collapse the universal m-cell to its chosen n-face, retaining all its
lower faces by the universal property of the actual globe. -/
def collapse (a : Bool) (n m : ℕ) : category m ⟶ category m :=
  lift (category m) ((category m).face a n Cell.top)
    (category_truncated m ((category m).face a n Cell.top))

@[simp] theorem collapse_top (a : Bool) (n m : ℕ) :
    (collapse a n m).toFun Cell.top = (category m).face a n Cell.top := rfl

theorem collapse_eq_id (a : Bool) {n m : ℕ} (hmn : m ≤ n) :
    collapse a n m = 𝟙 (category m) := by
  apply hom_ext
  have h := (category m).dimensionLE_mono hmn (category_truncated m Cell.top)
  cases a
  · exact h.1
  · exact h.2

/-- The existing pointwise face criterion is equivalently a test on maps
out of every actual finite globe. -/
theorem truncated_iff_collapse (C : StrictOmegaCategory.{0}) (n : ℕ) :
    C.IsTruncated n ↔ ∀ (m : ℕ) (f : category m ⟶ C) (a : Bool),
      collapse a n m ≫ f = f := by
  rw [truncated_iff_globe_test]
  constructor
  · intro h m f a
    apply hom_ext
    exact h m f a
  · intro h m f a
    exact congrArg (fun g : category m ⟶ C => g.toFun Cell.top) (h m f a)

end StrictOmegaCategory.Globe

/-- Internal-hom truncation reduces to a concrete equality on the
cylinders of finite globes. Naturality of the actual adjunction is the
only transport used here. -/
theorem internalHom_truncated_iff_cylinder_globes
    {F R : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0}} (adj : F ⊣ R)
    (Y : StrictOmegaCategory.{0}) (n : ℕ) :
    (R.obj Y).IsTruncated n ↔
      ∀ (m : ℕ) (f : F.obj (StrictOmegaCategory.Globe.category m) ⟶ Y) (a : Bool),
        F.map (StrictOmegaCategory.Globe.collapse a n m) ≫ f = f := by
  rw [StrictOmegaCategory.Globe.truncated_iff_collapse]
  constructor
  · intro h m f a
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left]
    exact h m ((adj.homEquiv _ _) f) a
  · intro h m g a
    have he := congrArg (adj.homEquiv (StrictOmegaCategory.Globe.category m) Y)
      (h m ((adj.homEquiv _ _).symm g) a)
    simpa only [adj.homEquiv_naturality_left, Equiv.apply_symm_apply] using he

namespace RightGrayInput

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)

/-- Preservation of finite truncations is equivalent to an explicit test on
the cylinders of free globes. -/
theorem internalHom_truncated_iff_globe_test
    (Y : StrictOmegaCategory.{0}) (n : ℕ) :
    (G.internalHom.obj Y).IsTruncated n ↔
      ∀ (m : ℕ) (f : G.cylinder.obj (StrictOmegaCategory.Globe.category m) ⟶ Y)
        (a : Bool), G.cylinder.map (StrictOmegaCategory.Globe.collapse a n m) ≫ f = f :=
  internalHom_truncated_iff_cylinder_globes G.adjunction Y n

end RightGrayInput

end Thomason.Construction

end

section

/-! # Universal pairs of composable strict cells

Gluing two actual free globes along a chosen target and source face is the
finite parameter for a composite. Its universal property retains both
cells and their matching equation. These are the composition parameters
needed to extend the constructed right interval beyond individual globes.
-/

namespace Thomason.Construction.StrictOmegaCategory.PastingGlobe

open CategoryTheory CategoryTheory.Limits

noncomputable section

abbrev category (n m k : ℕ) : StrictOmegaCategory.{0} :=
  pushout (Globe.faceMap true k n) (Globe.faceMap false k m)

abbrev left (n m k : ℕ) : Globe.category n ⟶ category n m k :=
  pushout.inl _ _

abbrev right (n m k : ℕ) : Globe.category m ⟶ category n m k :=
  pushout.inr _ _

def leftCell (n m k : ℕ) : category n m k := (left n m k).toFun Globe.Cell.top

def rightCell (n m k : ℕ) : category n m k := (right n m k).toFun Globe.Cell.top

theorem matching (n m k : ℕ) :
    (category n m k).target k (leftCell n m k) =
      (category n m k).source k (rightCell n m k) := by
  have he := congrArg (fun f : Globe.category k ⟶ category n m k =>
    f.toFun Globe.Cell.top) (pushout.condition (f := Globe.faceMap true k n)
      (g := Globe.faceMap false k m))
  change (left n m k).toFun ((Globe.category n).face true k Globe.Cell.top) =
    (right n m k).toFun ((Globe.category m).face false k Globe.Cell.top) at he
  exact ((left n m k).map_face true k Globe.Cell.top).symm.trans
    (he.trans ((right n m k).map_face false k Globe.Cell.top))

/-- A strict map from the pasted globes is determined by its two cells. -/
theorem hom_ext {n m k : ℕ} {C : StrictOmegaCategory.{0}}
    (f g : category n m k ⟶ C)
    (hl : f.toFun (leftCell n m k) = g.toFun (leftCell n m k))
    (hr : f.toFun (rightCell n m k) = g.toFun (rightCell n m k)) : f = g := by
  apply pushout.hom_ext
  · apply Globe.hom_ext
    exact hl
  · apply Globe.hom_ext
    exact hr

/-- Every matching pair determines its unique strict map from the pasting. -/
def desc {n m k : ℕ} (C : StrictOmegaCategory.{0})
    (x y : C) (hx : C.DimensionLE n x) (hy : C.DimensionLE m y)
    (hxy : C.target k x = C.source k y) : category n m k ⟶ C :=
  pushout.desc (Globe.lift C x hx) (Globe.lift C y hy) (by
    rw [Globe.faceMap_lift, Globe.faceMap_lift]
    apply Globe.hom_ext
    exact hxy)

@[simp] theorem desc_left {n m k : ℕ} (C : StrictOmegaCategory.{0})
    (x y : C) (hx : C.DimensionLE n x) (hy : C.DimensionLE m y)
    (hxy : C.target k x = C.source k y) :
    (desc C x y hx hy hxy).toFun (leftCell n m k) = x := by
  have he := congrArg (fun f : Globe.category n ⟶ C => f.toFun Globe.Cell.top)
    (pushout.inl_desc (Globe.lift C x hx) (Globe.lift C y hy)
      (show Globe.faceMap true k n ≫ Globe.lift C x hx =
        Globe.faceMap false k m ≫ Globe.lift C y hy from by
        rw [Globe.faceMap_lift, Globe.faceMap_lift]
        apply Globe.hom_ext
        exact hxy))
  exact he

@[simp] theorem desc_right {n m k : ℕ} (C : StrictOmegaCategory.{0})
    (x y : C) (hx : C.DimensionLE n x) (hy : C.DimensionLE m y)
    (hxy : C.target k x = C.source k y) :
    (desc C x y hx hy hxy).toFun (rightCell n m k) = y := by
  have he := congrArg (fun f : Globe.category m ⟶ C => f.toFun Globe.Cell.top)
    (pushout.inr_desc (Globe.lift C x hx) (Globe.lift C y hy)
      (show Globe.faceMap true k n ≫ Globe.lift C x hx =
        Globe.faceMap false k m ≫ Globe.lift C y hy from by
        rw [Globe.faceMap_lift, Globe.faceMap_lift]
        apply Globe.hom_ext
        exact hxy))
  exact he

theorem exists_unique_map {n m k : ℕ} (C : StrictOmegaCategory.{0})
    (x y : C) (hx : C.DimensionLE n x) (hy : C.DimensionLE m y)
    (hxy : C.target k x = C.source k y) :
    ∃! f : category n m k ⟶ C,
      f.toFun (leftCell n m k) = x ∧ f.toFun (rightCell n m k) = y := by
  refine ⟨desc C x y hx hy hxy, ⟨desc_left C x y hx hy hxy,
    desc_right C x y hx hy hxy⟩, ?_⟩
  intro f hf
  apply hom_ext
  · exact hf.1.trans (desc_left C x y hx hy hxy).symm
  · exact hf.2.trans (desc_right C x y hx hy hxy).symm

def composite (n m k : ℕ) : category n m k :=
  (category n m k).comp k (leftCell n m k) (rightCell n m k) (matching n m k)

theorem composite_dimension (n m k : ℕ) (hk : k < max n m) :
    (category n m k).DimensionLE (max n m) (composite n m k) := by
  apply (category n m k).dimensionLE_comp hk
  · exact (category n m k).dimensionLE_mono (Nat.le_max_left n m)
      ((left n m k).dimensionLE (Globe.category_truncated n Globe.Cell.top))
  · exact (category n m k).dimensionLE_mono (Nat.le_max_right n m)
      ((right n m k).dimensionLE (Globe.category_truncated m Globe.Cell.top))

/-- The universal composite is itself represented by a strict globe. -/
def compositionMap (n m k : ℕ) (hk : k < max n m) :
    Globe.category (max n m) ⟶ category n m k :=
  Globe.lift _ (composite n m k) (composite_dimension n m k hk)

/-- Evaluation of the pasted universal cell is the specified composition. -/
theorem desc_composite {n m k : ℕ} (C : StrictOmegaCategory.{0})
    (x y : C) (hx : C.DimensionLE n x) (hy : C.DimensionLE m y)
    (hxy : C.target k x = C.source k y) :
    (desc C x y hx hy hxy).toFun (composite n m k) = C.comp k x y hxy := by
  have hh : C.target k ((desc C x y hx hy hxy).toFun (leftCell n m k)) =
      C.source k ((desc C x y hx hy hxy).toFun (rightCell n m k)) := by
    rw [desc_left, desc_right]
    exact hxy
  have he := (desc C x y hx hy hxy).map_comp k (leftCell n m k)
    (rightCell n m k) (matching n m k) hh
  simpa only [composite, desc_left, desc_right] using he

/-- The composition map is compatible with every pair of bounded cells. -/
theorem compositionMap_desc {n m k : ℕ} (hk : k < max n m)
    (C : StrictOmegaCategory.{0}) (x y : C)
    (hx : C.DimensionLE n x) (hy : C.DimensionLE m y)
    (hxy : C.target k x = C.source k y) :
    compositionMap n m k hk ≫ desc C x y hx hy hxy =
      Globe.lift C (C.comp k x y hxy)
        (C.dimensionLE_comp hk (C.dimensionLE_mono (Nat.le_max_left n m) hx)
          (C.dimensionLE_mono (Nat.le_max_right n m) hy) hxy) := by
  apply Globe.hom_ext
  exact desc_composite C x y hx hy hxy

end

end Thomason.Construction.StrictOmegaCategory.PastingGlobe

end

section

/-! # The small globe-and-composition diagram of a strict category

Globes record cells and faces; pasted pairs record composition. This is
the precise small presentation used to extend the right interval cylinder.
-/

namespace Thomason.Construction.StrictOmegaCategory.GlobePasting

open CategoryTheory CategoryTheory.Limits

noncomputable section

inductive Shape
  | globe (n : ℕ)
  | pair (n k : ℕ) (hk : k < n)

def object : Shape → StrictOmegaCategory.{0}
  | .globe n => Globe.category n
  | .pair n k _ => PastingGlobe.category n n k

instance : Category Shape where
  Hom i j := object i ⟶ object j
  id i := 𝟙 (object i)
  comp f g := f ≫ g

def inclusion : Shape ⥤ StrictOmegaCategory.{0} where
  obj := object
  map f := f

def diagram (C : StrictOmegaCategory.{0}) : CostructuredArrow inclusion C ⥤ StrictOmegaCategory :=
  CostructuredArrow.proj inclusion C ⋙ inclusion

def cocone (C : StrictOmegaCategory.{0}) : Cocone (diagram C) where
  pt := C
  ι := {
    app j := j.hom
    naturality _ _ f := (CostructuredArrow.w f).trans (Category.comp_id _).symm }

abbrev globePoint (C : StrictOmegaCategory.{0}) {n : ℕ} (x : C) (hx : C.DimensionLE n x) :
    CostructuredArrow inclusion C :=
  CostructuredArrow.mk (Y := Shape.globe n) (Globe.lift C x hx)

/-- Value assigned by a compatible cocone to a bounded cell. -/
def value {C : StrictOmegaCategory.{0}} (s : Cocone (diagram C))
    {n : ℕ} (x : C) (hx : C.DimensionLE n x) : s.pt :=
  (s.ι.app (globePoint C x hx)).toFun Globe.Cell.top

theorem value_raise {C : StrictOmegaCategory.{0}} (s : Cocone (diagram C))
    {n m : ℕ} (hnm : n ≤ m) (x : C) (hx : C.DimensionLE n x) :
    value s x (C.dimensionLE_mono hnm hx) = value s x hx := by
  let u : object (.globe m) ⟶ object (.globe n) :=
    Globe.lift (Globe.category n) Globe.Cell.top
      ((Globe.category n).dimensionLE_mono hnm (Globe.category_truncated n Globe.Cell.top))
  have hu : u ≫ Globe.lift C x hx = Globe.lift C x (C.dimensionLE_mono hnm hx) := by
    apply Globe.hom_ext
    rfl
  let f : globePoint C x (C.dimensionLE_mono hnm hx) ⟶ globePoint C x hx :=
    CostructuredArrow.homMk u hu
  have he := congrArg (fun k => k.toFun Globe.Cell.top) (s.w f)
  exact he.symm

/-- A compatible family assigns the same value for every finite dimension bound. -/
theorem value_independent {C : StrictOmegaCategory.{0}} (s : Cocone (diagram C))
    {n m : ℕ} (x : C) (hx : C.DimensionLE n x) (hy : C.DimensionLE m x) :
    value s x hx = value s x hy := by
  exact (value_raise s (Nat.le_max_left n m) x hx).symm.trans
    (value_raise s (Nat.le_max_right n m) x hy)

def dimension (C : StrictOmegaCategory.{0}) (x : C) : ℕ :=
  Classical.choose (C.finite_dimension x)

theorem dimension_bound (C : StrictOmegaCategory.{0}) (x : C) :
    C.DimensionLE (dimension C x) x := Classical.choose_spec (C.finite_dimension x)

/-- The candidate map is defined on every actual cell, independently of a bound. -/
def evaluate {C : StrictOmegaCategory.{0}} (s : Cocone (diagram C)) (x : C) : s.pt :=
  value s x (dimension_bound C x)

theorem evaluate_eq_value {C : StrictOmegaCategory.{0}} (s : Cocone (diagram C))
    {n : ℕ} (x : C) (hx : C.DimensionLE n x) : evaluate s x = value s x hx :=
  value_independent s x _ hx

/-- Face preservation is forced by the morphisms between actual free globes. -/
theorem evaluate_face {C : StrictOmegaCategory.{0}} (s : Cocone (diagram C))
    (a : Bool) (m : ℕ) (x : C) :
    evaluate s (C.face a m x) = s.pt.face a m (evaluate s x) := by
  let n := dimension C x
  let hx : C.DimensionLE n x := dimension_bound C x
  let f : globePoint C (C.face a m x) (C.face_dimensionLE a m x) ⟶ globePoint C x hx :=
    CostructuredArrow.homMk (Globe.faceMap a m n) (Globe.faceMap_lift C x hx a m)
  have he := congrArg (fun k => k.toFun Globe.Cell.top) (s.w f)
  rw [evaluate_eq_value s (C.face a m x) (C.face_dimensionLE a m x)]
  exact he.symm.trans ((s.ι.app (globePoint C x hx)).map_face a m Globe.Cell.top)

end

end Thomason.Construction.StrictOmegaCategory.GlobePasting

end

section

/-! # Density of actual globes and composable pairs

Every strict category is the colimit of its small diagram of globes and
pasted pairs. The descent map is proved to preserve actual compositions.
-/

namespace Thomason.Construction.StrictOmegaCategory.GlobePasting

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The descended cell map agrees with every leg on every cell. -/
theorem evaluate_map {C : StrictOmegaCategory.{0}} (s : Cocone (diagram C))
    (i : Shape) (f : object i ⟶ C) (x : object i) :
    evaluate s (f.toFun x) =
      (s.ι.app (CostructuredArrow.mk (Y := i) f)).toFun x := by
  obtain ⟨n, hx⟩ := (object i).finite_dimension x
  have he : Globe.lift (object i) x hx ≫ f =
      Globe.lift C (f.toFun x) (f.dimensionLE hx) := by apply Globe.hom_ext; rfl
  let q : globePoint C (f.toFun x) (f.dimensionLE hx) ⟶
      CostructuredArrow.mk (Y := i) f :=
    CostructuredArrow.homMk (Globe.lift (object i) x hx) he
  have hq := congrArg (fun k => k.toFun Globe.Cell.top) (s.w q)
  exact (evaluate_eq_value s (f.toFun x) (f.dimensionLE hx)).trans hq.symm

/-- Composable pairs force the cellwise descent map to preserve composition. -/
theorem evaluate_comp {C : StrictOmegaCategory.{0}} (s : Cocone (diagram C))
    (k : ℕ) (x y : C) (hxy : C.target k x = C.source k y)
    (h' : s.pt.target k (evaluate s x) = s.pt.source k (evaluate s y)) :
    evaluate s (C.comp k x y hxy) = s.pt.comp k (evaluate s x) (evaluate s y) h' := by
  let n := max (k+1) (max (dimension C x) (dimension C y))
  have hkn : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_left _ _)
  have hx : C.DimensionLE n x := C.dimensionLE_mono
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)) (dimension_bound C x)
  have hy : C.DimensionLE n y := C.dimensionLE_mono
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)) (dimension_bound C y)
  let f : object (.pair n k hkn) ⟶ C := PastingGlobe.desc C x y hx hy hxy
  let l : PastingGlobe.category n n k ⟶ s.pt := s.ι.app (CostructuredArrow.mk (Y := Shape.pair n k hkn) f)
  have hL : evaluate s x = l.toFun (PastingGlobe.leftCell n n k) := by
    have e := evaluate_map s (.pair n k hkn) f (PastingGlobe.leftCell n n k)
    simpa only [f, PastingGlobe.desc_left] using e
  have hR : evaluate s y = l.toFun (PastingGlobe.rightCell n n k) := by
    have e := evaluate_map s (.pair n k hkn) f (PastingGlobe.rightCell n n k)
    simpa only [f, PastingGlobe.desc_right] using e
  have hC : evaluate s (C.comp k x y hxy) = l.toFun (PastingGlobe.composite n n k) := by
    have e := evaluate_map s (.pair n k hkn) f (PastingGlobe.composite n n k)
    simpa only [f, PastingGlobe.desc_composite] using e
  have hl : s.pt.target k (l.toFun (PastingGlobe.leftCell n n k)) =
      s.pt.source k (l.toFun (PastingGlobe.rightCell n n k)) := by
    rw [← hL, ← hR]
    exact h'
  have he := l.map_comp k (PastingGlobe.leftCell n n k) (PastingGlobe.rightCell n n k)
    (PastingGlobe.matching n n k) hl
  apply hC.trans
  apply he.trans
  simp only [← hL, ← hR]

def desc {C : StrictOmegaCategory.{0}} (s : Cocone (diagram C)) : C ⟶ s.pt where
  toFun := evaluate s
  map_face := evaluate_face s
  map_comp := evaluate_comp s

/-- Every strict category has the actual small globe-and-pasting presentation. -/
def isColimit (C : StrictOmegaCategory.{0}) : IsColimit (cocone C) where
  desc := desc
  fac s j := by
    apply Hom.ext
    funext x
    exact evaluate_map s j.left j.hom x
  uniq s f hf := by
    apply Hom.ext
    funext x
    have he := congrArg (fun k => k.toFun Globe.Cell.top)
      (hf (globePoint C x (dimension_bound C x)))
    exact he

end

end Thomason.Construction.StrictOmegaCategory.GlobePasting

end

end OAI
