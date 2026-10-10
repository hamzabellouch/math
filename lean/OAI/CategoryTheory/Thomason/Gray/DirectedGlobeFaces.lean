import OAI.CategoryTheory.Thomason.Chains.SimplexBasisHeight
import OAI.CategoryTheory.Thomason.Gray.CylinderAssembly
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeUniversal
import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Gray.StrictAbelianization
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Whiskering

namespace OAI

section

/-! # Ordered atoms of globes and their right cylinders

The two lower rows of a globe atom are singleton faces. Their linear rank
orders all negative faces before the atom and all positive faces after it.
This supplies generation of each actual globe-cylinder piece.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

def basisAtom (n p : ℕ) (b : Basis n p) : Cell (complex n) :=
  (topCell n).face b.val p

theorem basisAtom_top (n p : ℕ) (b : Basis n p) (side : Bool) :
    (basisAtom n p b).table side p = Finsupp.single b 1 := by
  change Cell.cutTable (topCell n) b.val p side p = _
  simp only [Cell.cutTable, Nat.lt_irrefl, ite_false, ite_true]
  exact topTable_eq_single n p b

theorem basisAtom_above (n p : ℕ) (b : Basis n p) (q : ℕ) (hpq : p < q) (side : Bool) :
    (basisAtom n p b).table side q = 0 :=
  Cell.table_zero_of_dimensionLE ((complex n).realization.face_dimensionLE b.val p
    (topCell n)) hpq side

theorem basisAtom_below (n p : ℕ) (b : Basis n p) (q : ℕ) (hqp : q < p) (side : Bool) :
    (basisAtom n p b).table side q =
      Finsupp.single (⟨side, Or.inl (hqp.trans_le (by
        rcases b.property with h | ⟨h, _⟩ <;> omega))⟩ : Basis n q) 1 := by
  have hqn : q < n := hqp.trans_le (by rcases b.property with h | ⟨h, _⟩ <;> omega)
  change Cell.cutTable (topCell n) b.val p side q = _
  simp only [Cell.cutTable, hqp, ite_true]
  simp [topCell, topTable, hqn]
  rfl

def basisHeight {n p : ℕ} (b : Basis n p) : ℤ :=
  if b.val then 2 * (n : ℤ) - p else p

theorem basisAtom_sideHeight (n p : ℕ) (b : Basis n p) (q : ℕ) (hqp : q < p)
    (side : Bool) (c : Basis n q)
    (hc : DFunLike.coe (F := Chains n q) ((basisAtom n p b).table side q) c ≠ 0) :
    if side then basisHeight b < basisHeight c else basisHeight c < basisHeight b := by
  rw [basisAtom_below n p b q hqp side] at hc
  have he : c.val = side := by
    by_contra h
    have hne : c ≠ (⟨side, Or.inl (hqp.trans_le (by
        rcases b.property with h | ⟨h, _⟩ <;> omega))⟩ : Basis n q) := by
      intro hh
      exact h (congrArg Subtype.val hh)
    exact hc (Finsupp.single_eq_of_ne hne)
  have hpn : p ≤ n := by rcases b.property with h | ⟨h, _⟩ <;> omega
  cases side <;> cases hb : b.val <;> simp only [basisHeight, he, hb, Bool.false_eq_true,
    ite_false, ite_true] <;> omega

def orderedAtomBasis (n : ℕ) : OrderedAtomBasis (complex n) where
  Index p := Basis n p
  coordinates _ := AddEquiv.refl _
  positive_iff _ _ := Iff.rfl
  augmentation := by
    change ∀ x : Chains n 0, weight n 0 x = x.sum (fun _ z => z)
    intro x
    simp [weight, Finsupp.linearCombination_apply]
  atom := basisAtom n
  atom_top := basisAtom_top n
  atom_above := basisAtom_above n
  height _ := basisHeight
  disjoint {p q r} b c hrp hrq hbc e := by
    by_cases he : DFunLike.coe (F := Chains n r) ((basisAtom n p b).table false r) e = 0
    · exact Or.inl he
    · right
      by_contra hf
      have h1 := basisAtom_sideHeight n p b r hrp false e he
      have h2 := basisAtom_sideHeight n q c r hrq true e hf
      simp only [Bool.false_eq_true, ite_false, ite_true] at h1 h2
      exact (lt_irrefl _) (h2.trans (h1.trans_le hbc))

theorem orderedAtomBasis_sideHeight (n : ℕ) : (orderedAtomBasis n).SideHeight :=
  basisAtom_sideHeight n

def cylinderOrderedAtomBasis (n : ℕ) : OrderedAtomBasis (rightCylinder (complex n)) :=
  (orderedAtomBasis n).cylinderOrderedAtomBasis (orderedAtomBasis_sideHeight n)

theorem cylinder_generated (n : ℕ) (P : Cell (rightCylinder (complex n)) → Prop)
    (hatom : ∀ p b, P ((cylinderOrderedAtomBasis n).atom p b))
    (hcomp : ∀ r x y hxy, P x → P y → P (Cell.comp x y r hxy)) : ∀ x, P x :=
  (cylinderOrderedAtomBasis n).generated P hatom hcomp

end
end Thomason.Construction.DirectedGlobeComplex

end

section

/-! # The two ends of the actual simplicial cylinder

An explicit disjoint union avoids any choice of coproduct presentation.
The map from these two copies to the cylinder is proved monic degreewise.
-/

namespace Thomason.Construction.SimplicialCylinder

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe u

/-- Two disjoint copies of a simplicial set, in each degree. -/
def ends (X : SSet.{u}) : SSet.{u} where
  obj m := X.obj m ⊕ X.obj m
  map f := ↾(Sum.map (X.map f) (X.map f))
  map_id m := by ext x; cases x <;> simp
  map_comp f g := by ext x; cases x <;> simp

/-- The map specified independently on the two ends. -/
def desc {X Y : SSet.{u}} (f g : X ⟶ Y) : ends X ⟶ Y where
  app m := ↾(Sum.elim (f.app m) (g.app m))
  naturality m n a := by
    ext x
    cases x with
    | inl x => exact ConcreteCategory.congr_hom (f.naturality a) x
    | inr x => exact ConcreteCategory.congr_hom (g.naturality a) x

def zero (X : SSet.{u}) : X ⟶ ends X where
  app m := ↾Sum.inl

def one (X : SSet.{u}) : X ⟶ ends X where
  app m := ↾Sum.inr

@[simp, reassoc]
theorem zero_desc {X Y : SSet.{u}} (f g : X ⟶ Y) : zero X ≫ desc f g = f := rfl

@[simp, reassoc]
theorem one_desc {X Y : SSet.{u}} (f g : X ⟶ Y) : one X ≫ desc f g = g := rfl

/-- The actual inclusion of the two cylinder ends. -/
noncomputable def inclusion (X : SSet.{u}) : ends X ⟶ X ⊗ Δ[1] :=
  desc SSet.ι₀ SSet.ι₁

@[simp, reassoc]
theorem zero_inclusion (X : SSet.{u}) : zero X ≫ inclusion X = SSet.ι₀ := rfl

@[simp, reassoc]
theorem one_inclusion (X : SSet.{u}) : one X ≫ inclusion X = SSet.ι₁ := rfl

/-- The two ends are disjoint, and each includes injectively. -/
instance inclusion_mono (X : SSet.{u}) : Mono (inclusion X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact congrArg Sum.inl (congrArg Prod.fst he)
    | inr b =>
      have hh := congrArg (fun z => (SSet.stdSimplex.objEquiv z.2) (0 : Fin (m.unop.len+1))) he
      change (0 : Fin 2) = 1 at hh
      exact False.elim (by contradiction)
  | inr a =>
    cases b with
    | inl b =>
      have hh := congrArg (fun z => (SSet.stdSimplex.objEquiv z.2) (0 : Fin (m.unop.len+1))) he
      change (1 : Fin 2) = 0 at hh
      exact False.elim (by contradiction)
    | inr b =>
      exact congrArg Sum.inr (congrArg Prod.fst he)

end Thomason.Construction.SimplicialCylinder

end

section

/-! # The strict unit of the chain realization adjunction

A cell is sent to the table of the additive classes of all its faces.
The finite-dimension condition and the strict composition laws are proved
in the quotient, including the vanishing of identity extensions.
-/

namespace Thomason.Construction.StrictOmegaCategory.Abelianization

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

variable (C : StrictOmegaCategory.{0})

theorem faceGenerator_of_dimension (a : Bool) (n : ℕ) (x : C)
    (hx : C.DimensionLE n x) : faceGenerator C a n x = generator C n ⟨x, hx⟩ := by
  apply congrArg (generator C n)
  exact Subtype.ext (by cases a; exact hx.1; exact hx.2)

theorem faceGenerator_zero (a : Bool) {n m : ℕ} (hnm : n < m) (x : C)
    (hx : C.DimensionLE n x) : faceGenerator C a m x = 0 := by
  cases m with
  | zero => omega
  | succ m =>
    have hx' := C.dimensionLE_mono (show n ≤ m by omega) hx
    rw [faceGenerator_of_dimension C a (m + 1) x (C.dimensionLE_mono (Nat.le_succ m) hx')]
    exact generator_identity C m x hx'

/-- The finite table of the additive classes of a strict cell's faces. -/
def unitCell (x : C) : DirectedComplex.Cell (complex C) where
  table a n := faceGenerator C a n x
  positive a n := generator_positive C n _
  augmentation a := augmentation_faceGenerator C a x
  boundary a n := by
    change differential C n (faceGenerator C a (n + 1) x) = _
    rw [differential_faceGenerator, faceGenerator_face C _ _ (Nat.lt_succ_self n),
      faceGenerator_face C _ _ (Nat.lt_succ_self n)]
    rfl
  finite_support := by
    obtain ⟨n, hn⟩ := C.finite_dimension x
    exact ⟨n, fun m hm a => faceGenerator_zero C a hm x hn⟩

@[simp] theorem unitCell_table (x : C) (a : Bool) (n : ℕ) :
    (unitCell C x).table a n = faceGenerator C a n x := rfl

theorem unitCell_face (a : Bool) (n : ℕ) (x : C) :
    unitCell C (C.face a n x) = (unitCell C x).face a n := by
  apply DirectedComplex.Cell.ext
  funext b m
  change faceGenerator C b m (C.face a n x) = DirectedComplex.Cell.cutTable (unitCell C x) a n b m
  unfold DirectedComplex.Cell.cutTable
  by_cases hmn : m < n
  · rw [ite_eq_left hmn]
    exact faceGenerator_face C b a hmn x
  · rw [ite_eq_right hmn]
    by_cases he : m = n
    · subst m
      rw [ite_eq_left rfl]
      apply congrArg (generator C n)
      exact Subtype.ext (C.face_face_same b a n x)
    · rw [ite_eq_right he]
      exact faceGenerator_zero C b (by omega) _ (C.face_dimensionLE a n x)

/-- Lower faces of a composite are the common lower faces of its factors. -/
theorem face_comp_below (a : Bool) {m n : ℕ} (hmn : m < n) (x y : C)
    (h : C.target n x = C.source n y) :
    C.face a m (C.comp n x y h) = C.face a m x := by
  have hs := congrArg (C.face a m) (C.source_comp n x y h)
  simpa only [source, C.globular, hmn, ite_true] using hs

theorem unitCell_comp (n : ℕ) (x y : C) (h : C.target n x = C.source n y)
    (h' : (unitCell C x).face true n = (unitCell C y).face false n) :
    unitCell C (C.comp n x y h) = DirectedComplex.Cell.comp (unitCell C x) (unitCell C y) n h' := by
  apply DirectedComplex.Cell.ext
  funext a m
  change faceGenerator C a m (C.comp n x y h) = DirectedComplex.Cell.pasteTable (unitCell C x) (unitCell C y) n a m
  unfold DirectedComplex.Cell.pasteTable
  by_cases hmn : m < n
  · rw [ite_eq_left hmn]
    apply congrArg (generator C m)
    exact Subtype.ext (face_comp_below C a hmn x y h)
  · rw [ite_eq_right hmn]
    by_cases he : m = n
    · subst m
      rw [ite_eq_left rfl]
      cases a
      · change faceGenerator C false n (C.comp n x y h) = faceGenerator C false n x
        apply congrArg (generator C n)
        exact Subtype.ext (C.source_comp n x y h)
      · change faceGenerator C true n (C.comp n x y h) = faceGenerator C true n y
        apply congrArg (generator C n)
        exact Subtype.ext (C.target_comp n x y h)
    · rw [ite_eq_right he]
      exact faceGenerator_composite C a n (by omega) x y h

/-- The concrete unit into the realization of lambda. -/
def unit : C ⟶ (complex C).realization where
  toFun := unitCell C
  map_face := unitCell_face C
  map_comp := unitCell_comp C

end

end Thomason.Construction.StrictOmegaCategory.Abelianization

end

section

/-! # Evaluating the strict chain presentation in a directed complex

Every strict functor to nu K induces a positive augmented chain map from
lambda C. The proof checks the actual composition relations and the signed
boundary; it makes no fullness assumption about realization.
-/

namespace Thomason.Construction.StrictOmegaCategory.Abelianization

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

variable {C : StrictOmegaCategory.{0}} {K : DirectedComplex.{0}}

/-- The degree n component extracted from a strict functor to nu K. -/
def evaluate (f : C ⟶ K.realization) (n : ℕ) : Chains C n →+ K.group n :=
  lift C n (fun x => (f.toFun x.val).table false n) (by
    intro k hk x y h
    have hh : (f.toFun x.val).face true k = (f.toFun y.val).face false k :=
      (f.map_face true k x.val).symm.trans ((congrArg f.toFun h).trans (f.map_face false k y.val))
    have he := f.map_comp k x.val y.val h hh
    change (f.toFun (C.comp k x.val y.val h)).table false n = _
    rw [he]
    change DirectedComplex.Cell.pasteTable _ _ k false n = _
    simp only [DirectedComplex.Cell.pasteTable, Nat.not_lt.mpr hk.le, Nat.ne_of_gt hk, ite_false])

@[simp] theorem evaluate_generator (f : C ⟶ K.realization) (n : ℕ) (x : Bounded C n) :
    evaluate f n (generator C n x) = (f.toFun x.val).table false n :=
  lift_generator C _ _ _ x

@[simp] theorem evaluate_faceGenerator (f : C ⟶ K.realization) (a : Bool) (n : ℕ) (x : C) :
    evaluate f n (faceGenerator C a n x) = (f.toFun x).table a n := by
  change evaluate f n (generator C n ⟨C.face a n x, C.face_dimensionLE a n x⟩) = _
  rw [evaluate_generator, f.map_face]
  change DirectedComplex.Cell.cutTable (f.toFun x) a n false n = _
  simp only [DirectedComplex.Cell.cutTable, Nat.lt_irrefl, ite_false, ite_true]

theorem evaluate_differential (f : C ⟶ K.realization) (n : ℕ) (x : Chains C (n + 1)) :
    evaluate f n (differential C n x) = K.differential n (evaluate f (n + 1) x) := by
  have he : (evaluate f n).comp (differential C n) =
      (K.differential n).comp (evaluate f (n + 1)) := by
    apply hom_ext
    intro y
    simp only [AddMonoidHom.comp_apply, differential_generator, map_sub,
      evaluate_faceGenerator, evaluate_generator]
    exact ((f.toFun y.val).boundary false n).symm
  exact DFunLike.congr_fun he x

theorem evaluate_augmentation (f : C ⟶ K.realization) (x : Chains C 0) :
    K.augmentation (evaluate f 0 x) = augmentation C x := by
  have he : K.augmentation.comp (evaluate f 0) = augmentation C := by
    apply hom_ext
    intro y
    simp only [AddMonoidHom.comp_apply, evaluate_generator, augmentation_generator]
    exact (f.toFun y.val).augmentation false
  exact DFunLike.congr_fun he x

theorem evaluate_positive (f : C ⟶ K.realization) (n : ℕ) {x : Chains C n}
    (hx : x ∈ positive C n) : evaluate f n x ∈ K.positive n := by
  have he : positive C n ≤ (K.positive n).comap (evaluate f n) := by
    apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨y, rfl⟩
    change evaluate f n (generator C n y) ∈ K.positive n
    rw [evaluate_generator]
    exact (f.toFun y.val).positive false n
  exact he hx

/-- The augmented positive chain map obtained from an arbitrary strict map. -/
def evaluateHom (f : C ⟶ K.realization) : DirectedComplex.Hom (complex C) K where
  app := evaluate f
  differential := evaluate_differential f
  augmentation := evaluate_augmentation f
  positive := evaluate_positive f

/-- Evaluation followed by the constructed unit recovers every strict cell. -/
theorem unit_evaluate (f : C ⟶ K.realization) :
    StrictOmegaCategory.Hom.comp (unit C) (evaluateHom f).realization = f := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply DirectedComplex.Cell.ext
  funext a n
  exact evaluate_faceGenerator f a n x

/-- The generator of any bounded cell is its unit table at that degree. -/
theorem unitCell_top (n : ℕ) (x : Bounded C n) :
    (unitCell C x.val).table false n = generator C n x :=
  faceGenerator_of_dimension C false n x.val x.property

/-- Every positive chain map is uniquely recovered from its realized unit. -/
theorem evaluate_unit (g : DirectedComplex.Hom (complex C) K) :
    evaluateHom (StrictOmegaCategory.Hom.comp (unit C) g.realization) = g := by
  apply DirectedComplex.Hom.ext_app
  intro n
  suffices he : evaluate (StrictOmegaCategory.Hom.comp (unit C) g.realization) n = g.app n from
    DFunLike.congr_fun he
  apply hom_ext
  intro x
  change evaluate (StrictOmegaCategory.Hom.comp (unit C) g.realization) n
      (generator C n x) = g.app n (generator C n x)
  rw [evaluate_generator]
  change g.app n ((unitCell C x.val).table false n) = _
  rw [unitCell_top]

/-- The actual lambda-nu hom-set equivalence. -/
def homEquiv (C : StrictOmegaCategory.{0}) (K : DirectedComplex.{0}) :
    DirectedComplex.Hom (complex C) K ≃ (C ⟶ K.realization) where
  toFun g := StrictOmegaCategory.Hom.comp (unit C) g.realization
  invFun := evaluateHom
  left_inv := evaluate_unit
  right_inv := unit_evaluate

end

end Thomason.Construction.StrictOmegaCategory.Abelianization

end

section

/-! # The strict-category / directed-complex adjunction

The two inverse constructions are natural. In particular lambda preserves
strict pushouts, so the universal pasted-globe relations have a canonical
positive-chain presentation before applying the right interval tensor.
-/

namespace Thomason.Construction.StrictOmegaCategory.Abelianization

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

variable {C D E : StrictOmegaCategory.{0}}

/-- The chain map induced by an arbitrary strict functor. -/
def map (f : C ⟶ D) : DirectedComplex.Hom (complex C) (complex D) :=
  evaluateHom (f ≫ unit D)

@[simp] theorem map_generator (f : C ⟶ D) (n : ℕ) (x : Bounded C n) :
    (map f).app n (generator C n x) = generator D n ⟨f.toFun x.val, f.dimensionLE x.property⟩ := by
  change evaluate (f ≫ unit D) n (generator C n x) = _
  rw [evaluate_generator]
  exact unitCell_top n ⟨f.toFun x.val, f.dimensionLE x.property⟩

/-- The concrete strict abelianization functor. -/
def functor : StrictOmegaCategory.{0} ⥤ DirectedComplex.{0} where
  obj := complex
  map := map
  map_id C := by
    apply DirectedComplex.Hom.ext_app
    intro n z
    have he : (map (𝟙 C)).app n = AddMonoidHom.id _ := by
      apply hom_ext
      intro x
      exact map_generator (𝟙 C) n x
    exact DFunLike.congr_fun he z
  map_comp f g := by
    apply DirectedComplex.Hom.ext_app
    intro n z
    have he : (map (f ≫ g)).app n = ((map g).app n).comp ((map f).app n) := by
      apply hom_ext
      intro x
      exact (map_generator (f ≫ g) n x).trans
        ((congrArg ((map g).app n) (map_generator f n x)).trans
          (map_generator g n ⟨f.toFun x.val, f.dimensionLE x.property⟩)).symm
    exact DFunLike.congr_fun he z

/-- Naturality in the strict source, checked on actual bounded-cell generators. -/
theorem evaluate_naturality {K : DirectedComplex.{0}} (f : C ⟶ D) (g : D ⟶ K.realization) :
    DirectedComplex.Hom.comp (map f) (evaluateHom g) = evaluateHom (f ≫ g) := by
  apply DirectedComplex.Hom.ext_app
  intro n z
  have he : ((evaluateHom g).app n).comp ((map f).app n) =
      (evaluateHom (f ≫ g)).app n := by
    apply hom_ext
    intro x
    change evaluate g n ((map f).app n (generator C n x)) =
      evaluate (f ≫ g) n (generator C n x)
    rw [map_generator, evaluate_generator, evaluate_generator]
    rfl
  exact DFunLike.congr_fun he z

/-- Lambda is left adjoint to the actual positive-table realization nu. -/
def adjunction : functor ⊣ realizationFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun C K => homEquiv C K
    homEquiv_naturality_left_symm := fun f g => (evaluate_naturality f g).symm
    homEquiv_naturality_right := fun g f => by
      apply StrictOmegaCategory.Hom.ext
      funext x
      apply DirectedComplex.Cell.ext
      rfl }

/-- The abelianization carries every existing strict colimit to the
corresponding directed-complex colimit, including the pasted globe squares. -/
theorem preservesColimits : Limits.PreservesColimitsOfSize.{0, 0} functor := by
  have := adjunction.isLeftAdjoint
  infer_instance

end

end Thomason.Construction.StrictOmegaCategory.Abelianization

end

section

/-! # The chain presentation recovers the explicit globe complexes

The unit/evaluation adjunction identifies lambda of an actual strict globe
with its signed positive globe complex. This checks the new presentation
against the concrete parameters already used for right cylinders.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- Evaluation from the additive strict-cell presentation to the explicit
positive globe chains. -/
def abelianizationToGlobe (n : ℕ) :
    DirectedComplex.Hom (StrictOmegaCategory.Abelianization.complex (StrictOmegaCategory.Globe.category n)) (complex n) :=
  StrictOmegaCategory.Abelianization.evaluateHom (fromGlobe n)

/-- The universal top cell supplies the reverse positive chain map. -/
def globeToAbelianization (n : ℕ) :
    DirectedComplex.Hom (complex n) (StrictOmegaCategory.Abelianization.complex (StrictOmegaCategory.Globe.category n)) :=
  cellMap n (StrictOmegaCategory.Abelianization.unitCell _ StrictOmegaCategory.Globe.Cell.top)

theorem globeToAbelianization_top (n : ℕ) :
    (globeToAbelianization n).realization.toFun (topCell n) =
      StrictOmegaCategory.Abelianization.unitCell _ StrictOmegaCategory.Globe.Cell.top := by
  apply cellMap_top_of_bounded
  exact (StrictOmegaCategory.Abelianization.unit _).dimensionLE
    (StrictOmegaCategory.Globe.category_truncated n StrictOmegaCategory.Globe.Cell.top)

theorem abelianizationToGlobe_top (n : ℕ) :
    (abelianizationToGlobe n).realization.toFun
      (StrictOmegaCategory.Abelianization.unitCell _ StrictOmegaCategory.Globe.Cell.top) = topCell n := by
  have he := congrArg (fun f : StrictOmegaCategory.Globe.category n ⟶ (complex n).realization =>
    f.toFun StrictOmegaCategory.Globe.Cell.top) (StrictOmegaCategory.Abelianization.unit_evaluate (fromGlobe n))
  exact he

theorem abelianizationToGlobe_inverse (n : ℕ) :
    DirectedComplex.Hom.comp (abelianizationToGlobe n) (globeToAbelianization n) =
      DirectedComplex.Hom.id _ := by
  apply (StrictOmegaCategory.Abelianization.homEquiv (StrictOmegaCategory.Globe.category n) _).injective
  apply StrictOmegaCategory.Globe.hom_ext
  change (globeToAbelianization n).realization.toFun
    ((abelianizationToGlobe n).realization.toFun
      (StrictOmegaCategory.Abelianization.unitCell _ StrictOmegaCategory.Globe.Cell.top)) = StrictOmegaCategory.Abelianization.unitCell _ StrictOmegaCategory.Globe.Cell.top
  rw [abelianizationToGlobe_top, globeToAbelianization_top]

theorem globeToAbelianization_inverse (n : ℕ) :
    DirectedComplex.Hom.comp (globeToAbelianization n) (abelianizationToGlobe n) =
      DirectedComplex.Hom.id _ := by
  apply (homEquiv n (complex n)).injective
  apply Subtype.ext
  change (abelianizationToGlobe n).realization.toFun
    ((globeToAbelianization n).realization.toFun (topCell n)) = topCell n
  rw [globeToAbelianization_top, abelianizationToGlobe_top]

/-- The positive chain presentation of a strict globe is exactly the
explicit globe complex, not an additional comparison input. -/
def abelianizationIso (n : ℕ) : StrictOmegaCategory.Abelianization.complex (StrictOmegaCategory.Globe.category n) ≅ complex n where
  hom := abelianizationToGlobe n
  inv := globeToAbelianization n
  hom_inv_id := abelianizationToGlobe_inverse n
  inv_hom_id := globeToAbelianization_inverse n

end

end Thomason.Construction.DirectedGlobeComplex

end

section

/-! # Natural chain presentations of all strict globe maps

The canonical isomorphisms from the abelianization of each globe to its
explicit chain complex are compatible with every strict globe map. Their
right-cylinder realizations therefore give a natural comparison of the
chain model with the concrete globe cylinders.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open CategoryTheory CategoryTheory.Functor _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- Naturality is proved through the actual lambda-nu adjunction, whose
unit followed by globe evaluation is the canonical globe isomorphism. -/
def abelianizationGlobeIso :
    StrictOmegaCategory.Globe.inclusion ⋙ StrictOmegaCategory.Abelianization.functor ≅
      chainFunctor :=
  NatIso.ofComponents (fun i => abelianizationIso i.dim) (fun {i j} f => by
    let f' : StrictOmegaCategory.Globe.category i.dim ⟶
        StrictOmegaCategory.Globe.category j.dim := f
    let a : StrictOmegaCategory.Abelianization.functor.obj
        (StrictOmegaCategory.Globe.category i.dim) ⟶ complex i.dim :=
      (abelianizationIso i.dim).hom
    let b : StrictOmegaCategory.Abelianization.functor.obj
        (StrictOmegaCategory.Globe.category j.dim) ⟶ complex j.dim :=
      (abelianizationIso j.dim).hom
    change StrictOmegaCategory.Abelianization.functor.map f' ≫ b = a ≫ chainMap f'
    apply (StrictOmegaCategory.Abelianization.adjunction.homEquiv _ _).injective
    rw [StrictOmegaCategory.Abelianization.adjunction.homEquiv_naturality_left,
      StrictOmegaCategory.Abelianization.adjunction.homEquiv_naturality_right]
    change f' ≫ (StrictOmegaCategory.Abelianization.unit _ ≫
        (StrictOmegaCategory.Abelianization.evaluateHom (fromGlobe j.dim)).realization) =
      (StrictOmegaCategory.Abelianization.unit _ ≫
        (StrictOmegaCategory.Abelianization.evaluateHom (fromGlobe i.dim)).realization) ≫ (chainMap f').realization
    have hunit (r : ℕ) : StrictOmegaCategory.Abelianization.unit
        (StrictOmegaCategory.Globe.category r) ≫
          (StrictOmegaCategory.Abelianization.evaluateHom (fromGlobe r)).realization =
        (globeIso r).hom := StrictOmegaCategory.Abelianization.unit_evaluate (fromGlobe r)
    rw [hunit, hunit, chainMap_realization]
    change f' ≫ (globeIso j.dim).hom =
      (globeIso i.dim).hom ≫ ((globeIso i.dim).inv ≫ f' ≫ (globeIso j.dim).hom)
    simp only [Iso.hom_inv_id_assoc])

/-- Tensoring the natural chain presentations with the right interval and
realizing gives the exact globe restriction of the chain model. -/
def rightCylinderAbelianizationGlobeIso :
    StrictOmegaCategory.Globe.inclusion ⋙
        (StrictOmegaCategory.Abelianization.functor ⋙ rightCylinderFunctor ⋙ realizationFunctor) ≅
      rightGlobeCylinder :=
  (Functor.associator StrictOmegaCategory.Globe.inclusion
    StrictOmegaCategory.Abelianization.functor (rightCylinderFunctor ⋙ realizationFunctor)).symm ≪≫
      isoWhiskerRight abelianizationGlobeIso (rightCylinderFunctor ⋙ realizationFunctor)

end

end Thomason.Construction.DirectedGlobeComplex

end

section

/-! # The degreewise inverse of oriental abelianization

The explicit simplex atoms give basis lifts. Positivity prevents a
composition from hiding atoms above its dimension bound. Generation is
expressed by `SimplexAtomsInput.generated` (Steiner 2004, Theorem 5.6).
-/

namespace Thomason.Construction.SimplexAtomsInput

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex SimplexComplex

noncomputable section

variable {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)

/-- The top chain of the chosen atom is its literal normalized basis element. -/
theorem atom_top {m p : ℕ} (b : Basis m p) (side : Bool) :
    (a.atom b).table side p = Finsupp.single b 1 := by
  change mapChains b.toOrderHom p ((a.principal p).table side p) = _
  rw [(a.principal_table p).1 side, mapChains_single, one_smul]
  unfold mapBasis
  rw [dite_eq_left (show StrictMono (fun i => b.toOrderHom (topBasis p i)) from b.strictMono)]
  rfl

/-- There are no atom chains above its basis dimension. -/
theorem atom_above_zero {m p : ℕ} (b : Basis m p) {n : ℕ} (hpn : p < n) (side : Bool) :
    (a.atom b).table side n = 0 := by
  change mapChains b.toOrderHom n ((a.principal p).table side n) = 0
  rw [(a.principal_table p).2.2 side n hpn, map_zero]

theorem atom_dimension {m p : ℕ} (b : Basis m p) :
    (h.object m).DimensionLE p (a.atom b) :=
  Cell.dimensionLE_of_table_zero (fun _ hn side => a.atom_above_zero b hn side)

/-- The nonzero top chain detects the exact dimension of an atom. -/
theorem atom_dimension_iff {m p n : ℕ} (b : Basis m p) :
    (h.object m).DimensionLE n (a.atom b) ↔ p ≤ n := by
  constructor
  · intro hx
    by_contra hn
    have hz := Cell.table_zero_of_dimensionLE hx (Nat.lt_of_not_ge hn) false
    rw [a.atom_top b false] at hz
    exact (Finsupp.single_ne_zero.mpr (by norm_num : (1 : ℤ) ≠ 0)) hz
  · intro hn
    exact (h.object m).dimensionLE_mono hn (a.atom_dimension b)

/-- A normalized simplex's positive cone admits no nonzero cancellation. -/
theorem positive_add_zero {m p : ℕ} (x y : (directedComplex m (h.squared m)).group p)
    (hx : x ∈ (directedComplex m (h.squared m)).positive p)
    (hy : y ∈ (directedComplex m (h.squared m)).positive p) (he : x + y = 0) :
    x = 0 ∧ y = 0 := by
  have hf (b : Basis m p) : x b = 0 ∧ y b = 0 := by
    have hb := congrArg (fun z : Chains m p => z b) he
    have hxb := hx b
    have hyb := hy b
    change x b + y b = 0 at hb
    omega
  exact ⟨Finsupp.ext (fun b => (hf b).1), Finsupp.ext (fun b => (hf b).2)⟩

/-- Lift a normalized basis element to the corresponding actual strict cell. -/
def basisLift (m p : ℕ) : Chains m p →+ StrictOmegaCategory.Abelianization.Chains (h.object m) p :=
  (Finsupp.linearCombination ℤ (fun b : Basis m p =>
    StrictOmegaCategory.Abelianization.generator (h.object m) p
      ⟨a.atom b, a.atom_dimension b⟩)).toAddMonoidHom

@[simp] theorem basisLift_single {m p : ℕ} (b : Basis m p) (z : ℤ) :
    a.basisLift m p (Finsupp.single b z) = z •
      StrictOmegaCategory.Abelianization.generator (h.object m) p
        ⟨a.atom b, a.atom_dimension b⟩ := by
  simp [basisLift]

/-- The basis lift recovers every bounded strict cell, using composition
generation of the simplex atoms. -/
theorem basisLift_cell (m : ℕ) : ∀ x : h.object m, ∀ n (hx : (h.object m).DimensionLE n x),
    a.basisLift m n (x.table false n) =
      StrictOmegaCategory.Abelianization.generator (h.object m) n ⟨x, hx⟩ := by
  apply a.generated m (fun x => ∀ n (hx : (h.object m).DimensionLE n x),
    a.basisLift m n (x.table false n) =
      StrictOmegaCategory.Abelianization.generator (h.object m) n ⟨x, hx⟩)
  · intro p b n hx
    have hpn := (a.atom_dimension_iff b).mp hx
    rcases hpn.eq_or_lt with he | he
    · subst n
      exact (congrArg (a.basisLift m p) (a.atom_top b false)).trans
        ((a.basisLift_single b 1).trans (one_smul ℤ _))
    · exact (congrArg (a.basisLift m n) (a.atom_above_zero b he false)).trans
        ((map_zero _).trans
          ((StrictOmegaCategory.Abelianization.faceGenerator_zero (h.object m) false he
            (a.atom b) (a.atom_dimension b)).symm.trans
              (StrictOmegaCategory.Abelianization.faceGenerator_of_dimension (h.object m) false n
                (a.atom b) hx)))
  · intro k x y hxy ihx ihy n hc
    have hp : ∀ p (u v : (directedComplex m (h.squared m)).group p),
        u ∈ (directedComplex m (h.squared m)).positive p →
        v ∈ (directedComplex m (h.squared m)).positive p →
        u + v = 0 → u = 0 ∧ v = 0 := fun _ u v hu hv he => positive_add_zero (h := h) u v hu hv he
    obtain ⟨hx, hy⟩ := Cell.dimensionLE_comp_factors hp hxy hc
    by_cases hkn : k < n
    · have ht : ((h.object m).comp k x y hxy).table false n =
          x.table false n + y.table false n := by
        change Cell.pasteTable x y k false n = _
        simp only [Cell.pasteTable, Nat.not_lt.mpr hkn.le, Nat.ne_of_gt hkn, ite_false]
      rw [ht, map_add, ihx n hx, ihy n hy]
      exact (StrictOmegaCategory.Abelianization.generator_composite (h.object m) k hkn
        ⟨x, hx⟩ ⟨y, hy⟩ hxy).symm
    · have he := (h.object m).comp_of_dimensionLE (Nat.le_of_not_gt hkn) hx hxy
      calc
        _ = a.basisLift m n (y.table false n) :=
          congrArg (fun z : h.object m => a.basisLift m n (z.table false n)) he
        _ = StrictOmegaCategory.Abelianization.generator (h.object m) n ⟨y, hy⟩ := ihy n hy
        _ = _ := congrArg (StrictOmegaCategory.Abelianization.generator (h.object m) n)
          (Subtype.ext he.symm)

end

end Thomason.Construction.SimplexAtomsInput

end

section

/-! # The explicit normalized-chain comparison for orientals

The counit of lambda–nu has the inverse given by the actual simplex atoms.
The comparison uses composition generation of the simplex atoms.
-/

namespace Thomason.Construction.SimplexAtomsInput

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex SimplexComplex

noncomputable section

variable {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)

/-- Evaluate the additive classes of strict cells in their original chains. -/
def toSimplexChains (_a : SimplexAtomsInput h) (m : ℕ) :
    Hom (StrictOmegaCategory.Abelianization.complex (h.object m))
      (directedComplex m (h.squared m)) :=
  StrictOmegaCategory.Abelianization.evaluateHom (𝟙 (h.object m))

/-- Evaluation with explicit unbundled chain-group types. -/
def toSimplexApp (m n : ℕ) :
    StrictOmegaCategory.Abelianization.Chains (h.object m) n →+ Chains m n :=
  (a.toSimplexChains m).app n

@[simp] theorem toSimplexChains_generator (m n : ℕ)
    (x : StrictOmegaCategory.Abelianization.Bounded (h.object m) n) :
    a.toSimplexApp m n
      (StrictOmegaCategory.Abelianization.generator (h.object m) n x) =
      x.val.table false n :=
  StrictOmegaCategory.Abelianization.evaluate_generator (𝟙 (h.object m)) n x

/-- The strict-cell relations impose no additional normalized-chain relation. -/
theorem toSimplexChains_basisLift (m n : ℕ) (z : Chains m n) :
    a.toSimplexApp m n (a.basisLift m n z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single b z =>
    rw [a.basisLift_single, map_zsmul, a.toSimplexChains_generator, a.atom_top]
    simp

/-- Every additive strict-cell class is recovered by the basis inverse. -/
theorem basisLift_toSimplexChains (m n : ℕ)
    (z : StrictOmegaCategory.Abelianization.Chains (h.object m) n) :
    a.basisLift m n (a.toSimplexApp m n z) = z := by
  have he : (a.basisLift m n).comp (a.toSimplexApp m n) = AddMonoidHom.id _ := by
    apply StrictOmegaCategory.Abelianization.hom_ext
    intro x
    change a.basisLift m n (a.toSimplexApp m n
      (StrictOmegaCategory.Abelianization.generator (h.object m) n x)) = _
    exact (congrArg (a.basisLift m n) (a.toSimplexChains_generator m n x)).trans
      (a.basisLift_cell m x.val n x.property)
  exact DFunLike.congr_fun he z

/-- In particular evaluation is injective in every degree. -/
theorem toSimplexChains_injective (m n : ℕ) :
    Function.Injective (a.toSimplexApp m n) := by
  intro x y hxy
  exact (a.basisLift_toSimplexChains m n x).symm.trans
    ((congrArg (a.basisLift m n) hxy).trans (a.basisLift_toSimplexChains m n y))

/-- The inverse sends positive basis combinations to positive strict-cell classes. -/
theorem basisLift_positive (m n : ℕ) {z : Chains m n} (hz : z ∈ positive m n) :
    a.basisLift m n z ∈ StrictOmegaCategory.Abelianization.positive (h.object m) n := by
  classical
  change (z.sum fun b k => k •
    StrictOmegaCategory.Abelianization.generator (h.object m) n
      ⟨a.atom b, a.atom_dimension b⟩) ∈ _
  apply (StrictOmegaCategory.Abelianization.positive (h.object m) n).sum_mem
  intro b hb
  change z b • StrictOmegaCategory.Abelianization.generator (h.object m) n
    ⟨a.atom b, a.atom_dimension b⟩ ∈ _
  rw [← Int.toNat_of_nonneg (hz b), natCast_zsmul]
  exact (StrictOmegaCategory.Abelianization.positive (h.object m) n).nsmul_mem
    (StrictOmegaCategory.Abelianization.generator_positive (h.object m) n _) _

/-- Differential compatibility follows from injectivity of the evaluated
chains; the basis construction already gives both inverse equations. -/
def fromSimplexChains (m : ℕ) :
    Hom (directedComplex m (h.squared m))
      (StrictOmegaCategory.Abelianization.complex (h.object m)) where
  app := a.basisLift m
  differential n x := by
    apply a.toSimplexChains_injective m n
    exact (a.toSimplexChains_basisLift m n _).trans
      (((a.toSimplexChains m).differential n (a.basisLift m (n+1) x)).trans
        (congrArg ((directedComplex m (h.squared m)).differential n)
          (a.toSimplexChains_basisLift m (n+1) x))).symm
  augmentation x := by
    have he := (a.toSimplexChains m).augmentation (a.basisLift m 0 x)
    exact he.symm.trans (congrArg (directedComplex m (h.squared m)).augmentation
      (a.toSimplexChains_basisLift m 0 x))
  positive n _ hz := a.basisLift_positive m n hz

/-- The actual directed-complex isomorphism, with all positivity and
augmentation information retained. -/
def abelianizationIso (m : ℕ) :
    StrictOmegaCategory.Abelianization.complex (h.object m) ≅
      directedComplex m (h.squared m) where
  hom := a.toSimplexChains m
  inv := a.fromSimplexChains m
  hom_inv_id := by
    apply DirectedComplex.Hom.ext_app
    intro n x
    exact a.basisLift_toSimplexChains m n x
  inv_hom_id := by
    apply DirectedComplex.Hom.ext_app
    intro n x
    exact a.toSimplexChains_basisLift m n x

end

end Thomason.Construction.SimplexAtomsInput

end

section

/-! # Globular face maps and the dimension test

The actual free-globe representation makes every strict cell observable.
In particular, truncation is detected by the source and target equations
on these maps. No interval tensor or internal-hom conclusion is assumed.
-/

namespace Thomason.Construction.StrictOmegaCategory.Globe

open CategoryTheory

/-- The chosen m-face of the universal n-cell. For m ≥ n this is its
identity extension, so the same definition covers every pair of indices. -/
def faceMap (a : Bool) (m n : ℕ) : category m ⟶ category n :=
  lift (category n) ((category n).face a m Cell.top)
    ((category n).face_dimensionLE a m Cell.top)

@[simp] theorem faceMap_top (a : Bool) (m n : ℕ) :
    (faceMap a m n).toFun Cell.top = (category n).face a m Cell.top := rfl

@[simp] theorem faceMap_self (a : Bool) (n : ℕ) : faceMap a n n = 𝟙 (category n) := by
  apply hom_ext
  exact face_of_dimension_le a n Cell.top le_rfl

/-- The two iterated faces of a higher globe obey the strict globular law. -/
theorem faceMap_comp (a b : Bool) (m k n : ℕ) (hmk : m < k) :
    faceMap a m k ≫ faceMap b k n = faceMap a m n := by
  apply hom_ext
  change (faceMap b k n).toFun ((category k).face a m Cell.top) = _
  exact ((faceMap b k n).map_face a m Cell.top).trans
    (((category n).globular a b m k Cell.top).trans (ite_eq_left hmk))

/-- Precomposing the universal cell map with a face gives its actual
source or target cell. -/
theorem faceMap_lift (C : StrictOmegaCategory) {n : ℕ} (x : C) (hx : C.DimensionLE n x)
    (a : Bool) (m : ℕ) :
    faceMap a m n ≫ lift C x hx =
      lift C (C.face a m x) (C.face_dimensionLE a m x) := by
  apply hom_ext
  exact (lift C x hx).map_face a m Cell.top

/-- Truncation is exactly the pointwise n-boundary test on all universal
finite cells. This supplies the dimension interface for an internal hom. -/
theorem truncated_iff_globe_test (C : StrictOmegaCategory) (n : ℕ) :
    C.IsTruncated n ↔ ∀ (m : ℕ) (f : category m ⟶ C) (a : Bool),
      f.toFun ((category m).face a n Cell.top) = f.toFun Cell.top := by
  constructor
  · intro h m f a
    apply (f.map_face a n Cell.top).trans
    cases a
    · exact (h _).1
    · exact (h _).2
  · intro h x
    obtain ⟨m, hm⟩ := C.finite_dimension x
    let f := lift C x hm
    have hs := h m f false
    have ht := h m f true
    exact ⟨(f.map_face false n Cell.top).symm.trans hs,
      (f.map_face true n Cell.top).symm.trans ht⟩

end Thomason.Construction.StrictOmegaCategory.Globe

end

section

/-! # Compatibility of strict globe faces with their chain cylinders

The positive chain maps for globular faces recover the actual strict face
maps. Tensoring these maps on the right respects both endpoint inclusions
and the interval collapse, before any abstract Gray extension is supplied.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

def faceMap (a : Bool) (m n : ℕ) : Hom (complex m) (complex n) :=
  cellMap m ((topCell n).face a m)

theorem faceMap_top (a : Bool) (m n : ℕ) :
    (faceMap a m n).realization.toFun (topCell m) = (topCell n).face a m := by
  apply cellMap_top_of_bounded
  exact (complex n).realization.face_dimensionLE a m (topCell n)

/-- The square from the actual free globe to its chain realization
commutes on each source and target map. -/
theorem fromGlobe_faceMap (a : Bool) (m n : ℕ) :
    StrictOmegaCategory.Globe.faceMap a m n ≫ fromGlobe n =
      fromGlobe m ≫ (faceMap a m n).realization := by
  apply StrictOmegaCategory.Globe.hom_ext
  change (fromGlobe n).toFun ((StrictOmegaCategory.Globe.category n).face a m
      StrictOmegaCategory.Globe.Cell.top) =
    (faceMap a m n).realization.toFun (topCell m)
  exact ((fromGlobe n).map_face a m StrictOmegaCategory.Globe.Cell.top).trans
    (faceMap_top a m n).symm

/-- The right-cylinder face maps preserve the two strict endpoint maps. -/
theorem faceMap_right_endpoint (a e : Bool) (m n : ℕ) :
    StrictOmegaCategory.Hom.comp (faceMap a m n).realization
      (RightCylinder.endpoint (complex n) e).realization =
      StrictOmegaCategory.Hom.comp (RightCylinder.endpoint (complex m) e).realization
        (RightCylinder.map (faceMap a m n)).realization := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply Cell.ext
  funext b k
  exact (RightCylinder.map_endpoint (faceMap a m n) e k (x.table b k)).symm

/-- Interval collapse also commutes with the concrete chain face map. -/
theorem faceMap_right_projection (a : Bool) (m n : ℕ) :
    StrictOmegaCategory.Hom.comp (RightCylinder.map (faceMap a m n)).realization
      (RightCylinder.projection (complex n)).realization =
      StrictOmegaCategory.Hom.comp (RightCylinder.projection (complex m)).realization
        (faceMap a m n).realization := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  exact RightCylinder.realization_projection_map (faceMap a m n) x

end

end Thomason.Construction.DirectedGlobeComplex

end

end OAI
