import OAI.CategoryTheory.Thomason.Gray.PosetPrismEndpoints
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import OAI.CategoryTheory.Thomason.Transfer.WeakFactorizationRecognition
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesColimit
import Mathlib.Data.Finset.Max
import Mathlib.Order.UpperLower.Basic

namespace OAI

section

/-! # The concrete initial and final ordinal faces -/

namespace Thomason.Construction.SimplexComplex

open CategoryTheory

/-- Inclusion of an initial segment of a finite ordinal. -/
def initialFace {q m : ℕ} (hqm : q ≤ m) : Fin (q + 1) ↪o Fin (m + 1) :=
  Fin.castLEOrderEmb (Nat.succ_le_succ hqm)

/-- Retraction to that initial segment, by clamping above its last vertex. -/
def initialClamp {q m : ℕ} (_hqm : q ≤ m) : Fin (m + 1) →o Fin (q + 1) where
  toFun i := ⟨min i.val q, Nat.lt_succ_of_le (min_le_right _ _)⟩
  monotone' := fun _ _ hij => min_le_min_right q hij

theorem initialClamp_retract {q m : ℕ} (hqm : q ≤ m) :
    (initialClamp hqm).comp (initialFace hqm).toOrderHom = OrderHom.id := by
  apply DFunLike.ext
  intro i
  apply Fin.ext
  exact min_eq_left (Nat.le_of_lt_succ i.isLt)

theorem initialFace_range {q m : ℕ} (hqm : q ≤ m) :
    Set.range (initialFace hqm) = Set.Iic (⟨q, Nat.lt_succ_of_le hqm⟩ : Fin (m + 1)) := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    exact Nat.le_of_lt_succ j.isLt
  · intro hi
    exact ⟨⟨i.val, Nat.lt_succ_of_le hi⟩, rfl⟩

/-- The full strict subcategory on an initial segment is its smaller oriental. -/
noncomputable def initialFaceIso {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)
    {q m : ℕ} (hqm : q ≤ m) :
    h.object q ≅ vertexFullSubcategory h (Set.range (initialFace hqm)) :=
  fullFaceIso a (initialFace hqm) (initialClamp hqm) (initialClamp_retract hqm)
    (by rw [initialFace_range]; exact Set.ordConnected_Iic)

/-- Inclusion of the final segment with q+1 vertices. -/
def finalFace {q m : ℕ} (hqm : q ≤ m) : Fin (q + 1) ↪o Fin (m + 1) :=
  OrderEmbedding.ofStrictMono (fun i => ⟨m - q + i.val, by omega⟩)
    (by intro i j hij; change m - q + i.val < m - q + j.val; omega)

/-- Retraction to a final segment by clamping below its first vertex. -/
def finalClamp {q m : ℕ} (hqm : q ≤ m) : Fin (m + 1) →o Fin (q + 1) where
  toFun i := ⟨i.val - (m - q), by omega⟩
  monotone' := fun _ _ hij => Nat.sub_le_sub_right hij _

theorem finalClamp_retract {q m : ℕ} (hqm : q ≤ m) :
    (finalClamp hqm).comp (finalFace hqm).toOrderHom = OrderHom.id := by
  apply DFunLike.ext
  intro i
  apply Fin.ext
  change m - q + i.val - (m - q) = i.val
  omega

theorem finalFace_range {q m : ℕ} (hqm : q ≤ m) :
    Set.range (finalFace hqm) = Set.Ici (⟨m - q, by omega⟩ : Fin (m + 1)) := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    change m - q ≤ m - q + j.val
    omega
  · intro hi
    change m - q ≤ i.val at hi
    refine ⟨⟨i.val - (m - q), by omega⟩, ?_⟩
    apply Fin.ext
    change m - q + (i.val - (m - q)) = i.val
    omega

/-- The full strict subcategory on a final segment is its smaller oriental. -/
noncomputable def finalFaceIso {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)
    {q m : ℕ} (hqm : q ≤ m) :
    h.object q ≅ vertexFullSubcategory h (Set.range (finalFace hqm)) :=
  fullFaceIso a (finalFace hqm) (finalClamp hqm) (finalClamp_retract hqm)
    (by rw [finalFace_range]; exact Set.ordConnected_Ici)

/-- The full subcategory on no vertices has no cells. -/
instance emptyVertexFullSubcategory (h : NormalizedSimplexIdentities) (m : ℕ) :
    IsEmpty (vertexFullSubcategory h (m := m) ∅) :=
  ⟨fun x => x.property.1⟩

end Thomason.Construction.SimplexComplex

end

section

/-! # Cellwise calculus for labels in the walking arrow -/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

variable {X : StrictOmegaCategory.{0}}

def firstLabel (p : X ⟶ StrictPoset.category (Fin 2)) (x : X) : Fin 2 := (p.toFun x).first
def lastLabel (p : X ⟶ StrictPoset.category (Fin 2)) (x : X) : Fin 2 := (p.toFun x).last

theorem label_ordered (p : X ⟶ StrictPoset.category (Fin 2)) (x : X) :
    firstLabel p x ≤ lastLabel p x := (p.toFun x).ordered

@[simp] theorem firstLabel_face_zero (p : X ⟶ StrictPoset.category (Fin 2))
    (a : Bool) (x : X) : firstLabel p (X.face a 0 x) =
      if a then lastLabel p x else firstLabel p x := by
  exact congrArg StrictPoset.Cell.first (p.map_face a 0 x)

@[simp] theorem lastLabel_face_zero (p : X ⟶ StrictPoset.category (Fin 2))
    (a : Bool) (x : X) : lastLabel p (X.face a 0 x) =
      if a then lastLabel p x else firstLabel p x := by
  exact congrArg StrictPoset.Cell.last (p.map_face a 0 x)

@[simp] theorem firstLabel_face_succ (p : X ⟶ StrictPoset.category (Fin 2))
    (a : Bool) (n : ℕ) (x : X) : firstLabel p (X.face a (n+1) x) = firstLabel p x :=
  congrArg StrictPoset.Cell.first (p.map_face a (n+1) x)

@[simp] theorem lastLabel_face_succ (p : X ⟶ StrictPoset.category (Fin 2))
    (a : Bool) (n : ℕ) (x : X) : lastLabel p (X.face a (n+1) x) = lastLabel p x :=
  congrArg StrictPoset.Cell.last (p.map_face a (n+1) x)

@[simp] theorem firstLabel_comp (p : X ⟶ StrictPoset.category (Fin 2))
    (n : ℕ) (x y : X) (h : X.target n x = X.source n y) :
    firstLabel p (X.comp n x y h) = firstLabel p x := by
  have hm := p.map_comp n x y h
    ((p.map_face true n x).symm.trans ((congrArg p.toFun h).trans (p.map_face false n y)))
  have he := congrArg StrictPoset.Cell.first hm
  cases n <;> exact he

@[simp] theorem lastLabel_comp_zero (p : X ⟶ StrictPoset.category (Fin 2))
    (x y : X) (h : X.target 0 x = X.source 0 y) :
    lastLabel p (X.comp 0 x y h) = lastLabel p y := by
  have he := congrArg StrictPoset.Cell.last (p.map_comp 0 x y h
    ((p.map_face true 0 x).symm.trans ((congrArg p.toFun h).trans (p.map_face false 0 y))))
  exact he

@[simp] theorem lastLabel_comp_succ (p : X ⟶ StrictPoset.category (Fin 2))
    (n : ℕ) (x y : X) (h : X.target (n+1) x = X.source (n+1) y) :
    lastLabel p (X.comp (n+1) x y h) = lastLabel p x := by
  exact congrArg StrictPoset.Cell.last (p.map_comp (n+1) x y h
    ((p.map_face true (n+1) x).symm.trans
      ((congrArg p.toFun h).trans (p.map_face false (n+1) y))))

theorem label_composable_zero (p : X ⟶ StrictPoset.category (Fin 2))
    (x y : X) (h : X.target 0 x = X.source 0 y) : lastLabel p x = firstLabel p y := by
  have he := congrArg (firstLabel p) h
  simpa only [source, target, firstLabel_face_zero, Bool.false_eq_true,
    ite_false, ite_true] using he

theorem labels_composable_succ (p : X ⟶ StrictPoset.category (Fin 2))
    (n : ℕ) (x y : X) (h : X.target (n+1) x = X.source (n+1) y) :
    firstLabel p x = firstLabel p y ∧ lastLabel p x = lastLabel p y := by
  constructor
  · simpa only [source, target, firstLabel_face_succ] using congrArg (firstLabel p) h
  · simpa only [source, target, lastLabel_face_succ] using congrArg (lastLabel p) h

/-- An endpoint-zero cell, as a cell of the actual full fibre. -/
def zeroCell (p : X ⟶ StrictPoset.category (Fin 2)) (x : X) (hl : lastLabel p x = 0) :
    labelFiber p 0 := ⟨x, (fullCell_label_iff p 0 x).mpr (by
      apply StrictPoset.Cell.ext
      · have ho := label_ordered p x
        change firstLabel p x = 0
        omega
      · exact hl)⟩

/-- The source object of a cell whose source has label zero, in the zero fibre. -/
def zeroSource (p : X ⟶ StrictPoset.category (Fin 2)) (x : X) (hf : firstLabel p x = 0) :
    Objects (labelFiber p 0) :=
  ⟨zeroCell p (X.face false 0 x) (by simpa using hf),
    ⟨Subtype.ext (X.face_face_same false false 0 x),
      Subtype.ext (X.face_face_same true false 0 x)⟩⟩

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Initial and final segments, including arbitrary subsets of finite ordinals -/

namespace Thomason.Construction.SimplexComplex

open CategoryTheory

/-- Every nonempty initial segment of a finite ordinal has a last vertex. -/
theorem lowerSet_eq_Iic {m : ℕ} {I : Set (Fin (m + 1))}
    (hI : IsLowerSet I) (hne : I.Nonempty) : ∃ i, I = Set.Iic i := by
  classical
  let S := Finset.univ.filter (fun i => i ∈ I)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i := S.max' hS
  have hi : i ∈ I := (Finset.mem_filter.mp (S.max'_mem hS)).2
  refine ⟨i, Set.ext fun j => ?_⟩
  constructor
  · intro hj
    exact S.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  · intro hj
    exact hI hj hi

/-- Every nonempty final segment of a finite ordinal has a first vertex. -/
theorem upperSet_eq_Ici {m : ℕ} {I : Set (Fin (m + 1))}
    (hI : IsUpperSet I) (hne : I.Nonempty) : ∃ i, I = Set.Ici i := by
  classical
  let S := Finset.univ.filter (fun i => i ∈ I)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i := S.min' hS
  have hi : i ∈ I := (Finset.mem_filter.mp (S.min'_mem hS)).2
  refine ⟨i, Set.ext fun j => ?_⟩
  constructor
  · intro hj
    exact S.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  · intro hj
    exact hI hj hi

/-- Every nonempty initial vertex segment gives the corresponding smaller oriental. -/
theorem initialSegment_oriental {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)
    {m : ℕ} {I : Set (Fin (m + 1))} (hI : IsLowerSet I) (hne : I.Nonempty) :
    ∃ q : Fin (m + 1), Nonempty (h.object q.val ≅ vertexFullSubcategory h I) := by
  obtain ⟨q, rfl⟩ := lowerSet_eq_Iic hI hne
  have hqm : q.val ≤ m := Nat.le_of_lt_succ q.isLt
  have hr : Set.range (initialFace hqm) = Set.Iic q := initialFace_range hqm
  exact ⟨q, ⟨initialFaceIso a hqm ≪≫ eqToIso (congrArg (vertexFullSubcategory h) hr)⟩⟩

/-- Every nonempty final vertex segment gives the corresponding smaller oriental. -/
theorem finalSegment_oriental {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)
    {m : ℕ} {I : Set (Fin (m + 1))} (hI : IsUpperSet I) (hne : I.Nonempty) :
    ∃ q : Fin (m + 1), Nonempty (h.object q.val ≅ vertexFullSubcategory h I) := by
  obtain ⟨i, rfl⟩ := upperSet_eq_Ici hI hne
  have hqm : m - i.val ≤ m := Nat.sub_le _ _
  have hi : (⟨m - (m - i.val), by omega⟩ : Fin (m + 1)) = i := by
    apply Fin.ext
    change m - (m - i.val) = i.val
    omega
  have hr : Set.range (finalFace hqm) = Set.Ici i := by
    simpa only [hi] using finalFace_range hqm
  exact ⟨⟨m - i.val, by omega⟩,
    ⟨finalFaceIso a hqm ≪≫ eqToIso (congrArg (vertexFullSubcategory h) hr)⟩⟩

end Thomason.Construction.SimplexComplex

end

section

/-!
# Homotopies and the actual realization weak equivalences

We derive the weak-equivalence status of simplicial cylinder inclusions
from Mathlib's proved anodyne pushout-product theorem and the explicit
Kan--Quillen WFS input. No homotopy-invariance hypothesis is added.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe u

/-- A one-dimensional horn is its sole vertex. -/
noncomputable def hornOneIso (i j : Fin 2) (hji : j ≠ i) :
    (Δ[0] : SSet.{u}) ≅ Λ[1, i] where
  hom := SSet.horn.ι i j hji
  inv := SSet.stdSimplex.isTerminalObj₀.from _
  hom_inv_id := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  inv_hom_id := by
    apply SSet.horn.hom_ext
    intro k hki
    have hk : k = j := by omega
    subst k
    have hc : SSet.horn.ι i j hji ≫
        (SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.horn.ι i j hji) =
        SSet.horn.ι i j hji := by
      rw [← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
        (SSet.horn.ι i j hji ≫ SSet.stdSimplex.isTerminalObj₀.from _) (𝟙 _), Category.id_comp]
    have he := congrArg SSet.yonedaEquiv hc
    change (SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.horn.ι i j hji).app _
      (SSet.horn.face i j hji) = SSet.horn.face i j hji
    simpa only [SSet.yonedaEquiv_comp, SSet.horn.yonedaEquiv_ι] using he

theorem anodyne_delta_one (j : Fin 2) :
    SSet.anodyneExtensions.{u} (SSet.stdSimplex.δ j) := by
  have hji : j ≠ j.rev := by fin_cases j <;> decide
  rw [← SSet.horn.ι_ι j.rev j hji]
  exact SSet.anodyneExtensions.comp_mem _ _
    (SSet.anodyneExtensions.of_isIso (hornOneIso j.rev j hji).hom)
    (SSet.anodyneExtensions.horn_ι j.rev)

noncomputable def unitZeroIso : (𝟙_ SSet.{u}) ≅ Δ[0] :=
  isTerminalTensorUnit.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀

theorem anodyne_iota_zero (X : SSet.{u}) : SSet.anodyneExtensions (SSet.ι₀ (X := X)) := by
  have h : SSet.ι₀ (X := X) = (ρ_ X).inv ≫
      X ◁ (unitZeroIso.hom ≫ SSet.stdSimplex.δ (1 : Fin 2)) := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.objEquiv.injective
      ext k
      rfl
  rw [h]
  apply SSet.anodyneExtensions.comp_mem
  · exact SSet.anodyneExtensions.of_isIso _
  · exact (SSet.anodyneExtensions.comp_mem _ _
      (SSet.anodyneExtensions.of_isIso unitZeroIso.hom) (anodyne_delta_one 1)).whiskerLeft X

theorem anodyne_iota_one (X : SSet.{u}) : SSet.anodyneExtensions (SSet.ι₁ (X := X)) := by
  have h : SSet.ι₁ (X := X) = (ρ_ X).inv ≫
      X ◁ (unitZeroIso.hom ≫ SSet.stdSimplex.δ (0 : Fin 2)) := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.objEquiv.injective
      ext k
      rfl
  rw [h]
  apply SSet.anodyneExtensions.comp_mem
  · exact SSet.anodyneExtensions.of_isIso _
  · exact (SSet.anodyneExtensions.comp_mem _ _
      (SSet.anodyneExtensions.of_isIso unitZeroIso.hom) (anodyne_delta_one 0)).whiskerLeft X

namespace KanQuillenPublishedInput

variable (kq : KanQuillenPublishedInput.{u})

include kq

/-- The published WFS identifies anodyne extensions with the actual
monomorphisms which are realization weak equivalences. -/
theorem anodyne_eq : SSet.anodyneExtensions.{u} =
    MorphismProperty.monomorphisms SSet.{u} ⊓ realizationWeakEquivalences := by
  have := kq.fibrationFactorization
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  exact MorphismProperty.llp_eq_of_wfs _ SSet.modelCategoryQuillen.J.rlp

theorem anodyne_weakEquivalence {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.anodyneExtensions f) : realizationWeakEquivalences f := by
  rw [kq.anodyne_eq] at hf
  exact hf.2

theorem cylinder_endpoint_zero (X : SSet.{u}) :
    realizationWeakEquivalences (SSet.ι₀ (X := X)) :=
  kq.anodyne_weakEquivalence (anodyne_iota_zero X)

theorem cylinder_endpoint_one (X : SSet.{u}) :
    realizationWeakEquivalences (SSet.ι₁ (X := X)) :=
  kq.anodyne_weakEquivalence (anodyne_iota_one X)

/-- A simplicial homotopy preserves and reflects the geometric-realization
weak-equivalence property. -/
theorem homotopy_weakEquivalence_iff {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) : realizationWeakEquivalences f ↔ realizationWeakEquivalences g := by
  have := kq.twoOutOfThree
  have h₀ := kq.cylinder_endpoint_zero X
  have h₁ := kq.cylinder_endpoint_one X
  constructor
  · intro hf
    have hH : realizationWeakEquivalences H.h := by
      apply realizationWeakEquivalences.of_precomp SSet.ι₀ H.h h₀
      rwa [H.h₀]
    simpa only [H.h₁] using realizationWeakEquivalences.comp_mem _ _ h₁ hH
  · intro hg
    have hH : realizationWeakEquivalences H.h := by
      apply realizationWeakEquivalences.of_precomp SSet.ι₁ H.h h₁
      rwa [H.h₁]
    simpa only [H.h₀] using realizationWeakEquivalences.comp_mem _ _ h₀ hH

end KanQuillenPublishedInput
end Thomason.Construction

end

section

/-! # Relative homotopy extension into a Kan complex

The construction uses the proved anodyne pushout-product theorem. No
realization weak-equivalence or Kan--Quillen model axiom is assumed.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe u

noncomputable section

/-- The zero face of a product is its projection followed by the zero endpoint. -/
@[reassoc]
theorem whisker_zero_face (K : SSet.{u}) :
    K ◁ SSet.stdSimplex.δ (1 : Fin 2) =
      fst K (Δ[0] : SSet.{u}) ≫ SSet.ι₀ := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.objEquiv.injective
    ext k
    change ↑((SimplexCategory.δ (1 : Fin 2)).toOrderHom
      ((SSet.stdSimplex.objEquiv x.2).toOrderHom k)) = (0 : ℕ)
    have he : (SSet.stdSimplex.objEquiv x.2).toOrderHom k = 0 :=
      @Subsingleton.elim (Fin 1) inferInstance _ _
    rw [he]
    rfl

/-- The product with the terminal standard simplex has a chosen section. -/
def zeroFaceSection (K : SSet.{u}) : K ⟶ K ⊗ (Δ[0] : SSet.{u}) :=
  (ρ_ K).inv ≫ K ◁ unitZeroIso.hom

@[reassoc (attr := simp)]
theorem zeroFaceSection_fst (K : SSet.{u}) :
    zeroFaceSection K ≫ fst K (Δ[0] : SSet.{u}) = 𝟙 K := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  rfl

@[reassoc (attr := simp)]
theorem zeroFaceSection_face (K : SSet.{u}) :
    zeroFaceSection K ≫ K ◁ SSet.stdSimplex.δ (1 : Fin 2) = SSet.ι₀ := by
  rw [whisker_zero_face, zeroFaceSection_fst_assoc]

/-- A prescribed simplicial homotopy on any subobject extends into a Kan
complex while keeping the entire initial map fixed. -/
theorem exists_kan_homotopy_extension {A K X : SSet.{u}}
    (i : A ⟶ K) [Mono i] [SSet.KanComplex X]
    (f : K ⟶ X) (h : A ⊗ Δ[1] ⟶ X) (h₀ : SSet.ι₀ ≫ h = i ≫ f) :
    ∃ e : K ⊗ Δ[1] ⟶ X, SSet.ι₀ ≫ e = f ∧ i ▷ Δ[1] ≫ e = h := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet)
    i (SSet.stdSimplex.δ (1 : Fin 2))
  have hc : i ▷ (Δ[0] : SSet.{u}) ≫ fst K (Δ[0] : SSet.{u}) ≫ f =
      A ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ h := by
    rw [whisker_zero_face, Category.assoc, h₀]
    have hp : i ▷ (Δ[0] : SSet.{u}) ≫ fst K (Δ[0] : SSet.{u}) =
        fst A (Δ[0] : SSet.{u}) ≫ i := by
      apply NatTrans.ext
      funext m
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hp, Category.assoc]
  let g : sq.pt ⟶ X := sq.isPushout.desc (fst K (Δ[0] : SSet.{u}) ≫ f) h hc
  have ha : SSet.anodyneExtensions sq.ι :=
    SSet.anodyneExtensions_pushoutObjObjι sq (anodyne_delta_one 1)
  have hl : HasLiftingProperty sq.ι (terminal.from X) :=
    ha _ (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let := hl
  let c : CommSq g sq.ι (terminal.from X) (terminal.from (K ⊗ Δ[1])) :=
    ⟨by simp⟩
  refine ⟨c.lift, ?_, ?_⟩
  · have he : K ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ c.lift =
        fst K (Δ[0] : SSet.{u}) ≫ f := by
      have hi : sq.inl ≫ sq.ι = K ◁ SSet.stdSimplex.δ (1 : Fin 2) := sq.inl_ι
      rw [← hi, Category.assoc, c.fac_left]
      exact sq.isPushout.inl_desc _ _ _
    have hz := congrArg (fun k => zeroFaceSection K ≫ k) he
    simpa only [← Category.assoc, zeroFaceSection_face, zeroFaceSection_fst,
      Category.id_comp] using hz
  · have hi : sq.inr ≫ sq.ι = i ▷ Δ[1] := sq.inr_ι
    rw [← hi, Category.assoc, c.fac_left]
    exact sq.isPushout.inr_desc _ _ _

end

end Thomason.Construction

end

section

/-! # Maps from the simplicial interval boundary are determined by its ends -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

universe u

theorem interval_boundary_constant {m : SimplexCategoryᵒᵖ}
    (z : (SSet.boundary 1 : SSet.{u}).obj m) (i : Fin (m.unop.len+1)) :
    (SSet.stdSimplex.objEquiv z.val).toOrderHom i =
      (SSet.stdSimplex.objEquiv z.val).toOrderHom 0 := by
  by_contra hi
  have hbound (j : Fin (m.unop.len+1)) :
      ((SSet.stdSimplex.objEquiv z.val).toOrderHom j).val < 2 :=
    ((SSet.stdSimplex.objEquiv z.val).toOrderHom j).isLt
  have hi_bound := hbound i
  apply z.property
  intro j
  have hjbound : j.val < 2 := j.isLt
  by_cases h : j = (SSet.stdSimplex.objEquiv z.val).toOrderHom 0
  · exact ⟨0, h.symm⟩
  · have hj : (SSet.stdSimplex.objEquiv z.val).toOrderHom i = j := by omega
    exact ⟨i, hj⟩

/-- Restriction to the two endpoints detects equality even with an arbitrary
simplicial parameter object. -/
theorem interval_boundary_tensor_hom_ext {K X : SSet.{u}}
    (f g : K ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ X)
    (h₀ : K ◁ SSet.boundary.ι (1 : Fin 2) ≫ f =
      K ◁ SSet.boundary.ι (1 : Fin 2) ≫ g)
    (h₁ : K ◁ SSet.boundary.ι (0 : Fin 2) ≫ f =
      K ◁ SSet.boundary.ι (0 : Fin 2) ≫ g) : f = g := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  rintro ⟨x, z⟩
  let w : (Δ[0] : SSet.{u}).obj m := SSet.stdSimplex.objMk (OrderHom.const _ 0)
  have hz (i : Fin 2)
      (hi : (SSet.stdSimplex.objEquiv z.val).toOrderHom 0 = i.rev) :
      (SSet.boundary.ι i).app m w = z := by
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    change (SimplexCategory.δ i).toOrderHom 0 = _
    rw [interval_boundary_constant z j, hi]
    fin_cases i <;> rfl
  let he : Fin 2 := (SSet.stdSimplex.objEquiv z.val).toOrderHom 0
  have he_bound : he.val < 2 := he.isLt
  have hcases : he = 0 ∨ he = 1 := by omega
  rcases hcases with h | h
  · have hz' := hz 1 (by simpa using h)
    have hh := congrArg (fun e => e.app m (x, w)) h₀
    change f.app m (x, (SSet.boundary.ι 1).app m w) =
      g.app m (x, (SSet.boundary.ι 1).app m w) at hh
    rwa [hz'] at hh
  · have hz' := hz 0 (by simpa using h)
    have hh := congrArg (fun e => e.app m (x, w)) h₁
    change f.app m (x, (SSet.boundary.ι 0).app m w) =
      g.app m (x, (SSet.boundary.ι 0).app m w) at hh
    rwa [hz'] at hh

end Thomason.Construction

end

section

/-! # The map from the interval boundary with two prescribed vertices -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

universe u

noncomputable section

def intervalBoundaryMap {X : SSet.{u}} (x₀ x₁ : X _⦋0⦌) :
    (SSet.boundary 1 : SSet.{u}) ⟶ X where
  app m := ↾fun z => if (SSet.stdSimplex.objEquiv z.val).toOrderHom 0 = 0 then
    (SSet.const (X := (SSet.boundary 1 : SSet.{u})) x₀).app m z
    else (SSet.const (X := (SSet.boundary 1 : SSet.{u})) x₁).app m z
  naturality m n f := by
    apply ConcreteCategory.hom_ext
    intro z
    have ht : (SSet.stdSimplex.objEquiv
        (((SSet.boundary 1 : SSet.{u}).map f) z).val).toOrderHom 0 =
        (SSet.stdSimplex.objEquiv z.val).toOrderHom 0 :=
      interval_boundary_constant z (f.unop.toOrderHom 0)
    change (if (SSet.stdSimplex.objEquiv
        (((SSet.boundary 1 : SSet.{u}).map f) z).val).toOrderHom 0 = 0 then
      (SSet.const x₀).app n _ else (SSet.const x₁).app n _) =
      X.map f (if (SSet.stdSimplex.objEquiv z.val).toOrderHom 0 = 0 then
        (SSet.const x₀).app m z else (SSet.const x₁).app m z)
    rw [ht]
    split_ifs
    · change X.map (n.unop.const _ 0).op x₀ = X.map f (X.map (m.unop.const _ 0).op x₀)
      exact NatTrans.naturality_apply (SSet.const (X := (SSet.boundary 1 : SSet.{u})) x₀) f z
    · change X.map (n.unop.const _ 0).op x₁ = X.map f (X.map (m.unop.const _ 0).op x₁)
      exact NatTrans.naturality_apply (SSet.const (X := (SSet.boundary 1 : SSet.{u})) x₁) f z

theorem intervalBoundaryMap_zero {X : SSet.{u}} (x₀ x₁ : X _⦋0⦌) :
    SSet.boundary.ι (1 : Fin 2) ≫ intervalBoundaryMap x₀ x₁ = SSet.const x₀ := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro z
  have hz : (SSet.stdSimplex.objEquiv z).toOrderHom 0 = 0 :=
    @Subsingleton.elim (Fin 1) inferInstance _ _
  change (if (SimplexCategory.δ (1 : Fin 2)).toOrderHom
      ((SSet.stdSimplex.objEquiv z).toOrderHom 0) = 0 then
        X.map (m.unop.const _ 0).op x₀ else X.map (m.unop.const _ 0).op x₁) = _
  rw [hz]
  rfl

theorem intervalBoundaryMap_one {X : SSet.{u}} (x₀ x₁ : X _⦋0⦌) :
    SSet.boundary.ι (0 : Fin 2) ≫ intervalBoundaryMap x₀ x₁ = SSet.const x₁ := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro z
  have hz : (SSet.stdSimplex.objEquiv z).toOrderHom 0 = 0 :=
    @Subsingleton.elim (Fin 1) inferInstance _ _
  change (if (SimplexCategory.δ (0 : Fin 2)).toOrderHom
      ((SSet.stdSimplex.objEquiv z).toOrderHom 0) = 0 then
        X.map (m.unop.const _ 0).op x₀ else X.map (m.unop.const _ 0).op x₁) = _
  rw [hz]
  rfl

theorem intervalBoundaryMap_postcomp {X Y : SSet.{u}} (x₀ x₁ : X _⦋0⦌) (p : X ⟶ Y) :
    intervalBoundaryMap x₀ x₁ ≫ p = intervalBoundaryMap (p.app _ x₀) (p.app _ x₁) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro z
  change p.app m (if (SSet.stdSimplex.objEquiv z.val).toOrderHom 0 = 0 then _ else _) =
    (if (SSet.stdSimplex.objEquiv z.val).toOrderHom 0 = 0 then _ else _)
  split_ifs
  · exact NatTrans.naturality_apply p (m.unop.const _ 0).op x₀
  · exact NatTrans.naturality_apply p (m.unop.const _ 0).op x₁

end

end Thomason.Construction

end

section

/-! # Monotone homotopies and the actual Kan–Quillen weak equivalences

A pointwise inequality between monotone maps gives an explicit simplicial
homotopy of their ordinary nerves. This will compare the finite-poset
adjunction unit on contractible posets with its value on a point.
-/

namespace Thomason.Construction

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

theorem orderNerveMap_id (P : Type) [PartialOrder P] :
    nerveMap (OrderHom.id : P →o P).monotone.functor = 𝟙 (nerve P) := by
  ext s
  rfl

theorem orderNerveMap_comp {P Q R : Type} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (f : P →o Q) (g : Q →o R) :
    nerveMap (g.comp f).monotone.functor =
      nerveMap f.monotone.functor ≫ nerveMap g.monotone.functor := by
  ext s
  rfl

/-- Interpolate between monotone maps along a monotone binary vertex label. -/
def orderInterpolate {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f g : P →o Q) (hfg : ∀ x, f x ≤ g x) {m : ℕ}
    (s : Fin (m + 1) →o P) (θ : Fin (m + 1) →o Fin 2) : Fin (m + 1) →o Q where
  toFun i := if θ i = 0 then f (s i) else g (s i)
  monotone' := by
    intro i j hij
    have hs := s.monotone hij
    have ht := θ.monotone hij
    dsimp
    split_ifs with hi hj
    · exact f.monotone hs
    · exact (f.monotone hs).trans (hfg _)
    · have hi' : θ i = 1 := by omega
      omega
    · exact g.monotone hs

/-- Every pointwise inequality induces a homotopy of the actual ordinary nerves. -/
noncomputable def orderNerveHomotopy {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f g : P →o Q) (hfg : ∀ x, f x ≤ g x) :
    SSet.Homotopy (nerveMap f.monotone.functor) (nerveMap g.monotone.functor) where
  h :=
    { app m := ↾fun x => NormalizedSimplexIdentities.orderSimplex
        (orderInterpolate f g hfg (NormalizedSimplexIdentities.simplexOrder x.1)
          (SSet.stdSimplex.objEquiv x.2).toOrderHom)
      naturality m n a := by
        ext x
        rfl }
  h₀ := by
    ext x
    rfl
  h₁ := by
    ext x
    rfl
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- Pointwise comparable monotone maps simultaneously induce realization
weak equivalences, using only the actual Kan–Quillen WFS input. -/
theorem orderNerve_weakEquivalence_iff (kq : KanQuillenPublishedInput.{0})
    {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f g : P →o Q) (hfg : ∀ x, f x ≤ g x) :
    realizationWeakEquivalences (nerveMap f.monotone.functor) ↔
      realizationWeakEquivalences (nerveMap g.monotone.functor) :=
  kq.homotopy_weakEquivalence_iff (orderNerveHomotopy f g hfg)

end Thomason.Construction

end

section

/-! # A canonical subdivision map into the nerve of finite chains

Only the forward map is needed for the subdivided-horn retraction. Its
construction descends the image-of-a-finite-chain maps on all simplices.
-/

namespace Thomason.Construction.NerveSubdivisionMap

open CategoryTheory CategoryTheory.Limits PartialOrder

noncomputable section

def vertices {P : Type} [PartialOrder P] {n : SimplexCategory}
    (f : SSet.stdSimplex.obj n ⟶ nerve P) : ULift.{0} (Fin (n.len+1)) →o P where
  toFun v := (SSet.yonedaEquiv f).obj v.down
  monotone' _ _ h := leOfHom ((SSet.yonedaEquiv f).map (homOfLE h))

def ordinalMap {m n : SimplexCategory} (a : m ⟶ n) :
    ULift.{0} (Fin (m.len+1)) →o ULift.{0} (Fin (n.len+1)) where
  toFun v := ULift.up (a.toOrderHom v.down)
  monotone' _ _ h := a.toOrderHom.monotone h

theorem vertices_comp {P : Type} [PartialOrder P] {m n : SimplexCategory}
    (a : m ⟶ n) (f : SSet.stdSimplex.obj n ⟶ nerve P) :
    vertices (SSet.stdSimplex.map a ≫ f) = (vertices f).comp (ordinalMap a) := by
  ext v
  change (SSet.yonedaEquiv (SSet.stdSimplex.map a ≫ f)).obj v.down = _
  rw [← SSet.yonedaEquiv_naturality]
  rfl

theorem vertices_postcomp {P Q : Type} [PartialOrder P] [PartialOrder Q]
    {n : SimplexCategory} (f : SSet.stdSimplex.obj n ⟶ nerve P) (g : P →o Q) :
    vertices (f ≫ nerveMap g.monotone.functor) = g.comp (vertices f) := by
  ext v
  change (SSet.yonedaEquiv (f ≫ nerveMap g.monotone.functor)).obj v.down = _
  rw [SSet.yonedaEquiv_comp]
  rfl

theorem chains_comp {P Q R : Type} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (f : P →o Q) (g : Q →o R) :
    NonemptyFiniteChains.orderHomMap (g.comp f) =
      (NonemptyFiniteChains.orderHomMap g).comp (NonemptyFiniteChains.orderHomMap f) := by
  ext C x
  simp [NonemptyFiniteChains.orderHomMap, NonemptyFiniteChains.map,
    Finset.image_image]

def chainNerveMap {P Q : Type} [PartialOrder P] [PartialOrder Q] (g : P →o Q) :
    nerve (NonemptyFiniteChains P) ⟶ nerve (NonemptyFiniteChains Q) :=
  nerveMap (NonemptyFiniteChains.orderHomMap g).monotone.functor

def chainsOfVertices {P : Type} [PartialOrder P] (n : SimplexCategory)
    (v : ULift.{0} (Fin (n.len+1)) →o P) :
    SimplexCategory.sd.obj n ⟶ nerve (NonemptyFiniteChains P) :=
  nerveMap (NonemptyFiniteChains.orderHomMap v).monotone.functor

theorem chainsOfVertices_comp {P : Type} [PartialOrder P] {m n : SimplexCategory}
    (a : m ⟶ n) (v : ULift.{0} (Fin (n.len+1)) →o P) :
    SimplexCategory.sd.map a ≫ chainsOfVertices n v =
      chainsOfVertices m (v.comp (ordinalMap a)) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  apply NonemptyFiniteChains.ext
  ext x
  change x ∈ (((s.obj i).map (ordinalMap a)).map v).finset ↔
    x ∈ ((s.obj i).map (v.comp (ordinalMap a))).finset
  simp [NonemptyFiniteChains.map, Finset.image_image, OrderHom.comp, ordinalMap]
  rfl

theorem chainsOfVertices_postcomp {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (n : SimplexCategory) (v : ULift.{0} (Fin (n.len+1)) →o P) (g : P →o Q) :
    chainsOfVertices n v ≫ chainNerveMap g = chainsOfVertices n (g.comp v) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  apply NonemptyFiniteChains.ext
  ext x
  change x ∈ (((s.obj i).map v).map g).finset ↔
    x ∈ ((s.obj i).map (g.comp v)).finset
  simp [NonemptyFiniteChains.map, Finset.image_image, OrderHom.comp]
  rfl

def piece {P : Type} [PartialOrder P] {n : SimplexCategory}
    (f : SSet.stdSimplex.obj n ⟶ nerve P) :
    SSet.sd.obj (SSet.stdSimplex.obj n) ⟶ nerve (NonemptyFiniteChains P) :=
  SSet.stdSimplex.sdIso.hom.app n ≫ chainsOfVertices n (vertices f)

theorem piece_naturality {P : Type} [PartialOrder P] {m n : SimplexCategory}
    (a : m ⟶ n) (f : SSet.stdSimplex.obj n ⟶ nerve P) :
    SSet.sd.map (SSet.stdSimplex.map a) ≫ piece f = piece (SSet.stdSimplex.map a ≫ f) := by
  calc
    _ = (SSet.sd.map (SSet.stdSimplex.map a) ≫ SSet.stdSimplex.sdIso.hom.app n) ≫
        chainsOfVertices n (vertices f) := (Category.assoc _ _ _).symm
    _ = (SSet.stdSimplex.sdIso.hom.app m ≫ SimplexCategory.sd.map a) ≫
        chainsOfVertices n (vertices f) :=
      congrArg (fun q => q ≫ chainsOfVertices n (vertices f))
        (SSet.stdSimplex.sdIso.hom.naturality a)
    _ = SSet.stdSimplex.sdIso.hom.app m ≫ chainsOfVertices m ((vertices f).comp (ordinalMap a)) := by
      rw [Category.assoc, chainsOfVertices_comp]
    _ = _ := congrArg (fun v => SSet.stdSimplex.sdIso.hom.app m ≫ chainsOfVertices m v)
      (vertices_comp a f).symm

theorem piece_postcomp {P Q : Type} [PartialOrder P] [PartialOrder Q]
    {n : SimplexCategory} (f : SSet.stdSimplex.obj n ⟶ nerve P) (g : P →o Q) :
    piece (f ≫ nerveMap g.monotone.functor) = piece f ≫ chainNerveMap g := by
  calc
    _ = SSet.stdSimplex.sdIso.hom.app n ≫ chainsOfVertices n (g.comp (vertices f)) :=
      congrArg (fun v => SSet.stdSimplex.sdIso.hom.app n ≫ chainsOfVertices n v)
        (vertices_postcomp f g)
    _ = _ := by rw [← chainsOfVertices_postcomp, ← Category.assoc]; rfl

def targetCocone (P : Type) [PartialOrder P] :
    Cocone (SimplicialHomotopyDescent.diagram SSet.sd (nerve P)) where
  pt := nerve (NonemptyFiniteChains P)
  ι := {
    app j := piece j.hom
    naturality i j a := by
      change SSet.sd.map (SSet.stdSimplex.map a.left) ≫ piece j.hom = piece i.hom ≫ 𝟙 _
      rw [piece_naturality, CostructuredArrow.w a, Category.comp_id] }

def map (P : Type) [PartialOrder P] : SSet.sd.obj (nerve P) ⟶ nerve (NonemptyFiniteChains P) :=
  (SimplicialHomotopyDescent.isColimit SSet.sd (nerve P)).desc (targetCocone P)

@[reassoc]
theorem map_fac {P : Type} [PartialOrder P] {n : SimplexCategory}
    (f : SSet.stdSimplex.obj n ⟶ nerve P) : SSet.sd.map f ≫ map P = piece f :=
  (SimplicialHomotopyDescent.isColimit SSet.sd (nerve P)).fac
    (targetCocone P) (CostructuredArrow.mk f)

theorem map_naturality {P Q : Type} [PartialOrder P] [PartialOrder Q] (g : P →o Q) :
    SSet.sd.map (nerveMap g.monotone.functor) ≫ map Q =
      map P ≫ nerveMap (NonemptyFiniteChains.orderHomMap g).monotone.functor := by
  apply (SimplicialHomotopyDescent.isColimit SSet.sd (nerve P)).hom_ext
  intro j
  change SSet.sd.map j.hom ≫ _ = SSet.sd.map j.hom ≫ _
  rw [← Category.assoc, ← SSet.sd.map_comp, map_fac, map_fac_assoc]
  exact piece_postcomp j.hom g

/-- On an ordinal nerve this map is the actual standard subdivision
isomorphism, expressed through the standard-simplex nerve isomorphism. -/
theorem map_standard (n : SimplexCategory) :
    SSet.sd.map (simplexNerveIso.hom.app n) ≫
        map (ULift.{0} (Fin (n.len+1))) = SSet.stdSimplex.sdIso.hom.app n := by
  let f : SSet.stdSimplex.obj n ⟶ nerve (ULift.{0} (Fin (n.len+1))) :=
    simplexNerveIso.hom.app n
  have hv : vertices f = OrderHom.id := by
    ext v
    rfl
  have hi : chainsOfVertices n (OrderHom.id : ULift.{0} (Fin (n.len+1)) →o _) =
      𝟙 (SimplexCategory.sd.obj n) := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    apply NonemptyFiniteChains.ext
    ext x
    change x ∈ ((s.obj i).map (OrderHom.id : ULift.{0} (Fin (n.len+1)) →o _)).finset ↔
      x ∈ (s.obj i).finset
    constructor
    · intro hx
      obtain ⟨y, hy, he⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp hx
      exact he ▸ hy
    · intro hx
      exact (NonemptyFiniteChains.mem_map_iff _ _ _).mpr ⟨x, hx, rfl⟩
  calc
    _ = piece f := map_fac f
    _ = SSet.stdSimplex.sdIso.hom.app n ≫ chainsOfVertices n OrderHom.id :=
      congrArg (fun v => SSet.stdSimplex.sdIso.hom.app n ≫ chainsOfVertices n v) hv
    _ = _ := by rw [hi]; exact Category.comp_id _

end

end Thomason.Construction.NerveSubdivisionMap

end

section

/-! # Exact subcomplexes carried by lower sets of nondegenerate faces

This records the finite carrier bookkeeping for the face-poset map.
For lower sets, unions and intersections agree with the corresponding
operations on actual simplicial subcomplexes.
-/

namespace Thomason.Construction.NonsingularLastVertex

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

variable {X : SSet.{0}}

def faceUnion (S : Set X.N) : X.Subcomplex := ⨆ s : S, s.val.subcomplex

theorem nondegenerate_mem_faceUnion_iff (S : Set X.N) (s : X.N) :
    s.simplex ∈ (faceUnion S).obj _ ↔ ∃ t ∈ S, s ≤ t := by
  change (s.simplex ∈ (⨆ t : S, t.val.subcomplex).obj _) ↔ _
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.val, t.property, (SSet.Subcomplex.ofSimplex_le_iff _ _).mpr ht⟩
  · rintro ⟨t, ht, hst⟩
    exact ⟨⟨t, ht⟩, (SSet.Subcomplex.ofSimplex_le_iff _ _).mp hst⟩

theorem nondegenerate_mem_faceUnion_iff_of_lower (S : Set X.N) (hS : IsLowerSet S)
    (s : X.N) : s.simplex ∈ (faceUnion S).obj _ ↔ s ∈ S := by
  rw [nondegenerate_mem_faceUnion_iff]
  exact ⟨fun ⟨_, ht, hst⟩ => hS hst ht, fun hs => ⟨s, hs, le_rfl⟩⟩

theorem faceUnion_mono : Monotone (faceUnion (X := X)) := by
  intro S T hST
  apply iSup_le
  intro s
  exact le_iSup_of_le ⟨s.val, hST s.property⟩ le_rfl

theorem faceUnion_union (S T : Set X.N) :
    faceUnion (S ∪ T) = faceUnion S ⊔ faceUnion T := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨s, hs | hs⟩
    · exact le_sup_of_le_left (le_iSup_of_le ⟨s, hs⟩ le_rfl)
    · exact le_sup_of_le_right (le_iSup_of_le ⟨s, hs⟩ le_rfl)
  · exact sup_le (faceUnion_mono Set.subset_union_left)
      (faceUnion_mono Set.subset_union_right)

theorem faceUnion_inter (S T : Set X.N) (hS : IsLowerSet S) (hT : IsLowerSet T) :
    faceUnion (S ∩ T) = faceUnion S ⊓ faceUnion T := by
  apply le_antisymm
  · exact le_inf (faceUnion_mono Set.inter_subset_left)
      (faceUnion_mono Set.inter_subset_right)
  · rw [SSet.N.subcomplex_le_iff]
    intro s hs
    apply (SSet.Subcomplex.ofSimplex_le_iff _ _).mpr
    rw [nondegenerate_mem_faceUnion_iff_of_lower _ (hS.inter hT)]
    have hh := (SSet.Subcomplex.ofSimplex_le_iff _ _).mp hs
    exact ⟨(nondegenerate_mem_faceUnion_iff_of_lower S hS s).mp hh.1,
      (nondegenerate_mem_faceUnion_iff_of_lower T hT s).mp hh.2⟩

theorem faceUnion_univ : faceUnion (Set.univ : Set X.N) = ⊤ := by
  apply top_unique
  rw [SSet.N.subcomplex_le_iff]
  intro s _
  exact le_iSup_of_le ⟨s, Set.mem_univ _⟩ le_rfl

variable [X.Nonsingular]

def faceInclusion (S : Set X.N) : S →o X.N :=
  ⟨Subtype.val, fun _ _ h => h⟩

theorem restrictedMap_range_le (S : Set X.N) :
    SSet.Subcomplex.range (nerveMap (faceInclusion S).monotone.functor ≫ map X) ≤
      faceUnion S := by
  intro d y hy
  obtain ⟨s, rfl⟩ := hy
  let t := (nerveMap (faceInclusion S).monotone.functor).app d s
  apply (SSet.Subcomplex.ofSimplex_le_iff _ _).mp
  apply le_trans (simplex_carrier t)
  exact le_iSup_of_le (s.obj (Fin.last d.unop.len)) le_rfl

def restrictedMap (S : Set X.N) : nerve S ⟶ (faceUnion S).toSSet :=
  SSet.Subcomplex.lift (nerveMap (faceInclusion S).monotone.functor ≫ map X)
    (restrictedMap_range_le S)

@[reassoc (attr := simp)]
theorem restrictedMap_ι (S : Set X.N) : restrictedMap S ≫ (faceUnion S).ι =
    nerveMap (faceInclusion S).monotone.functor ≫ map X := rfl

def faceSubset {S T : Set X.N} (h : S ⊆ T) : S →o T :=
  ⟨fun s => ⟨s.val, h s.property⟩, fun _ _ hs => hs⟩

@[reassoc]
theorem restrictedMap_naturality {S T : Set X.N} (h : S ⊆ T) :
    nerveMap (faceSubset h).monotone.functor ≫ restrictedMap T =
      restrictedMap S ≫ SSet.Subcomplex.homOfLE (faceUnion_mono h) := by
  apply (cancel_mono (faceUnion T).ι).mp
  simp only [Category.assoc, restrictedMap_ι, SSet.Subcomplex.homOfLE_ι]
  rw [← Category.assoc, ← orderNerveMap_comp]
  rfl

end

end Thomason.Construction.NonsingularLastVertex

end

end OAI
