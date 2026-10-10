import Mathlib
import OAI.CategoryTheory.Thomason.SquareClassification

namespace OAI

/-! Gray Generators. -/

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayTwo
open DirectedComplex DirectedComplex.Table GlobeComplex

instance : DecidableEq Coordinates := fun x y =>
  decidable_of_iff (x.vertex = y.vertex ∧ x.edge = y.edge ∧
    x.face = y.face ∧ x.volume = y.volume) Coordinates.ext_iff.symm

lemma code_injective : Function.Injective code := by decide

def cell (i : Fin 23) : Table K.{u} := (code i).table (code_valid i)

@[simp] lemma coordinates_cell (i : Fin 23) : coordinates (cell.{u} i) = code i :=
  Coordinates.coordinates_table _ _

lemma cell_injective : Function.Injective cell.{u} := by
  intro i j h
  exact code_injective (by simpa using congrArg coordinates h)

lemma cell_surjective : Function.Surjective cell.{u} := by
  intro t
  obtain ⟨i, hi⟩ := is_code (coordinates t) (coordinates_valid t)
  refine ⟨i, coordinates_injective ?_⟩
  exact (coordinates_cell i).trans hi.symm

def cellEquiv : Fin 23 ≃ Table K.{u} :=
  Equiv.ofBijective cell ⟨cell_injective, cell_surjective⟩

def faceIndex (k : ℕ) (b : Bool) (i : Fin 23) : Fin 23 :=
  match k with
  | 0 => if b then ![0, 16, 16, 16, 18, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 16, 22, 18, 22, 22, 22, 22] i
      else ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 16, 18, 18, 18, 18, 22] i
  | 1 => if b then ![0, 1, 1, 3, 4, 5, 13, 5, 8, 13, 13, 13, 15, 13, 13, 15, 16, 17, 18, 19, 19, 21, 22] i
      else ![0, 1, 3, 3, 4, 5, 5, 8, 8, 8, 8, 8, 8, 13, 15, 15, 16, 17, 18, 19, 21, 21, 22] i
  | 2 => if b then ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] i
      else ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] i
  | _ + 3 => i

lemma faceIndex_three_add (k : ℕ) (b : Bool) (i : Fin 23) :
    faceIndex (k + 3) b i = i := rfl

lemma truncate_cell (k : ℕ) (b : Bool) (i : Fin 23) :
    truncate k b (cell.{u} i) = cell (faceIndex k b i) := by
  rcases k with _ | _ | _ | k
  · apply coordinates_injective
    revert i b
    decide
  · apply coordinates_injective
    revert i b
    decide
  · apply coordinates_injective
    revert i b
    decide
  · rw [faceIndex_three_add]
    have h := K.nu.source_fixed_upwards (show 3 ≤ k+3 by omega) (bounded (cell i))
    cases b
    · exact h
    · exact K.nu.target_eq_self_of_source_eq_self h

lemma cell_composable_iff (k : ℕ) (i j : Fin 23) :
    truncate k true (cell.{u} i) = truncate k false (cell j) ↔
      faceIndex k true i = faceIndex k false j := by
  rw [truncate_cell, truncate_cell, cell_injective.eq_iff]

end Thomason.GrayTwo

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.OmegaCategory

lemma comp_of_right_source_fixed (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y) (hy : C.source k y = y) :
    C.comp k x y h = x := by
  have hy' : y = C.target k x := (h.trans hy).symm
  subst y
  exact C.unit_right k x h

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayTwo
open DirectedComplex DirectedComplex.Table GlobeComplex

def composite (e : Fin 8) : ℕ × Fin 23 × Fin 23 × Fin 23 :=
  ![(0, 1, 17, 13), (0, 2, 17, 14), (0, 3, 17, 15),
    (0, 4, 19, 5), (0, 4, 20, 7), (0, 4, 21, 8),
    (1, 7, 6, 9), (1, 12, 14, 11)] e

lemma composite_match (e : Fin 8) :
    faceIndex (composite e).1 true (composite e).2.1 =
      faceIndex (composite e).1 false (composite e).2.2.1 := by
  revert e
  decide

lemma composite_eq (e : Fin 8) :
    K.nu.comp (composite e).1 (cell.{u} (composite e).2.1)
      (cell (composite e).2.2.1) ((cell_composable_iff _ _ _).2 (composite_match e)) =
      cell (composite e).2.2.2 := by
  apply coordinates_injective
  revert e
  decide

lemma composable_cases (k : ℕ) (i j : Fin 23)
    (h : faceIndex k true i = faceIndex k false j) :
    faceIndex k false i = i ∨ faceIndex k false j = j ∨
      ∃ e : Fin 8, (composite e).1 = k ∧ (composite e).2.1 = i ∧
        (composite e).2.2.1 = j := by
  rcases k with _ | _ | _ | k
  · revert i j
    decide
  · revert i j
    decide
  · revert i j
    decide
  · exact Or.inl rfl

structure Diagram (X : OmegaCategory.{v}) where
  obj : Fin 23 → X.Cell
  faces : ∀ k b i, X.face k b (obj i) = obj (faceIndex k b i)
  composites : ∀ e : Fin 8,
    X.comp (composite e).1 (obj (composite e).2.1) (obj (composite e).2.2.1)
      (by
        change X.face (composite e).1 true _ = X.face (composite e).1 false _
        rw [faces, faces, composite_match]) = obj (composite e).2.2.2

namespace Diagram
variable {X : OmegaCategory.{v}} (D : Diagram X)

lemma source_obj (k : ℕ) (i : Fin 23) : X.source k (D.obj i) = D.obj (faceIndex k false i) :=
  D.faces k false i
lemma target_obj (k : ℕ) (i : Fin 23) : X.target k (D.obj i) = D.obj (faceIndex k true i) :=
  D.faces k true i

def evaluate (t : Table K.{u}) : X.Cell := D.obj (cellEquiv.symm t)

@[simp] lemma evaluate_cell (i : Fin 23) : D.evaluate (cell.{u} i) = D.obj i :=
  congrArg D.obj (cellEquiv.symm_apply_apply i)

lemma evaluate_comp (k : ℕ) (i j : Fin 23)
    (h : K.nu.target k (cell.{u} i) = K.nu.source k (cell j))
    (h' : X.target k (D.obj i) = X.source k (D.obj j)) :
    D.evaluate (K.nu.comp k (cell i) (cell j) h) = X.comp k (D.obj i) (D.obj j) h' := by
  rcases composable_cases k i j ((cell_composable_iff _ _ _).1 h) with hl | hr | ⟨e, he⟩
  · have hl' : K.nu.source k (cell.{u} i) = cell i := by
      change truncate k false (cell i) = cell i
      rw [truncate_cell, hl]
    rw [K.nu.comp_of_left_source_fixed k _ _ h hl', evaluate_cell,
      X.comp_of_left_source_fixed k _ _ h' (by rw [D.source_obj, hl])]
  · have hr' : K.nu.source k (cell.{u} j) = cell j := by
      change truncate k false (cell j) = cell j
      rw [truncate_cell, hr]
    rw [K.nu.comp_of_right_source_fixed k _ _ h hr', evaluate_cell,
      X.comp_of_right_source_fixed k _ _ h' (by rw [D.source_obj, hr])]
  · obtain ⟨rfl, rfl, rfl⟩ := he
    rw [composite_eq, evaluate_cell]
    exact (D.composites e).symm

def lift : OmegaCategory.Functor K.{u}.nu X where
  map := D.evaluate
  map_source k t := by
    obtain ⟨i, rfl⟩ := cell_surjective t
    change D.evaluate (truncate k false (cell i)) = X.source k (D.evaluate (cell i))
    rw [truncate_cell, evaluate_cell, evaluate_cell, D.source_obj]
  map_target k t := by
    obtain ⟨i, rfl⟩ := cell_surjective t
    change D.evaluate (truncate k true (cell i)) = X.target k (D.evaluate (cell i))
    rw [truncate_cell, evaluate_cell, evaluate_cell, D.target_obj]
  map_comp k s t h h' := by
    obtain ⟨i, rfl⟩ := cell_surjective s
    obtain ⟨j, rfl⟩ := cell_surjective t
    have h'' : X.target k (D.obj i) = X.source k (D.obj j) := by
      simpa only [evaluate_cell] using h'
    simpa only [evaluate_cell] using D.evaluate_comp k i j h h''

@[simp] lemma lift_cell (i : Fin 23) : D.lift.map (cell.{u} i) = D.obj i :=
  D.evaluate_cell i

end Diagram

lemma functor_ext {X : OmegaCategory.{v}} (F G : OmegaCategory.Functor K.{u}.nu X)
    (h : ∀ i, F.map (cell i) = G.map (cell i)) : F = G := by
  apply OmegaCategory.Functor.ext
  funext t
  obtain ⟨i, rfl⟩ := cell_surjective t
  exact h i

def diagramOfFunctor {X : OmegaCategory.{v}} (F : OmegaCategory.Functor K.{u}.nu X) : Diagram X where
  obj i := F.map (cell i)
  faces k b i := by
    erw [← F.map_face]
    have h : K.nu.face k b (cell i) = cell (faceIndex k b i) := by
      cases b <;> exact truncate_cell k _ i
    rw [h]
  composites e := by
    rw [← F.map_comp _ _ _ ((cell_composable_iff _ _ _).2 (composite_match e)), composite_eq]

@[simp] lemma diagramOfFunctor_lift {X : OmegaCategory.{v}} (F : OmegaCategory.Functor K.{u}.nu X) :
    (diagramOfFunctor F).lift = F := by
  apply functor_ext
  intro i
  exact Diagram.lift_cell _ i

end Thomason.GrayTwo

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

abbrev join (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell) :=
  CellTerm.composeOrLeft C k x y

lemma join_eq (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y) : C.join k x y = C.comp k x y h := by
  simp only [join, CellTerm.composeOrLeft, dite_eq_left h]

lemma join_source_le (C : OmegaCategory.{u}) (i k : ℕ) (x y : C.Cell)
    (hik : i ≤ k) (h : C.target k x = C.source k y) :
    C.source i (C.join k x y) = C.source i x := by
  rw [C.join_eq k x y h, C.source_comp_le i k hik]
lemma join_target_le (C : OmegaCategory.{u}) (i k : ℕ) (x y : C.Cell)
    (hik : i ≤ k) (h : C.target k x = C.source k y) :
    C.target i (C.join k x y) = C.target i y := by
  rw [C.join_eq k x y h, C.target_comp_le i k hik]
lemma join_source_gt (C : OmegaCategory.{u}) (i k : ℕ) (x y : C.Cell)
    (hki : k < i) (h : C.target k x = C.source k y) :
    C.source i (C.join k x y) = C.join k (C.source i x) (C.source i y) := by
  rw [C.join_eq k x y h, C.join_eq k _ _ (C.source_composable hki h),
    C.source_comp_gt i k hki]
lemma join_target_gt (C : OmegaCategory.{u}) (i k : ℕ) (x y : C.Cell)
    (hki : k < i) (h : C.target k x = C.source k y) :
    C.target i (C.join k x y) = C.join k (C.target i x) (C.target i y) := by
  rw [C.join_eq k x y h, C.join_eq k _ _ (C.target_composable hki h),
    C.target_comp_gt i k hki]

lemma join_left_unit (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (hx : C.source k x = x) (h : C.target k x = C.source k y) :
    C.join k x y = y := by
  rw [C.join_eq k x y h, C.comp_of_left_source_fixed k x y h hx]
lemma join_right_unit (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (hy : C.source k y = y) (h : C.target k x = C.source k y) :
    C.join k x y = x := by
  rw [C.join_eq k x y h, C.comp_of_right_source_fixed k x y h hy]

lemma join_assoc (C : OmegaCategory.{u}) (k : ℕ) (x y z : C.Cell)
    (hxy : C.target k x = C.source k y) (hyz : C.target k y = C.source k z) :
    C.join k (C.join k x y) z = C.join k x (C.join k y z) := by
  rw [C.join_eq k x y hxy, C.join_eq k y z hyz,
    C.join_eq k _ z (C.assoc_composable_left hxy hyz),
    C.join_eq k x _ (C.assoc_composable_right hxy hyz)]
  exact C.assoc k x y z _ _ _ _

lemma join_four (C : OmegaCategory.{u}) (k : ℕ) (a b c d : C.Cell)
    (hab : C.target k a = C.source k b) (hbc : C.target k b = C.source k c)
    (hcd : C.target k c = C.source k d) :
    C.join k (C.join k a b) (C.join k c d) = C.join k a (C.join k (C.join k b c) d) := by
  have hb_cd : C.target k b = C.source k (C.join k c d) := by
    rw [C.join_source_le k k c d le_rfl hcd]; exact hbc
  rw [C.join_assoc k a b (C.join k c d) hab hb_cd, C.join_assoc k b c d hbc hcd]

lemma join_four_middle (C : OmegaCategory.{u}) (k : ℕ) (a b c d e f : C.Cell)
    (hab : C.target k a = C.source k b) (hbc : C.target k b = C.source k c)
    (hcd : C.target k c = C.source k d) (hae : C.target k a = C.source k e)
    (hef : C.target k e = C.source k f) (hfd : C.target k f = C.source k d)
    (hm : C.join k b c = C.join k e f) :
    C.join k (C.join k a b) (C.join k c d) =
      C.join k (C.join k a e) (C.join k f d) := by
  rw [C.join_four k a b c d hab hbc hcd, C.join_four k a e f d hae hef hfd, hm]

lemma join_interchange (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b c d : C.Cell)
    (hab : C.target l a = C.source l b) (hcd : C.target l c = C.source l d)
    (hac : C.target k a = C.source k c) (hbd : C.target k b = C.source k d) :
    C.join k (C.join l a b) (C.join l c d) =
      C.join l (C.join k a c) (C.join k b d) := by
  have h₁ : C.target k (C.comp l a b hab) = C.source k (C.comp l c d hcd) := by
    rw [C.target_comp_le k l (by omega), C.source_comp_le k l (by omega)]
    have he : C.target k a = C.target k b := by
      have hh := congrArg (C.target k) hab
      simpa only [C.target_target, min_eq_left (le_of_lt hkl),
        C.target_source, ite_eq_left hkl] using hh
    exact he.symm.trans hac
  have h₂ : C.target l (C.comp k a c hac) = C.source l (C.comp k b d hbd) := by
    rw [C.target_comp_gt l k hkl a c hac (C.target_composable hkl hac),
      C.source_comp_gt l k hkl b d hbd (C.source_composable hkl hbd)]
    simp only [hab, hcd]
  rw [C.join_eq l a b hab, C.join_eq l c d hcd,
    C.join_eq k a c hac, C.join_eq k b d hbd,
    C.join_eq k _ _ h₁, C.join_eq l _ _ h₂]
  exact C.interchange k l hkl a b c d _ _ _ _ _ _

lemma join_factor_right (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b : C.Cell) (h : C.target k a = C.source k b) :
    C.join k a b = C.join l (C.join k a (C.source l b)) (C.join k (C.target l a) b) := by
  have hab : C.target k a = C.source k (C.source l b) := by
    rw [C.source_source, min_eq_left (le_of_lt hkl)]; exact h
  have hab' : C.target k (C.target l a) = C.source k b := by
    rw [C.target_target, min_eq_left (le_of_lt hkl)]; exact h
  have h' := C.join_interchange k l hkl a (C.target l a) (C.source l b) b
    (C.source_target_self l a).symm (C.target_source_self l b) hab hab'
  rw [C.join_right_unit l a (C.target l a) (C.source_target_self l a)
    (C.source_target_self l a).symm,
    C.join_left_unit l (C.source l b) b (C.source_source_self l b) (C.target_source_self l b)] at h'
  exact h'

lemma join_factor_left (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b : C.Cell) (h : C.target k a = C.source k b) :
    C.join k a b = C.join l (C.join k (C.source l a) b) (C.join k a (C.target l b)) := by
  have hab : C.target k (C.source l a) = C.source k b := by
    rw [C.target_source, ite_eq_left hkl]; exact h
  have hab' : C.target k a = C.source k (C.target l b) := by
    rw [C.source_target, ite_eq_left hkl]; exact h
  have h' := C.join_interchange k l hkl (C.source l a) a b (C.target l b)
    (C.target_source_self l a) (C.source_target_self l b).symm hab hab'
  rw [C.join_left_unit l (C.source l a) a (C.source_source_self l a) (C.target_source_self l a),
    C.join_right_unit l b (C.target l b) (C.source_target_self l b)
      (C.source_target_self l b).symm] at h'
  exact h'

lemma join_middle (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b : C.Cell) (h : C.target k a = C.source k b) :
    C.join l (C.join k a (C.source l b)) (C.join k (C.target l a) b) =
      C.join l (C.join k (C.source l a) b) (C.join k a (C.target l b)) :=
  (C.join_factor_right k l hkl a b h).symm.trans (C.join_factor_left k l hkl a b h)

lemma join_whisker_right (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b c : C.Cell) (hc : C.source l c = c)
    (hab : C.target l a = C.source l b)
    (hac : C.target k a = C.source k c) (hbc : C.target k b = C.source k c) :
    C.join k (C.join l a b) c = C.join l (C.join k a c) (C.join k b c) := by
  have hcc : C.target l c = C.source l c := (C.target_eq_self_of_source_eq_self hc).trans hc.symm
  have h' := C.join_interchange k l hkl a b c c hab hcc hac hbc
  rw [C.join_left_unit l c c hc hcc] at h'
  exact h'

lemma join_whisker_left (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b c : C.Cell) (ha : C.source l a = a)
    (hbc : C.target l b = C.source l c)
    (hab : C.target k a = C.source k b) (hac : C.target k a = C.source k c) :
    C.join k a (C.join l b c) = C.join l (C.join k a b) (C.join k a c) := by
  have haa : C.target l a = C.source l a := (C.target_eq_self_of_source_eq_self ha).trans ha.symm
  have h' := C.join_interchange k l hkl a a b c haa hbc hab hac
  rw [C.join_left_unit l a a ha haa] at h'
  exact h'

lemma Functor.map_join {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y) :
    F.map (C.join k x y) = D.join k (F.map x) (F.map y) := by
  rw [C.join_eq k x y h, D.join_eq k _ _ (F.map_composable h), F.map_comp]

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayTwo
open DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace Diagram
variable {X : OmegaCategory.{v}} (D : Diagram X)
lemma obj_composite (e : Fin 8) :
    D.obj (composite e).2.2.2 =
      X.join (composite e).1 (D.obj (composite e).2.1) (D.obj (composite e).2.2.1) := by
  rw [X.join_eq _ _ _ (by rw [D.target_obj, D.source_obj, composite_match])]
  exact (D.composites e).symm
lemma obj5 : D.obj 5 = X.join 0 (D.obj 4) (D.obj 19) := D.obj_composite 3
lemma obj7 : D.obj 7 = X.join 0 (D.obj 4) (D.obj 20) := D.obj_composite 4
lemma obj8 : D.obj 8 = X.join 0 (D.obj 4) (D.obj 21) := D.obj_composite 5
lemma obj9 : D.obj 9 = X.join 1 (D.obj 7) (D.obj 6) := D.obj_composite 6
lemma obj11 : D.obj 11 = X.join 1 (D.obj 12) (D.obj 14) := D.obj_composite 7
lemma obj13 : D.obj 13 = X.join 0 (D.obj 1) (D.obj 17) := D.obj_composite 0
lemma obj14 : D.obj 14 = X.join 0 (D.obj 2) (D.obj 17) := D.obj_composite 1
lemma obj15 : D.obj 15 = X.join 0 (D.obj 3) (D.obj 17) := D.obj_composite 2
end Diagram

section Pasting
variable {X : OmegaCategory.{v}} (L R : Diagram X) (h : L.obj 17 = R.obj 4)

include h in
lemma glue_source : L.obj 16 = R.obj 0 := by
  have h' := congrArg (X.source 0) h
  rw [L.source_obj, R.source_obj] at h'
  exact h'
include h in
lemma glue_target : L.obj 22 = R.obj 18 := by
  have h' := congrArg (X.target 0) h
  rw [L.target_obj, R.target_obj] at h'
  exact h'

def pastedObj (i : Fin 23) : X.Cell :=
  match i.val with
  | 0 => L.obj 0
  | 1 => X.join 0 (L.obj 1) (R.obj 1)
  | 2 => X.join 0 (L.obj 2) (R.obj 2)
  | 3 => X.join 0 (L.obj 3) (R.obj 3)
  | 4 => L.obj 4
  | 5 => X.join 0 (L.obj 4) (X.join 0 (L.obj 19) (R.obj 19))
  | 6 => X.join 1 (X.join 0 (L.obj 6) (R.obj 19)) (X.join 0 (L.obj 1) (R.obj 6))
  | 7 => X.join 0 (L.obj 4) (X.join 0 (L.obj 20) (R.obj 20))
  | 8 => X.join 0 (L.obj 4) (X.join 0 (L.obj 21) (R.obj 21))
  | 9 => X.join 1
      (X.join 0 (L.obj 4) (X.join 0 (L.obj 20) (R.obj 20)))
      (X.join 1 (X.join 0 (L.obj 6) (R.obj 19)) (X.join 0 (L.obj 1) (R.obj 6)))
  | 10 => X.join 1 (X.join 0 (L.obj 10) (R.obj 21)) (X.join 0 (L.obj 1) (R.obj 10))
  | 11 => X.join 1
      (X.join 1 (X.join 0 (L.obj 12) (R.obj 21)) (X.join 0 (L.obj 3) (R.obj 12)))
      (X.join 0 (X.join 0 (L.obj 2) (R.obj 2)) (R.obj 17))
  | 12 => X.join 1 (X.join 0 (L.obj 12) (R.obj 21)) (X.join 0 (L.obj 3) (R.obj 12))
  | 13 => X.join 0 (X.join 0 (L.obj 1) (R.obj 1)) (R.obj 17)
  | 14 => X.join 0 (X.join 0 (L.obj 2) (R.obj 2)) (R.obj 17)
  | 15 => X.join 0 (X.join 0 (L.obj 3) (R.obj 3)) (R.obj 17)
  | 16 => R.obj 16
  | 17 => R.obj 17
  | 18 => L.obj 18
  | 19 => X.join 0 (L.obj 19) (R.obj 19)
  | 20 => X.join 0 (L.obj 20) (R.obj 20)
  | 21 => X.join 0 (L.obj 21) (R.obj 21)
  | _ => R.obj 22

attribute [local simp] Diagram.source_obj Diagram.target_obj
  Diagram.obj5 Diagram.obj7 Diagram.obj8 Diagram.obj9 Diagram.obj11
  Diagram.obj13 Diagram.obj14 Diagram.obj15
  OmegaCategory.join_source_le OmegaCategory.join_source_gt
  OmegaCategory.join_target_le OmegaCategory.join_target_gt
  OmegaCategory.join_assoc

include h in
lemma pasted_match9 :
    X.target 1 (X.join 0 (L.obj 4) (X.join 0 (L.obj 20) (R.obj 20))) =
      X.source 1 (X.join 1 (X.join 0 (L.obj 6) (R.obj 19)) (X.join 0 (L.obj 1) (R.obj 6))) := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  simp [faceIndex, h, hs, ht]

include h in
lemma pasted_match11 :
    X.target 1 (X.join 1 (X.join 0 (L.obj 12) (R.obj 21)) (X.join 0 (L.obj 3) (R.obj 12))) =
      X.source 1 (X.join 0 (L.obj 2) (X.join 0 (R.obj 2) (R.obj 17))) := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  simp [faceIndex, h, hs, ht]

include h in
lemma pasted_source_zero (i : Fin 23) :
    X.source 0 (pastedObj L R i) = pastedObj L R (faceIndex 0 false i) := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  have h9 := pasted_match9 L R h
  have h11 := pasted_match11 L R h
  fin_cases i <;> simp [pastedObj, faceIndex, h, hs, ht, h9, h11]

include h in
lemma pasted_target_zero (i : Fin 23) :
    X.target 0 (pastedObj L R i) = pastedObj L R (faceIndex 0 true i) := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  have h9 := pasted_match9 L R h
  have h11 := pasted_match11 L R h
  fin_cases i <;> simp [pastedObj, faceIndex, h, hs, ht, h9, h11]

include h in
lemma pasted_source_one (i : Fin 23) :
    X.source 1 (pastedObj L R i) = pastedObj L R (faceIndex 1 false i) := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  have h9 := pasted_match9 L R h
  have h11 := pasted_match11 L R h
  fin_cases i <;> simp [pastedObj, faceIndex, h, hs, ht, h9, h11]

include h in
lemma pasted_target_one (i : Fin 23) :
    X.target 1 (pastedObj L R i) = pastedObj L R (faceIndex 1 true i) := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  have h9 := pasted_match9 L R h
  have h11 := pasted_match11 L R h
  fin_cases i <;> simp [pastedObj, faceIndex, h, hs, ht, h9, h11]

include h in
lemma pasted_source_three (i : Fin 23) :
    X.source 3 (pastedObj L R i) = pastedObj L R (faceIndex 3 false i) := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  have h9 := pasted_match9 L R h
  have h11 := pasted_match11 L R h
  fin_cases i <;> simp [pastedObj, faceIndex, h, hs, ht, h9, h11]

include h in
lemma pasted_source_two_others (i : Fin 23) (hi : i ≠ 10) :
    X.source 2 (pastedObj L R i) = pastedObj L R (faceIndex 2 false i) := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  have h9 := pasted_match9 L R h
  have h11 := pasted_match11 L R h
  fin_cases i <;> try contradiction
  all_goals simp [pastedObj, faceIndex, h, hs, ht, h9, h11]

include h in
lemma pasted_target_two_others (i : Fin 23) (hi : i ≠ 10) :
    X.target 2 (pastedObj L R i) = pastedObj L R (faceIndex 2 true i) := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  have h9 := pasted_match9 L R h
  have h11 := pasted_match11 L R h
  fin_cases i <;> try contradiction
  all_goals simp [pastedObj, faceIndex, h, hs, ht, h9, h11]

include h in
lemma pasted_source_coherence :
    X.join 1
      (X.join 0 (X.join 1 (L.obj 12) (X.join 0 (L.obj 2) (R.obj 4))) (R.obj 21))
      (X.join 0 (L.obj 1) (X.join 1 (R.obj 12) (X.join 0 (R.obj 2) (R.obj 17)))) =
    X.join 1
      (X.join 1 (X.join 0 (L.obj 12) (R.obj 21)) (X.join 0 (L.obj 3) (R.obj 12)))
      (X.join 0 (L.obj 2) (X.join 0 (R.obj 2) (R.obj 17))) := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  let a := X.join 0 (L.obj 12) (R.obj 21)
  let b := X.join 0 (L.obj 2) (X.join 0 (R.obj 4) (R.obj 21))
  let c := X.join 0 (L.obj 1) (R.obj 12)
  let d := X.join 0 (L.obj 1) (X.join 0 (R.obj 2) (R.obj 17))
  let e := X.join 0 (L.obj 3) (R.obj 12)
  let f := X.join 0 (L.obj 2) (X.join 0 (R.obj 3) (R.obj 17))
  have hm : X.join 1 b c = X.join 1 e f := by
    have hm' := X.join_middle 0 1 (by decide) (L.obj 2) (R.obj 12)
      (by simp [faceIndex, hs])
    simpa [b, c, e, f, faceIndex, h, hs, ht] using hm'
  have hf : X.join 0 (L.obj 2) (X.join 0 (R.obj 2) (R.obj 17)) = X.join 1 f d := by
    have hf' := X.join_factor_right 0 1 (by decide) (L.obj 2) (X.join 0 (R.obj 2) (R.obj 17))
      (by simp [faceIndex, hs])
    simpa [f, d, faceIndex, h, hs, ht] using hf'
  have hl : X.join 0 (X.join 1 (L.obj 12) (X.join 0 (L.obj 2) (R.obj 4))) (R.obj 21) =
      X.join 1 a b := by
    have hl' := X.join_whisker_right 0 1 (by decide) (L.obj 12)
      (X.join 0 (L.obj 2) (R.obj 4)) (R.obj 21)
      (by simp [faceIndex]) (by simp [faceIndex, h, hs])
      (by simp [faceIndex, ht]) (by simp [faceIndex, hs])
    simpa [a, b, faceIndex, hs, ht] using hl'
  have hr : X.join 0 (L.obj 1) (X.join 1 (R.obj 12) (X.join 0 (R.obj 2) (R.obj 17))) =
      X.join 1 c d := by
    exact X.join_whisker_left 0 1 (by decide) (L.obj 1) (R.obj 12)
      (X.join 0 (R.obj 2) (R.obj 17))
      (by simp [faceIndex]) (by simp [faceIndex])
      (by simp [faceIndex, hs]) (by simp [faceIndex, hs])
  rw [hl, hr, hf]
  exact X.join_four_middle 1 a b c d e f
    (by simp [a, b, faceIndex, h, hs, ht])
    (by simp [b, c, faceIndex, hs])
    (by simp [c, d, faceIndex, hs])
    (by simp [a, e, faceIndex, h, hs, ht])
    (by simp [e, f, faceIndex, hs])
    (by simp [f, d, faceIndex, hs]) hm

include h in
lemma pasted_source_two_top :
    X.source 2 (pastedObj L R 10) = pastedObj L R 11 := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  simpa [pastedObj, faceIndex, h, hs, ht] using pasted_source_coherence L R h

include h in
lemma pasted_target_coherence :
    X.join 1
      (X.join 0 (X.join 1 (X.join 0 (L.obj 4) (L.obj 20)) (L.obj 6)) (R.obj 21))
      (X.join 0 (L.obj 1) (X.join 1 (X.join 0 (R.obj 4) (R.obj 20)) (R.obj 6))) =
    X.join 1 (X.join 0 (L.obj 4) (X.join 0 (L.obj 20) (R.obj 20)))
      (X.join 1 (X.join 0 (L.obj 6) (R.obj 19)) (X.join 0 (L.obj 1) (R.obj 6))) := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  let a := X.join 0 (L.obj 4) (X.join 0 (L.obj 20) (R.obj 21))
  let b := X.join 0 (L.obj 6) (R.obj 21)
  let c := X.join 0 (L.obj 1) (X.join 0 (R.obj 4) (R.obj 20))
  let d := X.join 0 (L.obj 1) (R.obj 6)
  let e := X.join 0 (L.obj 4) (X.join 0 (L.obj 19) (R.obj 20))
  let f := X.join 0 (L.obj 6) (R.obj 19)
  have hm : X.join 1 b c = X.join 1 e f := by
    have hm' := X.join_middle 0 1 (by decide) (L.obj 6) (R.obj 20)
      (by simp [faceIndex, ht])
    simpa [b, c, e, f, faceIndex, h, hs, ht] using hm'
  have hf : X.join 0 (L.obj 4) (X.join 0 (L.obj 20) (R.obj 20)) = X.join 1 a e := by
    have hf' := X.join_factor_right 0 1 (by decide) (X.join 0 (L.obj 4) (L.obj 20)) (R.obj 20)
      (by simp [faceIndex, ht])
    simpa [a, e, faceIndex, h, hs, ht] using hf'
  have hl : X.join 0 (X.join 1 (X.join 0 (L.obj 4) (L.obj 20)) (L.obj 6)) (R.obj 21) =
      X.join 1 a b := by
    have hl' := X.join_whisker_right 0 1 (by decide) (X.join 0 (L.obj 4) (L.obj 20))
      (L.obj 6) (R.obj 21)
      (by simp [faceIndex]) (by simp [faceIndex])
      (by simp [faceIndex, ht]) (by simp [faceIndex, ht])
    simpa [a, b, faceIndex, hs, ht] using hl'
  have hr : X.join 0 (L.obj 1) (X.join 1 (X.join 0 (R.obj 4) (R.obj 20)) (R.obj 6)) =
      X.join 1 c d := by
    exact X.join_whisker_left 0 1 (by decide) (L.obj 1) (X.join 0 (R.obj 4) (R.obj 20))
      (R.obj 6) (by simp [faceIndex]) (by simp [faceIndex])
      (by simp [faceIndex, hs]) (by simp [faceIndex, hs])
  rw [hl, hr, hf]
  exact X.join_four_middle 1 a b c d e f
    (by simp [a, b, faceIndex, ht])
    (by simp [b, c, faceIndex, h, hs, ht])
    (by simp [c, d, faceIndex, hs])
    (by simp [a, e, faceIndex, ht])
    (by simp [e, f, faceIndex, ht])
    (by simp [f, d, faceIndex, h, hs, ht]) hm

include h in
lemma pasted_target_two_top :
    X.target 2 (pastedObj L R 10) = pastedObj L R 9 := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  simpa [pastedObj, faceIndex, h, hs, ht] using pasted_target_coherence L R h

include h in
lemma pasted_faces (k : ℕ) (b : Bool) (i : Fin 23) :
    X.face k b (pastedObj L R i) = pastedObj L R (faceIndex k b i) := by
  rcases k with _ | _ | _ | k
  · cases b
    · exact pasted_source_zero L R h i
    · exact pasted_target_zero L R h i
  · cases b
    · exact pasted_source_one L R h i
    · exact pasted_target_one L R h i
  · by_cases hi : i = 10
    · subst i
      cases b
      · exact pasted_source_two_top L R h
      · exact pasted_target_two_top L R h
    · cases b
      · exact pasted_source_two_others L R h i hi
      · exact pasted_target_two_others L R h i hi
  · exact X.face_of_fixed (pasted_source_three L R h i) (by omega) b

def paste : Diagram X where
  obj := pastedObj L R
  faces := pasted_faces L R h
  composites e := by
    rw [← X.join_eq]
    fin_cases e <;> rfl

@[simp] lemma paste_obj (i : Fin 23) : (paste L R h).obj i = pastedObj L R i := rfl

end Pasting
end Thomason.GrayTwo

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayTwo
open DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace Diagram
variable {X : OmegaCategory.{v}} {Y : OmegaCategory.{w}}

def map (D : Diagram X) (F : OmegaCategory.Functor X Y) : Diagram Y where
  obj i := F.map (D.obj i)
  faces k b i := by rw [← F.map_face, D.faces]
  composites e := by
    have h : X.target (composite e).1 (D.obj (composite e).2.1) =
        X.source (composite e).1 (D.obj (composite e).2.2.1) := by
      rw [D.target_obj, D.source_obj, composite_match]
    rw [← F.map_comp _ _ _ h, D.composites]

@[simp] lemma map_obj (D : Diagram X) (F : OmegaCategory.Functor X Y) (i : Fin 23) :
    (D.map F).obj i = F.map (D.obj i) := rfl

end Diagram

lemma map_pastedObj {X : OmegaCategory.{v}} {Y : OmegaCategory.{w}}
    (L R : Diagram X) (h : L.obj 17 = R.obj 4) (F : OmegaCategory.Functor X Y) (i : Fin 23) :
    F.map (pastedObj L R i) = pastedObj (L.map F) (R.map F) i := by
  have hs := glue_source L R h
  have ht := glue_target L R h
  have h9 := pasted_match9 L R h
  have h11 := pasted_match11 L R h
  fin_cases i <;> simp [pastedObj, Diagram.map_obj, Functor.map_join,
    Diagram.source_obj, Diagram.target_obj,
    Diagram.obj5, Diagram.obj8, Diagram.obj13, Diagram.obj15,
    OmegaCategory.join_source_le, OmegaCategory.join_source_gt,
    OmegaCategory.join_target_gt,
    faceIndex, h, hs, ht, h9, h11, OmegaCategory.join_assoc,
    ← F.map_source, ← F.map_target]

def generators : Fin 7 → Fin 23 := ![2, 4, 6, 10, 12, 17, 20]

lemma functor_ext_generators {X : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor K.{u}.nu X)
    (h : ∀ i, F.map (cell (generators i)) = G.map (cell (generators i))) : F = G := by
  let D := diagramOfFunctor F
  let E := diagramOfFunctor G
  have h₂ : D.obj 2 = E.obj 2 := h 0
  have h₄ : D.obj 4 = E.obj 4 := h 1
  have h₆ : D.obj 6 = E.obj 6 := h 2
  have h₁₀ : D.obj 10 = E.obj 10 := h 3
  have h₁₂ : D.obj 12 = E.obj 12 := h 4
  have h₁₇ : D.obj 17 = E.obj 17 := h 5
  have h₂₀ : D.obj 20 = E.obj 20 := h 6
  have hf (i : Fin 23) (he : D.obj i = E.obj i) (k : ℕ) (b : Bool) :
      D.obj (faceIndex k b i) = E.obj (faceIndex k b i) := by
    rw [← D.faces, ← E.faces, he]
  have h₀ : D.obj 0 = E.obj 0 := hf 2 h₂ 0 false
  have h₁ : D.obj 1 = E.obj 1 := hf 2 h₂ 1 true
  have h₃ : D.obj 3 = E.obj 3 := hf 2 h₂ 1 false
  have h₁₆ : D.obj 16 = E.obj 16 := hf 2 h₂ 0 true
  have h₁₈ : D.obj 18 = E.obj 18 := hf 20 h₂₀ 0 false
  have h₁₉ : D.obj 19 = E.obj 19 := hf 20 h₂₀ 1 true
  have h₂₁ : D.obj 21 = E.obj 21 := hf 20 h₂₀ 1 false
  have h₂₂ : D.obj 22 = E.obj 22 := hf 20 h₂₀ 0 true
  apply functor_ext
  intro i
  change D.obj i = E.obj i
  fin_cases i
  · change D.obj 0 = E.obj 0
    exact h₀
  · change D.obj 1 = E.obj 1
    exact h₁
  · change D.obj 2 = E.obj 2
    exact h₂
  · change D.obj 3 = E.obj 3
    exact h₃
  · change D.obj 4 = E.obj 4
    exact h₄
  · change D.obj 5 = E.obj 5
    simp only [Diagram.obj5, h₄, h₁₉]
  · change D.obj 6 = E.obj 6
    exact h₆
  · change D.obj 7 = E.obj 7
    simp only [Diagram.obj7, h₄, h₂₀]
  · change D.obj 8 = E.obj 8
    simp only [Diagram.obj8, h₄, h₂₁]
  · change D.obj 9 = E.obj 9
    simp only [Diagram.obj7, Diagram.obj9, h₄, h₆, h₂₀]
  · change D.obj 10 = E.obj 10
    exact h₁₀
  · change D.obj 11 = E.obj 11
    simp only [Diagram.obj11, Diagram.obj14, h₂, h₁₂, h₁₇]
  · change D.obj 12 = E.obj 12
    exact h₁₂
  · change D.obj 13 = E.obj 13
    simp only [Diagram.obj13, h₁, h₁₇]
  · change D.obj 14 = E.obj 14
    simp only [Diagram.obj14, h₂, h₁₇]
  · change D.obj 15 = E.obj 15
    simp only [Diagram.obj15, h₃, h₁₇]
  · change D.obj 16 = E.obj 16
    exact h₁₆
  · change D.obj 17 = E.obj 17
    exact h₁₇
  · change D.obj 18 = E.obj 18
    exact h₁₈
  · change D.obj 19 = E.obj 19
    exact h₁₉
  · change D.obj 20 = E.obj 20
    exact h₂₀
  · change D.obj 21 = E.obj 21
    exact h₂₁
  · change D.obj 22 = E.obj 22
    exact h₂₂

end Thomason.GrayTwo

end

end OAI
