import OAI.CategoryTheory.Thomason.StrictCategories
import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement

namespace OAI

/-! The equivalence between separate-boundary and Boolean-face presentations
of strict omega-categories preserves every cell and every composition. -/

universe u v

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

private theorem source_comp_le (C : StrictOmegaCategory.{u}) (i k : ℕ)
    (hik : i ≤ k) (x y : C) (h : C.target k x = C.source k y) :
    C.source i (C.comp k x y h) = C.source i x := by
  rcases lt_or_eq_of_le hik with hik | rfl
  · have hc := congrArg (C.face false i) (C.source_comp k x y h)
    simpa only [C.globular, hik, ite_true] using hc
  · exact C.source_comp i x y h

private theorem target_comp_le (C : StrictOmegaCategory.{u}) (i k : ℕ)
    (hik : i ≤ k) (x y : C) (h : C.target k x = C.source k y) :
    C.target i (C.comp k x y h) = C.target i y := by
  rcases lt_or_eq_of_le hik with hik | rfl
  · have hc := congrArg (C.face true i) (C.target_comp k x y h)
    simpa only [C.globular, hik, ite_true] using hc
  · exact C.target_comp i x y h

/-- Interpret Boolean faces as separate source and target operations. -/
def toOmegaCategory (C : StrictOmegaCategory.{u}) : Thomason.OmegaCategory.{u} where
  Cell := C.Cell
  source := C.source
  target := C.target
  source_source i j x := by
    change C.face false i (C.face false j x) = C.face false (min i j) x
    rw [C.globular]
    split_ifs with hij
    · rw [min_eq_left (le_of_lt hij)]
    · rw [min_eq_right (le_of_not_gt hij)]
  target_target i j x := by
    change C.face true i (C.face true j x) = C.face true (min i j) x
    rw [C.globular]
    split_ifs with hij
    · rw [min_eq_left (le_of_lt hij)]
    · rw [min_eq_right (le_of_not_gt hij)]
  source_target := C.globular false true
  target_source := C.globular true false
  comp := C.comp
  source_comp_le := source_comp_le C
  target_comp_le := target_comp_le C
  source_comp_gt i k hki x y h hs := C.face_comp false i k hki x y h hs
  target_comp_gt i k hki x y h ht := C.face_comp true i k hki x y h ht
  unit_left := C.left_unit
  unit_right := C.right_unit
  assoc := C.assoc
  interchange k l hkl a b c d hab hcd hac hbd hl hr :=
    (C.interchange k l hkl a c b d hac hbd hab hcd hr hl).symm
  finite_dimension x := by
    obtain ⟨n, hn, _⟩ := C.finite_dimension x
    exact ⟨n, hn⟩

/-- The same cell function is a functor in the separate-boundary presentation. -/
def Hom.toOmegaFunctor {C : StrictOmegaCategory.{u}} {D : StrictOmegaCategory.{v}}
    (f : Hom C D) : Thomason.OmegaCategory.Functor C.toOmegaCategory D.toOmegaCategory where
  map := f.toFun
  map_source := f.map_face false
  map_target := f.map_face true
  map_comp := f.map_comp

@[simp] theorem toOmegaCategory_isTruncated (C : StrictOmegaCategory.{u}) (n : ℕ) :
    C.toOmegaCategory.IsTruncated n ↔ C.IsTruncated n := by
  constructor
  · intro h x
    exact ⟨h x, C.toOmegaCategory.target_eq_self_of_source_eq_self (h x)⟩
  · intro h x
    exact (h x).1

end Thomason.Construction.StrictOmegaCategory

namespace Thomason.OmegaCategory

/-- Combine source and target into a Boolean-indexed boundary operation. -/
def toStrictOmegaCategory (C : OmegaCategory.{u}) : Construction.StrictOmegaCategory.{u} where
  Cell := C.Cell
  face a n x := if a then C.target n x else C.source n x
  globular a b m n x := by
    cases a <;> cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · rw [C.source_source]
      split_ifs with h
      · rw [min_eq_left (le_of_lt h)]
      · rw [min_eq_right (le_of_not_gt h)]
    · exact C.source_target m n x
    · exact C.target_source m n x
    · rw [C.target_target]
      split_ifs with h
      · rw [min_eq_left (le_of_lt h)]
      · rw [min_eq_right (le_of_not_gt h)]
  comp := C.comp
  source_comp n x y h := C.source_comp_le n n le_rfl x y h
  target_comp n x y h := C.target_comp_le n n le_rfl x y h
  face_comp a m n hnm x y h h' := by
    cases a
    · exact C.source_comp_gt m n hnm x y h h'
    · exact C.target_comp_gt m n hnm x y h h'
  left_unit := C.unit_left
  right_unit := C.unit_right
  assoc := C.assoc
  interchange m n hmn a b c d hab hcd hac hbd hl hr :=
    (C.interchange m n hmn a c b d hac hbd hab hcd hr hl).symm
  finite_dimension x := by
    obtain ⟨n, hn⟩ := C.finite_dimension x
    exact ⟨n, hn, C.target_eq_self_of_source_eq_self hn⟩

/-- Strict functors preserve the combined Boolean face operation. -/
def Functor.toStrictHom {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (f : Functor C D) : Construction.StrictOmegaCategory.Hom
      C.toStrictOmegaCategory D.toStrictOmegaCategory where
  toFun := f.map
  map_face a n x := by
    cases a
    · exact f.map_source n x
    · exact f.map_target n x
  map_comp := f.map_comp

@[simp] theorem toStrictOmegaCategory_isTruncated (C : OmegaCategory.{u}) (n : ℕ) :
    C.toStrictOmegaCategory.IsTruncated n ↔ C.IsTruncated n := by
  constructor
  · intro h x
    exact (h x).1
  · intro h x
    exact ⟨h x, C.target_eq_self_of_source_eq_self (h x)⟩

end Thomason.OmegaCategory

namespace Thomason.Construction

open CategoryTheory

/-- The cell-preserving conversion to separate source and target. -/
def toOmega : StrictOmegaCategory.{u} ⥤ OmegaCategory.{u} where
  obj := StrictOmegaCategory.toOmegaCategory
  map := StrictOmegaCategory.Hom.toOmegaFunctor
  map_id _ := by apply OmegaCategory.Functor.ext; rfl
  map_comp _ _ := by apply OmegaCategory.Functor.ext; rfl

/-- The cell-preserving conversion to Boolean-indexed boundaries. -/
def fromOmega : OmegaCategory.{u} ⥤ StrictOmegaCategory.{u} where
  obj := OmegaCategory.toStrictOmegaCategory
  map := OmegaCategory.Functor.toStrictHom
  map_id _ := by apply StrictOmegaCategory.Hom.ext; rfl
  map_comp _ _ := by apply StrictOmegaCategory.Hom.ext; rfl

private def strictRoundtripIso (C : StrictOmegaCategory.{u}) :
    C ≅ fromOmega.obj (toOmega.obj C) where
  hom :=
    { toFun := fun x => x
      map_face a _ _ := by cases a <;> rfl
      map_comp _ _ _ _ _ := rfl }
  inv :=
    { toFun := fun x => x
      map_face a _ _ := by cases a <;> rfl
      map_comp _ _ _ _ _ := rfl }
  hom_inv_id := by apply StrictOmegaCategory.Hom.ext; rfl
  inv_hom_id := by apply StrictOmegaCategory.Hom.ext; rfl

private def omegaRoundtripIso (C : OmegaCategory.{u}) :
    toOmega.obj (fromOmega.obj C) ≅ C where
  hom :=
    { map := fun x => x
      map_source _ _ := rfl
      map_target _ _ := rfl
      map_comp _ _ _ _ _ := rfl }
  inv :=
    { map := fun x => x
      map_source _ _ := rfl
      map_target _ _ := rfl
      map_comp _ _ _ _ _ := rfl }
  hom_inv_id := by apply OmegaCategory.Functor.ext; rfl
  inv_hom_id := by apply OmegaCategory.Functor.ext; rfl

/-- The two presentations describe equivalent categories of strict omega-categories. -/
noncomputable def representationEquivalence : StrictOmegaCategory.{u} ≌ OmegaCategory.{u} where
  functor := toOmega
  inverse := fromOmega
  unitIso := NatIso.ofComponents strictRoundtripIso (by intro C D f; apply StrictOmegaCategory.Hom.ext; rfl)
  counitIso := NatIso.ofComponents omegaRoundtripIso (by intro C D f; apply OmegaCategory.Functor.ext; rfl)
  functor_unitIso_comp C := by apply OmegaCategory.Functor.ext; rfl

/-- Conversion restricted to categories with a uniform finite dimension bound. -/
def toFiniteOmega (n : ℕ) : StrictOmegaCategory.Truncated.{u} n ⥤
    OmegaCategory.NCategory.{u} n where
  obj C := ⟨C.val.toOmegaCategory, (C.val.toOmegaCategory_isTruncated n).mpr C.property⟩
  map := StrictOmegaCategory.Hom.toOmegaFunctor
  map_id _ := by apply OmegaCategory.Functor.ext; rfl
  map_comp _ _ := by apply OmegaCategory.Functor.ext; rfl

/-- The inverse conversion also preserves the same finite dimension bound. -/
def fromFiniteOmega (n : ℕ) : OmegaCategory.NCategory.{u} n ⥤
    StrictOmegaCategory.Truncated.{u} n where
  obj C := ⟨C.val.toStrictOmegaCategory, (C.val.toStrictOmegaCategory_isTruncated n).mpr C.property⟩
  map := OmegaCategory.Functor.toStrictHom
  map_id _ := by apply StrictOmegaCategory.Hom.ext; rfl
  map_comp _ _ := by apply StrictOmegaCategory.Hom.ext; rfl

/-- The presentation equivalence restricts in every finite dimension. -/
noncomputable def finiteRepresentationEquivalence (n : ℕ) : StrictOmegaCategory.Truncated.{u} n ≌
    OmegaCategory.NCategory.{u} n where
  functor := toFiniteOmega n
  inverse := fromFiniteOmega n
  unitIso := NatIso.ofComponents (fun C =>
    { hom := (strictRoundtripIso C.val).hom
      inv := (strictRoundtripIso C.val).inv
      hom_inv_id := by apply StrictOmegaCategory.Hom.ext; rfl
      inv_hom_id := by apply StrictOmegaCategory.Hom.ext; rfl }) (by intro C D f; apply StrictOmegaCategory.Hom.ext; rfl)
  counitIso := NatIso.ofComponents (fun C =>
    { hom := (omegaRoundtripIso C.val).hom
      inv := (omegaRoundtripIso C.val).inv
      hom_inv_id := by apply OmegaCategory.Functor.ext; rfl
      inv_hom_id := by apply OmegaCategory.Functor.ext; rfl }) (by intro C D f; apply OmegaCategory.Functor.ext; rfl)
  functor_unitIso_comp C := by apply OmegaCategory.Functor.ext; rfl

end Thomason.Construction

end OAI
