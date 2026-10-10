import Mathlib
import OAI.CategoryTheory.Thomason.DirectedPrisms

namespace OAI

/-! Cones. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

abbrev Objects (C : OmegaCategory.{u}) := C.Cells 0

def sourceObject (C : OmegaCategory.{u}) (x : C.Cell) : C.Objects :=
  ⟨C.source 0 x, C.source_source_self 0 x⟩

def targetObject (C : OmegaCategory.{u}) (x : C.Cell) : C.Objects :=
  ⟨C.target 0 x, C.source_target_self 0 x⟩

@[simp] lemma sourceObject_source_zero (C : OmegaCategory.{u}) (x : C.Cell) :
    C.sourceObject (C.source 0 x) = C.sourceObject x := by
  apply Subtype.ext
  exact C.source_source_self 0 x

@[simp] lemma targetObject_source_zero (C : OmegaCategory.{u}) (x : C.Cell) :
    C.targetObject (C.source 0 x) = C.sourceObject x := by
  apply Subtype.ext
  exact C.target_source_self 0 x

@[simp] lemma sourceObject_target_zero (C : OmegaCategory.{u}) (x : C.Cell) :
    C.sourceObject (C.target 0 x) = C.targetObject x := by
  apply Subtype.ext
  exact C.source_target_self 0 x

@[simp] lemma targetObject_target_zero (C : OmegaCategory.{u}) (x : C.Cell) :
    C.targetObject (C.target 0 x) = C.targetObject x := by
  apply Subtype.ext
  exact C.target_target_self 0 x

@[simp] lemma sourceObject_source_succ (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.sourceObject (C.source (k+1) x) = C.sourceObject x := by
  apply Subtype.ext
  exact C.source_source 0 (k+1) x

@[simp] lemma targetObject_source_succ (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.targetObject (C.source (k+1) x) = C.targetObject x := by
  apply Subtype.ext
  simpa [targetObject] using C.target_source 0 (k+1) x

@[simp] lemma sourceObject_target_succ (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.sourceObject (C.target (k+1) x) = C.sourceObject x := by
  apply Subtype.ext
  simpa [sourceObject] using C.source_target 0 (k+1) x

@[simp] lemma targetObject_target_succ (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.targetObject (C.target (k+1) x) = C.targetObject x := by
  apply Subtype.ext
  exact C.target_target 0 (k+1) x

@[simp] lemma sourceObject_comp (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell) (h) :
    C.sourceObject (C.comp k x y h) = C.sourceObject x := by
  apply Subtype.ext
  exact C.source_comp_le 0 k (Nat.zero_le k) x y h

@[simp] lemma targetObject_comp (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell) (h) :
    C.targetObject (C.comp k x y h) = C.targetObject y := by
  apply Subtype.ext
  exact C.target_comp_le 0 k (Nat.zero_le k) x y h

@[simp] lemma sourceObject_object (C : OmegaCategory.{u}) (x : C.Objects) :
    C.sourceObject x.val = x := Subtype.ext x.property

@[simp] lemma targetObject_object (C : OmegaCategory.{u}) (x : C.Objects) :
    C.targetObject x.val = x := Subtype.ext (C.target_eq_self_of_source_eq_self x.property)

def Functor.objects {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (x : C.Objects) : D.Objects :=
  ⟨F.map x.val, by rw [← F.map_source, x.property]⟩

@[simp] lemma Functor.objects_source {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (x : C.Cell) : F.objects (C.sourceObject x) = D.sourceObject (F.map x) :=
  Subtype.ext (F.map_source 0 x)

@[simp] lemma Functor.objects_target {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (x : C.Cell) : F.objects (C.targetObject x) = D.targetObject (F.map x) :=
  Subtype.ext (F.map_target 0 x)

def thinMap {S : Type u} {T : Type v} {r : S → S → Prop} {q : T → T → Prop}
    {hr : ∀ s, r s s} {ht : ∀ {s t v}, r s t → r t v → r s v}
    {hq : ∀ s, q s s} {hu : ∀ {s t v}, q s t → q t v → q s v}
    (f : S → T) (hf : ∀ {s t}, r s t → q (f s) (f t)) :
    Functor (thin r hr ht) (thin q hq hu) where
  map x := ⟨f x.left, f x.right, hf x.related⟩
  map_source k x := by cases k <;> apply ThinCell.ext <;> rfl
  map_target k x := by cases k <;> apply ThinCell.ext <;> rfl
  map_comp k x y h h' := by cases k <;> apply ThinCell.ext <;> rfl

def chaoticLift {C : OmegaCategory.{u}} {S : Type v} (f : C.Objects → S) :
    Functor C (chaotic S) where
  map x := ⟨f (C.sourceObject x), f (C.targetObject x), True.intro⟩
  map_source k x := by
    cases k with
    | zero => apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.source, ThinCell.vertex]
    | succ k => apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.source]
  map_target k x := by
    cases k with
    | zero => apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.target, ThinCell.vertex]
    | succ k => apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.target]
  map_comp k x y h h' := by
    cases k with
    | zero => apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.comp]
    | succ k =>
      have he : C.targetObject x = C.targetObject y := by
        simpa using congrArg C.targetObject h
      apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.comp, he]

def chaoticRestrict {C : OmegaCategory.{u}} {S : Type v}
    (F : Functor C (chaotic S)) (x : C.Objects) : S := (F.map x.val).left

def chaoticHomEquiv (C : OmegaCategory.{u}) (S : Type v) :
    (C.Objects → S) ≃ Functor C (chaotic S) where
  toFun := chaoticLift
  invFun := chaoticRestrict
  left_inv f := by funext x; simp [chaoticRestrict, chaoticLift]
  right_inv F := by
    apply Functor.ext
    funext x
    apply ThinCell.ext
    · change (F.map (C.source 0 x)).left = (F.map x).left
      have hh := congrArg (fun z : (chaotic S).Cell => z.left) (F.map_source 0 x)
      exact hh
    · change (F.map (C.target 0 x)).left = (F.map x).right
      have hh := congrArg (fun z : (chaotic S).Cell => z.left) (F.map_target 0 x)
      exact hh

def objectsFunctor : CategoryTheory.Functor OmegaCategory.{u} (Type u) where
  obj := Objects
  map F := TypeCat.ofHom F.objects

def chaoticFunctor : CategoryTheory.Functor (Type u) OmegaCategory.{u} where
  obj := chaotic
  map f := thinMap f (fun _ => True.intro)

def objectsChaoticAdjunction : CategoryTheory.Adjunction objectsFunctor chaoticFunctor :=
  CategoryTheory.Adjunction.mkOfHomEquiv {
    homEquiv := fun C S => TypeCat.homEquiv.trans (chaoticHomEquiv C S)
    homEquiv_naturality_left_symm := by
      intro C' C S F G
      rfl
    homEquiv_naturality_right := by
      intro C S T f g
      rfl }

noncomputable instance objects_preservesColimits :
    CategoryTheory.Limits.PreservesColimitsOfSize.{v,w} objectsFunctor.{u} :=
  objectsChaoticAdjunction.leftAdjoint_preservesColimits

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

structure Subcategory (C : OmegaCategory.{u}) where
  carrier : Set C.Cell
  source_mem (k : ℕ) {x : C.Cell} : x ∈ carrier → C.source k x ∈ carrier
  target_mem (k : ℕ) {x : C.Cell} : x ∈ carrier → C.target k x ∈ carrier
  comp_mem (k : ℕ) {x y : C.Cell} (h : C.target k x = C.source k y) :
    x ∈ carrier → y ∈ carrier → C.comp k x y h ∈ carrier

namespace Subcategory

variable {C : OmegaCategory.{u}} (S : Subcategory C)

def category : OmegaCategory.{u} where
  Cell := S.carrier
  source k x := ⟨C.source k x.val, S.source_mem k x.property⟩
  target k x := ⟨C.target k x.val, S.target_mem k x.property⟩
  source_source i j x := Subtype.ext (C.source_source i j x.val)
  target_target i j x := Subtype.ext (C.target_target i j x.val)
  source_target i j x := by
    apply Subtype.ext
    by_cases h : i < j <;> simpa [h] using C.source_target i j x.val
  target_source i j x := by
    apply Subtype.ext
    by_cases h : i < j <;> simpa [h] using C.target_source i j x.val
  comp k x y h := ⟨C.comp k x.val y.val (congrArg Subtype.val h),
    S.comp_mem k _ x.property y.property⟩
  source_comp_le i k hik x y h := Subtype.ext (C.source_comp_le i k hik x.val y.val _)
  target_comp_le i k hik x y h := Subtype.ext (C.target_comp_le i k hik x.val y.val _)
  source_comp_gt i k hki x y h hs := Subtype.ext (C.source_comp_gt i k hki x.val y.val _ _)
  target_comp_gt i k hki x y h ht := Subtype.ext (C.target_comp_gt i k hki x.val y.val _ _)
  unit_left k x h := Subtype.ext (C.unit_left k x.val _)
  unit_right k x h := Subtype.ext (C.unit_right k x.val _)
  assoc k x y z hxy hyz hxy_z hx_yz := Subtype.ext (C.assoc k x.val y.val z.val _ _ _ _)
  interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd :=
    Subtype.ext (C.interchange k l hkl a.val b.val c.val d.val _ _ _ _ _ _)
  finite_dimension x := by
    obtain ⟨k, hk⟩ := C.finite_dimension x.val
    exact ⟨k, Subtype.ext hk⟩

def inclusion : Functor S.category C where
  map := Subtype.val
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ _ := rfl

def lift {D : OmegaCategory.{v}} (F : Functor D C) (hf : ∀ x, F.map x ∈ S.carrier) :
    Functor D S.category where
  map x := ⟨F.map x, hf x⟩
  map_source k x := Subtype.ext (F.map_source k x)
  map_target k x := Subtype.ext (F.map_target k x)
  map_comp k x y h h' := Subtype.ext (F.map_comp k x y h (congrArg Subtype.val h'))

lemma lift_inclusion {D : OmegaCategory.{v}} (F : Functor D C)
    (hf : ∀ x, F.map x ∈ S.carrier) : Functor.comp (S.lift F hf) S.inclusion = F := rfl

lemma inclusion_injective : Function.Injective S.inclusion.map := Subtype.val_injective

end Subcategory

def fullOn (C : OmegaCategory.{u}) (S : Set C.Objects) : Subcategory C where
  carrier := {x | C.sourceObject x ∈ S ∧ C.targetObject x ∈ S}
  source_mem k x hx := by
    cases k with
    | zero => simpa only [Set.mem_ofPred_eq, sourceObject_source_zero,
        targetObject_source_zero, and_self] using hx.1
    | succ k => simpa only [Set.mem_ofPred_eq, sourceObject_source_succ,
        targetObject_source_succ] using hx
  target_mem k x hx := by
    cases k with
    | zero => simpa only [Set.mem_ofPred_eq, sourceObject_target_zero,
        targetObject_target_zero, and_self] using hx.2
    | succ k => simpa only [Set.mem_ofPred_eq, sourceObject_target_succ,
        targetObject_target_succ] using hx
  comp_mem k x y h hx hy := by
    exact ⟨by simpa only [sourceObject_comp] using hx.1,
      by simpa only [targetObject_comp] using hy.2⟩

lemma comp_fixed (C : OmegaCategory.{u}) (k : ℕ) {x : C.Cell}
    (hx : C.source k x = x) (h : C.target k x = C.source k x) : C.comp k x x h = x := by
  have hu := C.unit_left k x (C.target_source_self k x)
  simpa only [hx] using hu

lemma comp_eq_of_eq_fixed (C : OmegaCategory.{u}) (k : ℕ) {x y z : C.Cell}
    (h : C.target k x = C.source k y) (hx : x = z) (hy : y = z)
    (hz : C.source k z = z) : C.comp k x y h = z := by
  subst x
  subst y
  exact C.comp_fixed k hz h

def Functor.fiber {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (d : D.Objects) : Subcategory C where
  carrier := {x | F.map x = d.val}
  source_mem k x hx := by
    change F.map (C.source k x) = d.val
    rw [F.map_source, hx]
    exact D.source_fixed_upwards (Nat.zero_le k) d.property
  target_mem k x hx := by
    change F.map (C.target k x) = d.val
    rw [F.map_target, hx]
    exact D.target_eq_self_of_source_eq_self (D.source_fixed_upwards (Nat.zero_le k) d.property)
  comp_mem k x y h hx hy := by
    change F.map (C.comp k x y h) = d.val
    rw [F.map_comp k x y h (F.map_composable h)]
    exact D.comp_eq_of_eq_fixed k _ hx hy
      (D.source_fixed_upwards (Nat.zero_le k) d.property)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

@[simp] lemma source_object (C : OmegaCategory.{u}) (k : ℕ) (a : C.Objects) :
    C.source k a.val = a.val := C.source_fixed_upwards (Nat.zero_le k) a.property

@[simp] lemma target_object (C : OmegaCategory.{u}) (k : ℕ) (a : C.Objects) :
    C.target k a.val = a.val := C.target_eq_self_of_source_eq_self (C.source_object k a)

inductive ConeCell (C : OmegaCategory.{u}) : Type u
  | old : C.Cell → ConeCell C
  | edge : C.Objects → ConeCell C
  | top : ConeCell C

namespace ConeCell

variable (C : OmegaCategory.{u})

def source : ℕ → ConeCell C → ConeCell C
  | k, old x => old (C.source k x)
  | 0, edge a => old a.val
  | _+1, edge a => edge a
  | _, top => top

def target : ℕ → ConeCell C → ConeCell C
  | k, old x => old (C.target k x)
  | 0, edge _ => top
  | _+1, edge a => edge a
  | _, top => top

def comp : (k : ℕ) → (x y : ConeCell C) → target C k x = source C k y → ConeCell C
  | _, old x, old y, h => old (C.comp _ x y (old.inj h))
  | 0, old x, edge _, _ => edge (C.sourceObject x)
  | 0, edge a, top, _ => edge a
  | _, top, top, _ => top
  | _+1, edge a, edge _, _ => edge a
  | 0, old _, top, h => by cases h
  | 0, edge _, old _, h => by cases h
  | 0, edge _, edge _, h => by cases h
  | 0, top, old _, h => by cases h
  | 0, top, edge _, h => by cases h
  | _+1, old _, edge _, h => by cases h
  | _+1, old _, top, h => by cases h
  | _+1, edge _, old _, h => by cases h
  | _+1, edge _, top, h => by cases h
  | _+1, top, old _, h => by cases h
  | _+1, top, edge _, h => by cases h

lemma source_source (i j : ℕ) (x : ConeCell C) :
    source C i (source C j x) = source C (min i j) x := by
  cases x with
  | old x => simp [source, C.source_source]
  | edge a => cases i <;> cases j <;> simp [source]
  | top => rfl

lemma target_target (i j : ℕ) (x : ConeCell C) :
    target C i (target C j x) = target C (min i j) x := by
  cases x with
  | old x => simp [target, C.target_target]
  | edge a => cases i <;> cases j <;> simp [target]
  | top => rfl

lemma source_target (i j : ℕ) (x : ConeCell C) :
    source C i (target C j x) = if i < j then source C i x else target C j x := by
  cases x with
  | old x => by_cases h : i < j <;> simp [source, target, C.source_target, h]
  | edge a => cases i <;> cases j <;> simp [source, target]
  | top => simp [source, target]

lemma target_source (i j : ℕ) (x : ConeCell C) :
    target C i (source C j x) = if i < j then target C i x else source C j x := by
  cases x with
  | old x => by_cases h : i < j <;> simp [source, target, C.target_source, h]
  | edge a => cases i <;> cases j <;> simp [source, target]
  | top => simp [source, target]

lemma source_comp_le (i k : ℕ) (hik : i ≤ k) (x y : ConeCell C)
    (h : target C k x = source C k y) : source C i (comp C k x y h) = source C i x := by
  cases k with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    cases x <;> cases y <;> try (cases h)
    all_goals simp_all [source, comp, C.source_comp_le, sourceObject]
  | succ k =>
    cases x <;> cases y <;> try (cases h)
    all_goals simp_all [source, comp, C.source_comp_le i (k+1) hik]

lemma target_comp_le (i k : ℕ) (hik : i ≤ k) (x y : ConeCell C)
    (h : target C k x = source C k y) : target C i (comp C k x y h) = target C i y := by
  cases k with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    cases x <;> cases y <;> try (cases h)
    all_goals simp_all [target, comp, C.target_comp_le]
  | succ k =>
    cases x <;> cases y <;> try (cases h)
    all_goals simp_all [target, comp, C.target_comp_le i (k+1) hik]

lemma source_comp_gt (i k : ℕ) (hki : k < i) (x y : ConeCell C)
    (h : target C k x = source C k y)
    (hs : target C k (source C i x) = source C k (source C i y)) :
    source C i (comp C k x y h) = comp C k (source C i x) (source C i y) hs := by
  cases i with
  | zero => omega
  | succ i =>
    cases k <;> cases x <;> cases y <;> try (cases h)
    all_goals simp_all [source, comp, sourceObject, C.source_source]
    all_goals exact C.source_comp_gt _ _ (by omega) _ _ _ _

lemma target_comp_gt (i k : ℕ) (hki : k < i) (x y : ConeCell C)
    (h : target C k x = source C k y)
    (hs : target C k (target C i x) = source C k (target C i y)) :
    target C i (comp C k x y h) = comp C k (target C i x) (target C i y) hs := by
  cases i with
  | zero => omega
  | succ i =>
    cases k <;> cases x <;> cases y <;> try (cases h)
    all_goals simp_all [target, comp, sourceObject, C.source_target]
    all_goals exact C.target_comp_gt _ _ (by omega) _ _ _ _

end ConeCell
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.ConeCell

variable (C : OmegaCategory.{u})

lemma unit_left (k : ℕ) (x : ConeCell C) (h : target C k (source C k x) = source C k x) :
    comp C k (source C k x) x h = x := by
  cases k <;> cases x <;> simp [source, comp, C.unit_left]

lemma unit_right (k : ℕ) (x : ConeCell C) (h : target C k x = source C k (target C k x)) :
    comp C k x (target C k x) h = x := by
  cases k <;> cases x <;> simp [target, comp, C.unit_right]

lemma assoc (k : ℕ) (x y z : ConeCell C)
    (hxy : target C k x = source C k y) (hyz : target C k y = source C k z)
    (hxy_z : target C k (comp C k x y hxy) = source C k z)
    (hx_yz : target C k x = source C k (comp C k y z hyz)) :
    comp C k (comp C k x y hxy) z hxy_z = comp C k x (comp C k y z hyz) hx_yz := by
  cases k <;> cases x <;> cases y <;> try (cases hxy)
  all_goals cases z <;> try (cases hyz)
  all_goals simp_all [comp, sourceObject, C.source_comp_le]
  all_goals exact C.assoc _ _ _ _ _ _ _ _

lemma interchange (k l : ℕ) (hkl : k < l) (a b c d : ConeCell C)
    (hab : target C l a = source C l b) (hcd : target C l c = source C l d)
    (hac : target C k a = source C k c) (hbd : target C k b = source C k d)
    (hab_cd : target C k (comp C l a b hab) = source C k (comp C l c d hcd))
    (hac_bd : target C l (comp C k a c hac) = source C l (comp C k b d hbd)) :
    comp C k (comp C l a b hab) (comp C l c d hcd) hab_cd =
      comp C l (comp C k a c hac) (comp C k b d hbd) hac_bd := by
  cases l with
  | zero => omega
  | succ l =>
    cases k <;> cases a <;> cases b <;> try (cases hab)
    all_goals cases c <;> cases d <;> try (cases hcd)
    all_goals try (cases hac)
    all_goals try (cases hbd)
    all_goals simp_all [comp, sourceObject, C.source_comp_le]
    all_goals exact C.interchange _ _ (by omega) _ _ _ _ _ _ _ _ _ _

lemma finite_dimension (x : ConeCell C) : ∃ k, source C k x = x := by
  cases x with
  | old x =>
    obtain ⟨k, hk⟩ := C.finite_dimension x
    exact ⟨k, congrArg old hk⟩
  | edge a => exact ⟨1, rfl⟩
  | top => exact ⟨0, rfl⟩

end Thomason.OmegaCategory.ConeCell

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def terminalCone (C : OmegaCategory.{u}) : OmegaCategory.{u} where
  Cell := ConeCell C
  source := ConeCell.source C
  target := ConeCell.target C
  source_source := ConeCell.source_source C
  target_target := ConeCell.target_target C
  source_target := ConeCell.source_target C
  target_source := ConeCell.target_source C
  comp := ConeCell.comp C
  source_comp_le := ConeCell.source_comp_le C
  target_comp_le := ConeCell.target_comp_le C
  source_comp_gt := ConeCell.source_comp_gt C
  target_comp_gt := ConeCell.target_comp_gt C
  unit_left := ConeCell.unit_left C
  unit_right := ConeCell.unit_right C
  assoc := ConeCell.assoc C
  interchange := ConeCell.interchange C
  finite_dimension := ConeCell.finite_dimension C

lemma terminalCone_truncated (C : OmegaCategory.{u}) {n : ℕ} (hn : 1 ≤ n)
    (hC : C.IsTruncated n) : C.terminalCone.IsTruncated n := by
  intro x
  cases n with
  | zero => omega
  | succ n =>
    cases x with
    | old x => exact congrArg ConeCell.old (hC x)
    | edge a => rfl
    | top => rfl

def terminalConeInclusion (C : OmegaCategory.{u}) : Functor C C.terminalCone where
  map := ConeCell.old
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ _ := rfl

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def intervalVertex (i : Fin 2) : interval.{u}.Objects :=
  ⟨⟨⟨i⟩, ⟨i⟩, le_rfl⟩, rfl⟩

def intervalArrow : interval.{u}.Cell := ⟨⟨0⟩, ⟨1⟩, by decide⟩

lemma interval_cases (x : interval.{u}.Cell) :
    x = (intervalVertex 0).val ∨ x = intervalArrow ∨ x = (intervalVertex 1).val := by
  rcases x with ⟨⟨a⟩, ⟨b⟩, h⟩
  fin_cases a <;> fin_cases b
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · simp at h
  · exact Or.inr (Or.inr rfl)

@[simp] lemma interval_source_arrow : interval.source 0 intervalArrow = (intervalVertex 0).val := rfl
@[simp] lemma interval_target_arrow : interval.target 0 intervalArrow = (intervalVertex 1).val := rfl
@[simp] lemma interval_source_succ (k : ℕ) (x : interval.{u}.Cell) : interval.source (k+1) x = x := rfl
@[simp] lemma interval_target_succ (k : ℕ) (x : interval.{u}.Cell) : interval.target (k+1) x = x := rfl

def coneLabel (C : OmegaCategory.{u}) : Functor C.terminalCone interval where
  map
    | ConeCell.old _ => (intervalVertex 0).val
    | ConeCell.edge _ => intervalArrow
    | ConeCell.top => (intervalVertex 1).val
  map_source k x := by cases k <;> cases x <;> rfl
  map_target k x := by cases k <;> cases x <;> rfl
  map_comp k x y h h' := by
    cases k <;> cases x <;> cases y <;> try (cases h)
    all_goals rfl

def coneMap {C : OmegaCategory.{u}} {D : OmegaCategory.{v}} (F : Functor C D) :
    Functor C.terminalCone D.terminalCone where
  map
    | ConeCell.old x => ConeCell.old (F.map x)
    | ConeCell.edge a => ConeCell.edge (F.objects a)
    | ConeCell.top => ConeCell.top
  map_source k x := by
    cases x with
    | old x => exact congrArg ConeCell.old (F.map_source k x)
    | edge a => cases k <;> rfl
    | top => rfl
  map_target k x := by
    cases x with
    | old x => exact congrArg ConeCell.old (F.map_target k x)
    | edge a => cases k <;> rfl
    | top => rfl
  map_comp k x y h h' := by
    cases k <;> cases x <;> cases y <;> try (cases h)
    all_goals simp only [terminalCone, ConeCell.comp, ConeCell.old.injEq, ConeCell.edge.injEq]
    all_goals first
      | rfl
      | exact F.objects_source _
      | exact F.map_comp _ _ _ _ _

def terminalConeFunctor : CategoryTheory.Functor OmegaCategory.{u}
    (CategoryTheory.Over interval.{u}) where
  obj C := CategoryTheory.Over.mk (coneLabel C)
  map F := CategoryTheory.Over.homMk (coneMap F) (by
    apply Functor.ext
    funext x
    cases x <;> rfl)
  map_id C := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply Functor.ext
    funext x
    cases x <;> rfl
  map_comp F G := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply Functor.ext
    funext x
    cases x <;> rfl

def Functor.fiberMap {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    {B : OmegaCategory.{w}} (p : Functor C B) (q : Functor D B)
    (F : Functor C D) (hw : Functor.comp F q = p) (b : B.Objects) :
    Functor (p.fiber b).category (q.fiber b).category :=
  (q.fiber b).lift (Functor.comp (p.fiber b).inclusion F) (fun x => by
    change q.map (F.map x.val) = b.val
    have he := congrArg (fun f : Functor C B => f.map x.val) hw
    exact he.trans x.property)

def fiberFunctor {B : OmegaCategory.{u}} (b : B.Objects) :
    CategoryTheory.Functor (CategoryTheory.Over B) OmegaCategory.{u} where
  obj p := (p.hom.fiber b).category
  map F := Functor.fiberMap _ _ F.left (CategoryTheory.Over.w F) b

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

@[simp] lemma interval_arrow_ne_zero : intervalArrow.{u} ≠ (intervalVertex 0).val := by
  intro h
  have he := congrArg (fun x : interval.{u}.Cell => x.right.down.val) h
  norm_num [intervalArrow, intervalVertex] at he

@[simp] lemma interval_arrow_ne_one : intervalArrow.{u} ≠ (intervalVertex 1).val := by
  intro h
  have he := congrArg (fun x : interval.{u}.Cell => x.left.down.val) h
  norm_num [intervalArrow, intervalVertex] at he

@[simp] lemma interval_zero_ne_one : (intervalVertex 0).val ≠ (intervalVertex 1).val := by
  intro h
  have he := congrArg (fun x : interval.Cell => x.left.down.val) h
  norm_num [intervalVertex] at he

@[simp] lemma interval_zero_ne_arrow : (intervalVertex 0).val ≠ intervalArrow.{u} :=
  Ne.symm interval_arrow_ne_zero
@[simp] lemma interval_one_ne_arrow : (intervalVertex 1).val ≠ intervalArrow.{u} :=
  Ne.symm interval_arrow_ne_one
@[simp] lemma interval_one_ne_zero : (intervalVertex 1).val ≠ (intervalVertex 0).val :=
  Ne.symm interval_zero_ne_one

abbrev zeroFiber {C : OmegaCategory.{u}} (p : Functor C interval.{v}) :=
  (p.fiber (intervalVertex 0)).category

def zeroSourceObject {C : OmegaCategory.{u}} (p : Functor C interval.{v}) (x : C.Cell)
    (h : interval.source 0 (p.map x) = (intervalVertex 0).val) : (zeroFiber p).Objects :=
  ⟨⟨C.source 0 x, (p.map_source 0 x).trans h⟩, Subtype.ext (C.source_source_self 0 x)⟩

lemma zeroSourceObject_source_succ {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (k : ℕ) (x : C.Cell) (h h') :
    zeroSourceObject p (C.source (k+1) x) h = zeroSourceObject p x h' := by
  apply Subtype.ext
  apply Subtype.ext
  exact C.source_source 0 (k+1) x

lemma zeroSourceObject_target_succ {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (k : ℕ) (x : C.Cell) (h h') :
    zeroSourceObject p (C.target (k+1) x) h = zeroSourceObject p x h' := by
  apply Subtype.ext
  apply Subtype.ext
  change C.source 0 (C.target (k+1) x) = C.source 0 x
  simpa using C.source_target 0 (k+1) x

lemma zeroSourceObject_comp {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (k : ℕ) (x y : C.Cell) (h hx hxy) :
    zeroSourceObject p (C.comp k x y h) hxy = zeroSourceObject p x hx := by
  apply Subtype.ext
  apply Subtype.ext
  exact C.source_comp_le 0 k (Nat.zero_le k) x y h

noncomputable def coneExtendMap {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (x : C.Cell) : B.terminalCone.Cell := by
  classical
  exact if h0 : p.map x = (intervalVertex 0).val then ConeCell.old (F.map ⟨x, h0⟩)
    else if ha : p.map x = intervalArrow then
      ConeCell.edge (F.objects (zeroSourceObject p x (by rw [ha]; rfl)))
    else ConeCell.top

lemma coneExtendMap_zero {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (x : C.Cell)
    (hx : p.map x = (intervalVertex 0).val) :
    coneExtendMap p F x = ConeCell.old (F.map ⟨x, hx⟩) := by
  simp [coneExtendMap, hx]
  rfl

lemma coneExtendMap_arrow {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (x : C.Cell)
    (hx : p.map x = intervalArrow) :
    coneExtendMap p F x = ConeCell.edge (F.objects (zeroSourceObject p x (by rw [hx]; rfl))) := by
  simp [coneExtendMap, hx]
  rfl

lemma coneExtendMap_one {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (x : C.Cell)
    (hx : p.map x = (intervalVertex 1).val) : coneExtendMap p F x = ConeCell.top := by
  simp [coneExtendMap, hx]
  rfl

lemma coneExtendMap_source {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (k : ℕ) (x : C.Cell) :
    coneExtendMap p F (C.source k x) = B.terminalCone.source k (coneExtendMap p F x) := by
  rcases interval_cases (p.map x) with hx | hx | hx
  · have hs : p.map (C.source k x) = (intervalVertex 0).val := by
      rw [p.map_source, hx, interval.source_object]
    rw [coneExtendMap_zero p F _ hs, coneExtendMap_zero p F _ hx]
    exact congrArg ConeCell.old (F.map_source k ⟨x, hx⟩)
  · cases k with
    | zero =>
      have hs : p.map (C.source 0 x) = (intervalVertex 0).val := by rw [p.map_source, hx]; rfl
      rw [coneExtendMap_zero p F _ hs, coneExtendMap_arrow p F _ hx]
      rfl
    | succ k =>
      have hs : p.map (C.source (k+1) x) = intervalArrow := by rw [p.map_source, interval_source_succ, hx]
      rw [coneExtendMap_arrow p F _ hs, coneExtendMap_arrow p F _ hx]
      change ConeCell.edge (F.objects _) = ConeCell.edge (F.objects _)
      rw [zeroSourceObject_source_succ]
  · have hs : p.map (C.source k x) = (intervalVertex 1).val := by
      rw [p.map_source, hx, interval.source_object]
    rw [coneExtendMap_one p F _ hs, coneExtendMap_one p F _ hx]
    rfl

lemma coneExtendMap_target {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (k : ℕ) (x : C.Cell) :
    coneExtendMap p F (C.target k x) = B.terminalCone.target k (coneExtendMap p F x) := by
  rcases interval_cases (p.map x) with hx | hx | hx
  · have hs : p.map (C.target k x) = (intervalVertex 0).val := by
      rw [p.map_target, hx, interval.target_object]
    rw [coneExtendMap_zero p F _ hs, coneExtendMap_zero p F _ hx]
    exact congrArg ConeCell.old (F.map_target k ⟨x, hx⟩)
  · cases k with
    | zero =>
      have hs : p.map (C.target 0 x) = (intervalVertex 1).val := by rw [p.map_target, hx]; rfl
      rw [coneExtendMap_one p F _ hs, coneExtendMap_arrow p F _ hx]
      rfl
    | succ k =>
      have hs : p.map (C.target (k+1) x) = intervalArrow := by rw [p.map_target, interval_target_succ, hx]
      rw [coneExtendMap_arrow p F _ hs, coneExtendMap_arrow p F _ hx]
      change ConeCell.edge (F.objects _) = ConeCell.edge (F.objects _)
      rw [zeroSourceObject_target_succ]
  · have hs : p.map (C.target k x) = (intervalVertex 1).val := by
      rw [p.map_target, hx, interval.target_object]
    rw [coneExtendMap_one p F _ hs, coneExtendMap_one p F _ hx]
    rfl

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma interval_map_comp_zero_left {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (x y : C.Cell) (h : C.target 0 x = C.source 0 y) :
    (p.map (C.comp 0 x y h)).left = (p.map x).left := by
  rw [p.map_comp 0 x y h (p.map_composable h)]
  rfl

lemma interval_map_comp_zero_right {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (x y : C.Cell) (h : C.target 0 x = C.source 0 y) :
    (p.map (C.comp 0 x y h)).right = (p.map y).right := by
  rw [p.map_comp 0 x y h (p.map_composable h)]
  rfl

lemma interval_map_comp_succ {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (k : ℕ) (x y : C.Cell) (h : C.target (k+1) x = C.source (k+1) y) :
    p.map (C.comp (k+1) x y h) = p.map x := by
  rw [p.map_comp (k+1) x y h (p.map_composable h)]
  rfl

lemma coneExtendMap_comp {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y)
    (h' : B.terminalCone.target k (coneExtendMap p F x) = B.terminalCone.source k (coneExtendMap p F y)) :
    coneExtendMap p F (C.comp k x y h) =
      B.terminalCone.comp k (coneExtendMap p F x) (coneExtendMap p F y) h' := by
  have hm := p.map_composable h
  cases k with
  | zero =>
    rcases interval_cases (p.map x) with hx | hx | hx
    · rcases interval_cases (p.map y) with hy | hy | hy
      · have hz : p.map (C.comp 0 x y h) = (intervalVertex 0).val := by
          apply ThinCell.ext
          · rw [interval_map_comp_zero_left, hx]
          · rw [interval_map_comp_zero_right, hy]
        simp only [coneExtendMap_zero p F _ hz, coneExtendMap_zero p F _ hx,
          coneExtendMap_zero p F _ hy, terminalCone, ConeCell.comp, ConeCell.old.injEq]
        exact F.map_comp 0 ⟨x, hx⟩ ⟨y, hy⟩ (Subtype.ext h) _
      · have hz : p.map (C.comp 0 x y h) = intervalArrow := by
          apply ThinCell.ext
          · rw [interval_map_comp_zero_left, hx]; rfl
          · rw [interval_map_comp_zero_right, hy]
        simp only [coneExtendMap_arrow p F _ hz, coneExtendMap_zero p F _ hx,
          coneExtendMap_arrow p F _ hy, terminalCone, ConeCell.comp, ConeCell.edge.injEq]
        rw [← F.objects_source ⟨x, hx⟩]
        apply congrArg F.objects
        apply Subtype.ext
        apply Subtype.ext
        exact C.source_comp_le 0 0 le_rfl x y h
      · simp [hx, hy] at hm
    · rcases interval_cases (p.map y) with hy | hy | hy
      · simp [hx, hy] at hm
      · simp [hx, hy] at hm
      · have hz : p.map (C.comp 0 x y h) = intervalArrow := by
          apply ThinCell.ext
          · rw [interval_map_comp_zero_left, hx]
          · rw [interval_map_comp_zero_right, hy]; rfl
        simp only [coneExtendMap_arrow p F _ hz, coneExtendMap_arrow p F _ hx,
          coneExtendMap_one p F _ hy, terminalCone, ConeCell.comp, ConeCell.edge.injEq]
        rw [zeroSourceObject_comp]
    · rcases interval_cases (p.map y) with hy | hy | hy
      · simp [hx, hy] at hm
      · simp [hx, hy] at hm
      · have hz : p.map (C.comp 0 x y h) = (intervalVertex 1).val := by
          apply ThinCell.ext
          · rw [interval_map_comp_zero_left, hx]
          · rw [interval_map_comp_zero_right, hy]
        simp only [coneExtendMap_one p F _ hz, coneExtendMap_one p F _ hx,
          coneExtendMap_one p F _ hy, terminalCone, ConeCell.comp]
  | succ k =>
    have he : p.map x = p.map y := hm
    rcases interval_cases (p.map x) with hx | hx | hx
    · have hy := he.symm.trans hx
      have hz := (interval_map_comp_succ p k x y h).trans hx
      simp only [coneExtendMap_zero p F _ hz, coneExtendMap_zero p F _ hx,
        coneExtendMap_zero p F _ hy, terminalCone, ConeCell.comp, ConeCell.old.injEq]
      exact F.map_comp (k+1) ⟨x, hx⟩ ⟨y, hy⟩ (Subtype.ext h) _
    · have hy := he.symm.trans hx
      have hz := (interval_map_comp_succ p k x y h).trans hx
      simp only [coneExtendMap_arrow p F _ hz, coneExtendMap_arrow p F _ hx,
        coneExtendMap_arrow p F _ hy, terminalCone, ConeCell.comp, ConeCell.edge.injEq]
      rw [zeroSourceObject_comp]
    · have hy := he.symm.trans hx
      have hz := (interval_map_comp_succ p k x y h).trans hx
      simp only [coneExtendMap_one p F _ hz, coneExtendMap_one p F _ hx,
        coneExtendMap_one p F _ hy, terminalCone, ConeCell.comp]

noncomputable def coneExtend {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) : Functor C B.terminalCone where
  map := coneExtendMap p F
  map_source := coneExtendMap_source p F
  map_target := coneExtendMap_target p F
  map_comp := coneExtendMap_comp p F

lemma coneExtend_label {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{v}) (F : Functor (zeroFiber p) B) :
    Functor.comp (coneExtend p F) (coneLabel B) = p := by
  apply Functor.ext
  funext x
  change (coneLabel B).map (coneExtendMap p F x) = p.map x
  rcases interval_cases (p.map x) with hx | hx | hx
  · rw [coneExtendMap_zero p F _ hx, hx]; rfl
  · rw [coneExtendMap_arrow p F _ hx]
    exact hx.symm
  · rw [coneExtendMap_one p F _ hx, hx]; rfl

end Thomason.OmegaCategory

end

end OAI
