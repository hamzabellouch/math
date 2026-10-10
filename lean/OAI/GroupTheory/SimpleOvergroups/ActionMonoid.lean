import Mathlib

namespace OAI

namespace SourceActionMonoid
universe u v
variable (V : Type u) (Z : Type v) [Group V] [MulAction V Z]

inductive Generator
  | grp : V → Generator
  | pre : Z → Generator
  | delete : Z → Generator
  | zero : Generator

abbrev Word := FreeMonoid (Generator V Z)

inductive Relation : Word V Z → Word V Z → Prop
  | group_mul (g h : V) : Relation
      (.of (.grp g) * .of (.grp h)) (.of (.grp (g * h)))
  | group_one : Relation (.of (.grp 1)) 1
  | delete_prefix (z : Z) : Relation (.of (.delete z) * .of (.pre z)) 1
  | delete_prefix_ne (y z : Z) (h : y ≠ z) : Relation
      (.of (.delete y) * .of (.pre z)) (.of .zero)
  | group_prefix (g : V) (z : Z) : Relation
      (.of (.grp g) * .of (.pre z)) (.of (.pre (g • z)))
  | delete_group (z : Z) (g : V) : Relation
      (.of (.delete z) * .of (.grp g)) (.of (.delete (g⁻¹ • z)))
  | zero_left (a : Generator V Z) : Relation (.of .zero * .of a) (.of .zero)
  | zero_right (a : Generator V Z) : Relation (.of a * .of .zero) (.of .zero)

abbrev M := PresentedMonoid (Relation V Z)

variable {V Z}

def of (a : Generator V Z) : M V Z := PresentedMonoid.of (Relation V Z) a

def omega : M V Z := of .zero

def prepend (z : Z) : M V Z := of (.pre z)
def delete (z : Z) : M V Z := of (.delete z)

def groupMap : V →* M V Z where
  toFun g := of (.grp g)
  map_one' := PresentedMonoid.mk_eq_mk_of_rel (Relation.group_one (V := V) (Z := Z))
  map_mul' g h := (PresentedMonoid.mk_eq_mk_of_rel (Relation.group_mul (V := V) (Z := Z) g h)).symm

@[simp] lemma of_grp (g : V) : of (.grp g) = groupMap (Z := Z) g := rfl

@[simp] lemma delete_prefix (z : Z) : delete (V := V) z * prepend z = 1 :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.delete_prefix (V := V) (Z := Z) z)

lemma delete_prefix_ne (y z : Z) (h : y ≠ z) :
    delete (V := V) y * prepend z = omega :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.delete_prefix_ne (V := V) (Z := Z) y z h)

lemma group_prefix (g : V) (z : Z) : groupMap g * prepend z = prepend (V := V) (g • z) :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.group_prefix (V := V) (Z := Z) g z)

lemma delete_group (z : Z) (g : V) : delete (V := V) z * groupMap g = delete (g⁻¹ • z) :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.delete_group (V := V) (Z := Z) z g)

@[simp] lemma omega_of (a : Generator V Z) : omega * of a = omega :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.zero_left (V := V) (Z := Z) a)

@[simp] lemma of_omega (a : Generator V Z) : of a * omega = omega :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.zero_right (V := V) (Z := Z) a)

@[simp] lemma omega_mul (a : M V Z) : omega * a = omega := by
  induction a using PresentedMonoid.inductionOn with | h w =>
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [map_mul, ← mul_assoc]
      exact (congrArg (· * PresentedMonoid.mk (Relation V Z) w) (omega_of a)).trans ih

@[simp] lemma mul_omega (a : M V Z) : a * omega = omega := by
  induction a using PresentedMonoid.inductionOn with | h w =>
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [map_mul, mul_assoc, ih]
      exact of_omega a

def prefixes (l : List Z) : M V Z := (l.map prepend).prod

def deletions (l : List Z) : M V Z := (l.reverse.map delete).prod

@[simp] lemma prefixes_nil : prefixes (V := V) ([] : List Z) = 1 := rfl
@[simp] lemma deletions_nil : deletions (V := V) ([] : List Z) = 1 := rfl
@[simp] lemma prefixes_cons (z : Z) (l : List Z) :
    prefixes (V := V) (z :: l) = prepend z * prefixes l := rfl

lemma deletions_append (l k : List Z) :
    deletions (V := V) (l ++ k) = deletions k * deletions l := by
  simp [deletions]

@[simp] lemma deletions_cons (z : Z) (l : List Z) :
    deletions (V := V) (z :: l) = deletions l * delete z := by
  simp [deletions]

def normal (l : List Z) (g : V) (r : List Z) : M V Z :=
  prefixes l * groupMap g * deletions r

lemma prepend_normal (z : Z) (l : List Z) (g : V) (r : List Z) :
    prepend z * normal l g r = normal (z :: l) g r := by
  simp only [normal, prefixes_cons, mul_assoc]

lemma group_normal_nil (h g : V) (r : List Z) :
    groupMap h * normal [] g r = normal [] (h * g) r := by
  simp [normal, map_mul, mul_assoc]

lemma group_normal_cons (h : V) (z : Z) (l : List Z) (g : V) (r : List Z) :
    groupMap h * normal (z :: l) g r = normal ((h • z) :: l) g r := by
  simp only [normal, prefixes_cons, ← mul_assoc, group_prefix]

lemma delete_normal_nil (z : Z) (g : V) (r : List Z) :
    delete z * normal [] g r = normal [] 1 (r ++ [g⁻¹ • z]) := by
  simp [normal, ← mul_assoc, delete_group, deletions]

lemma delete_normal_cons (z : Z) (l : List Z) (g : V) (r : List Z) :
    delete z * normal (z :: l) g r = normal l g r := by
  simp only [normal, prefixes_cons, ← mul_assoc, delete_prefix, one_mul]

lemma delete_normal_cons_ne (y z : Z) (h : y ≠ z) (l : List Z) (g : V) (r : List Z) :
    delete y * normal (z :: l) g r = omega := by
  simp only [normal, prefixes_cons, ← mul_assoc, delete_prefix_ne y z h, omega_mul]

theorem normal_exists (a : M V Z) :
    a = omega ∨ ∃ (l : List Z) (g : V) (r : List Z), a = normal l g r := by
  classical
  induction a using PresentedMonoid.inductionOn with | h w =>
    induction w using FreeMonoid.inductionOn' with
    | one =>
      right
      exact ⟨[], 1, [], by simp [normal]⟩
    | of_mul c w ih =>
      rw [map_mul]
      rcases ih with h | ⟨l, g, r, h⟩
      · left
        rw [h]
        exact of_omega c
      · rw [h]
        change of c * normal l g r = omega ∨ _
        cases c with
        | zero => exact Or.inl (omega_mul _)
        | pre z => exact Or.inr ⟨z :: l, g, r, prepend_normal z l g r⟩
        | grp q =>
          cases l with
          | nil => exact Or.inr ⟨[], q * g, r, group_normal_nil q g r⟩
          | cons z l => exact Or.inr ⟨q • z :: l, g, r, group_normal_cons q z l g r⟩
        | delete y =>
          cases l with
          | nil => exact Or.inr ⟨[], 1, r ++ [g⁻¹ • y], delete_normal_nil y g r⟩
          | cons z l =>
            by_cases hyz : y = z
            · subst y
              exact Or.inr ⟨l, g, r, delete_normal_cons z l g r⟩
            · exact Or.inl (delete_normal_cons_ne y z hyz l g r)

abbrev State := List Z × V

def headAction (g : V) : State (V := V) (Z := Z) → State (V := V) (Z := Z)
  | ([], v) => ([], g * v)
  | (z :: zs, v) => (g • z :: zs, v)

noncomputable section
local instance : DecidableEq Z := Classical.decEq _

def generatorAction : Generator V Z → Function.End (Option (State (V := V) (Z := Z)))
  | .grp g => Option.map (headAction g)
  | .pre z => Option.map (fun s => (z :: s.1, s.2))
  | .delete z => fun s => match s with
    | none => none
    | some ([], _) => none
    | some (y :: ys, v) => if z = y then some (ys, v) else none
  | .zero => fun _ => none

@[simp] lemma end_mul_apply {A : Type*} (f g : Function.End A) (a : A) :
    (f * g) a = f (g a) := rfl
@[simp] lemma end_one_apply {A : Type*} (a : A) : (1 : Function.End A) a = a := rfl

lemma generatorAction_relations (a b : Word V Z) (h : Relation V Z a b) :
    FreeMonoid.lift generatorAction a = FreeMonoid.lift generatorAction b := by
  cases h with
  | group_mul g h =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    funext s
    simp only [end_mul_apply]
    cases s with
    | none => rfl
    | some p =>
      rcases p with ⟨l, v⟩
      cases l <;> simp [generatorAction, headAction, mul_assoc, mul_smul]
  | group_one =>
    simp only [FreeMonoid.lift_eval_of, map_one]
    funext s
    simp only [end_one_apply]
    cases s with
    | none => rfl
    | some p =>
      rcases p with ⟨l, v⟩
      cases l <;> simp [generatorAction, headAction]
  | delete_prefix z =>
    simp only [map_mul, FreeMonoid.lift_eval_of, map_one]
    funext s
    simp only [end_mul_apply, end_one_apply]
    cases s <;> simp [generatorAction]
  | delete_prefix_ne y z h =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    funext s
    simp only [end_mul_apply]
    cases s <;> simp [generatorAction, h]
  | group_prefix g z =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    funext s
    simp only [end_mul_apply]
    cases s <;> simp [generatorAction, headAction]
  | delete_group z g =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    funext s
    simp only [end_mul_apply]
    cases s with
    | none => rfl
    | some p =>
      rcases p with ⟨l, v⟩
      cases l with
      | nil => rfl
      | cons y ys =>
        have hi : z = g • y ↔ g⁻¹ • z = y := by
          constructor
          · intro h
            rw [h, inv_smul_smul]
          · intro h
            rw [← h, smul_inv_smul]
        simp only [generatorAction, Option.map_some, headAction]
        simp only [hi]
  | zero_left a =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    rfl
  | zero_right a =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    funext s
    simp only [end_mul_apply]
    cases a <;> rfl

def representation : M V Z →* Function.End (Option (State (V := V) (Z := Z))) :=
  PresentedMonoid.lift generatorAction generatorAction_relations

@[simp] lemma representation_of (a : Generator V Z) :
    representation (of a) = generatorAction a := rfl

@[simp] lemma representation_omega (s : Option (State (V := V) (Z := Z))) :
    representation omega s = none := rfl

@[simp] lemma representation_group (g : V) (s : Option (State (V := V) (Z := Z))) :
    representation (groupMap (Z := Z) g) s = s.map (headAction g) := rfl

@[simp] lemma representation_prepend (z : Z) (s : Option (State (V := V) (Z := Z))) :
    representation (prepend (V := V) z) s = s.map (fun p => (z :: p.1, p.2)) := rfl

def strip : List Z → List Z → Option (List Z)
  | [], w => some w
  | _ :: _, [] => none
  | z :: zs, y :: ys => if z = y then strip zs ys else none

@[simp] lemma strip_append (r l : List Z) : strip r (r ++ l) = some l := by
  induction r with
  | nil => rfl
  | cons z r ih => simpa [strip] using ih

lemma strip_eq_some_iff (r k t : List Z) : strip r k = some t ↔ k = r ++ t := by
  induction r generalizing k with
  | nil => simp [strip]
  | cons z r ih =>
    cases k with
    | nil => simp [strip]
    | cons y k =>
      by_cases h : z = y
      · subst y
        simp [strip, ih]
      · simp [strip, h, Ne.symm h]

@[simp] lemma representation_prefixes (l : List Z)
    (s : Option (State (V := V) (Z := Z))) :
    representation (prefixes (V := V) l) s = s.map (fun p => (l ++ p.1, p.2)) := by
  induction l with
  | nil => simp
  | cons z l ih =>
    simp only [prefixes_cons, map_mul, end_mul_apply, ih, representation_prepend,
      Option.map_map]
    rfl

@[simp] lemma representation_delete_none (z : Z) :
    representation (delete (V := V) z) none = none := rfl

@[simp] lemma representation_delete_nil (z : Z) (v : V) :
    representation (delete (V := V) z) (some ([], v)) = none := rfl

@[simp] lemma representation_delete_cons (z y : Z) (k : List Z) (v : V) :
    representation (delete (V := V) z) (some (y :: k, v)) =
      if z = y then some (k, v) else none := rfl

@[simp] lemma representation_deletions_none (r : List Z) :
    representation (deletions (V := V) r) none = none := by
  induction r with
  | nil => rfl
  | cons z r ih =>
    simpa only [deletions_cons, map_mul, end_mul_apply, representation_delete_none] using ih

lemma representation_deletions (r : List Z) (k : List Z) (v : V) :
    representation (deletions (V := V) r) (some (k, v)) =
      (strip r k).map (fun t => (t, v)) := by
  induction r generalizing k with
  | nil => rfl
  | cons z r ih =>
    rw [deletions_cons, map_mul, end_mul_apply]
    cases k with
    | nil => simp [strip]
    | cons y k =>
      by_cases h : z = y
      · subst y
        simpa [strip] using ih k
      · simp [strip, h]

@[simp] lemma strip_self (r : List Z) : strip r r = some [] := by
  simpa only [List.append_nil] using strip_append r []

lemma representation_normal (l : List Z) (g : V) (r k : List Z) (v : V) :
    representation (normal l g r) (some (k, v)) =
      (strip r k).map (fun t =>
        let p := headAction g (t, v)
        (l ++ p.1, p.2)) := by
  simp only [normal, map_mul, end_mul_apply, representation_deletions,
    representation_group, representation_prefixes, Option.map_map]
  rfl

@[simp] lemma representation_normal_at (l : List Z) (g : V) (r : List Z) :
    representation (normal l g r) (some (r, 1)) = some (l, g) := by
  simp only [representation_normal, strip_self, Option.map_some, headAction,
    List.append_nil, mul_one]

lemma normal_ne_zero (l : List Z) (g : V) (r : List Z) : normal l g r ≠ omega := by
  intro h
  have e := congrArg (fun a : M V Z => representation a (some (r, 1))) h
  simp only [representation_normal_at, representation_omega, reduceCtorEq] at e

lemma normal_domain_prefix (l : List Z) (g : V) (r k : List Z) (v : V)
    (h : representation (normal l g r) (some (k, v)) ≠ none) : r <+: k := by
  cases hs : strip r k with
  | none => simp only [representation_normal, hs, Option.map_none, ne_eq, not_true_eq_false] at h
  | some t => exact ⟨t, ((strip_eq_some_iff _ _ _).mp hs).symm⟩

theorem normal_eq_parameters {l l' : List Z} {g g' : V} {r r' : List Z}
    (h : normal l g r = normal l' g' r') : l = l' ∧ g = g' ∧ r = r' := by
  have hr : r <+: r' := normal_domain_prefix l g r r' 1 (by
    rw [h, representation_normal_at]
    exact Option.some_ne_none _)
  have hr' : r' <+: r := normal_domain_prefix l' g' r' r 1 (by
    rw [← h, representation_normal_at]
    exact Option.some_ne_none _)
  have heq : r = r' := hr.eq_of_length (Nat.le_antisymm hr.length_le hr'.length_le)
  subst r'
  have e := congrArg (fun a : M V Z => representation a (some (r, 1))) h
  simp only [representation_normal_at, Option.some.injEq, Prod.mk.injEq] at e
  exact ⟨e.1, e.2, rfl⟩

@[simp] theorem normal_eq_iff {l l' : List Z} {g g' : V} {r r' : List Z} :
    normal l g r = normal l' g' r' ↔ l = l' ∧ g = g' ∧ r = r' := by
  constructor
  · exact normal_eq_parameters
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem unique_normal_form (a : M V Z) (ha : a ≠ omega) :
    ∃! p : List Z × V × List Z, a = normal p.1 p.2.1 p.2.2 := by
  obtain h | ⟨l, g, r, h⟩ := normal_exists a
  · exact (ha h).elim
  · refine ⟨(l, g, r), h, ?_⟩
    rintro ⟨l', g', r'⟩ h'
    obtain ⟨rfl, rfl, rfl⟩ := normal_eq_parameters (h'.symm.trans h)
    rfl

theorem groupMap_injective : Function.Injective (groupMap (V := V) (Z := Z)) := by
  intro g h heq
  have he : normal ([] : List Z) g [] = normal [] h [] := by
    simpa only [normal, prefixes_nil, deletions_nil, one_mul, mul_one] using heq
  exact (normal_eq_parameters he).2.1

def groupUnits : V →* (M V Z)ˣ := (groupMap (V := V) (Z := Z)).toHomUnits

@[simp] lemma groupUnits_val (g : V) :
    (groupUnits (Z := Z) g).val = groupMap (Z := Z) g := rfl

theorem groupUnits_injective : Function.Injective (groupUnits (V := V) (Z := Z)) := by
  intro g h heq
  exact groupMap_injective (congrArg Units.val heq)

end

namespace Algorithm
variable [DecidableEq Z]

abbrev Form := Option (List Z × V × List Z)

def eval : Form (V := V) (Z := Z) → M V Z
  | none => omega
  | some (l, g, r) => normal l g r

def step : Generator V Z → Form (V := V) (Z := Z) → Form (V := V) (Z := Z)
  | _, none => none
  | .zero, _ => none
  | .pre z, some (l, g, r) => some (z :: l, g, r)
  | .grp h, some ([], g, r) => some ([], h * g, r)
  | .grp h, some (z :: l, g, r) => some (h • z :: l, g, r)
  | .delete y, some ([], g, r) => some ([], 1, r ++ [g⁻¹ • y])
  | .delete y, some (z :: l, g, r) => if y = z then some (l, g, r) else none

lemma eval_step (c : Generator V Z) (f : Form (V := V) (Z := Z)) :
    eval (step c f) = of c * eval f := by
  cases f with
  | none => exact (of_omega c).symm
  | some p =>
    rcases p with ⟨l, g, r⟩
    cases c with
    | zero => exact (omega_mul _).symm
    | pre z => exact (prepend_normal z l g r).symm
    | grp h =>
      cases l with
      | nil => exact (group_normal_nil h g r).symm
      | cons z l => exact (group_normal_cons h z l g r).symm
    | delete y =>
      cases l with
      | nil => exact (delete_normal_nil y g r).symm
      | cons z l =>
        by_cases h : y = z
        · subst y
          change eval (if z = z then some (l, g, r) else none) =
            delete z * normal (z :: l) g r
          rw [ite_eq_left rfl]
          exact (delete_normal_cons z l g r).symm
        · change eval (if y = z then some (l, g, r) else none) =
            delete y * normal (z :: l) g r
          rw [ite_eq_right h]
          exact (delete_normal_cons_ne y z h l g r).symm

def normalize : List (Generator V Z) → Form (V := V) (Z := Z)
  | [] => some ([], 1, [])
  | c :: w => step c (normalize w)

theorem normalize_correct (w : List (Generator V Z)) :
    eval (normalize w) = PresentedMonoid.mk (Relation V Z) (FreeMonoid.ofList w) := by
  induction w with
  | nil => simp [normalize, eval, normal]
  | cons c w ih =>
    simp only [normalize, eval_step, ih, FreeMonoid.ofList_cons, map_mul]
    rfl

omit [DecidableEq Z] in
lemma eval_injective : Function.Injective (eval (V := V) (Z := Z)) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some p => exact (normal_ne_zero p.1 p.2.1 p.2.2 hab.symm).elim
  | some p =>
    rcases p with ⟨l, g, r⟩
    cases b with
    | none => exact (normal_ne_zero l g r hab).elim
    | some p =>
      rcases p with ⟨l', g', r'⟩
      obtain ⟨rfl, rfl, rfl⟩ := normal_eq_parameters hab
      rfl

theorem word_eq_iff (a b : List (Generator V Z)) :
    PresentedMonoid.mk (Relation V Z) (FreeMonoid.ofList a) =
        PresentedMonoid.mk (Relation V Z) (FreeMonoid.ofList b) ↔ normalize a = normalize b := by
  rw [← normalize_correct, ← normalize_correct]
  exact eval_injective.eq_iff

def equalWords [DecidableEq V] (a b : List (Generator V Z)) : Bool :=
  decide (normalize a = normalize b)

theorem equalWords_correct [DecidableEq V] (a b : List (Generator V Z)) :
    equalWords a b = true ↔
      PresentedMonoid.mk (Relation V Z) (FreeMonoid.ofList a) =
        PresentedMonoid.mk (Relation V Z) (FreeMonoid.ofList b) := by
  simp only [equalWords, decide_eq_true_eq, ← word_eq_iff]

end Algorithm
end SourceActionMonoid

end OAI
